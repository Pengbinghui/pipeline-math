#!/usr/bin/env python3
"""Arb/Krawczyk isolation of the contact triple and numerical facts.

Uses outward-rounded python-flint Arb arithmetic.  The only non-interval
objects used in the Krawczyk preconditioner are exact rational numbers.
"""
from __future__ import annotations

import os
from fractions import Fraction
from decimal import Decimal

import sympy as sp
from flint import arb, arb_series, ctx

BITS = int(os.environ.get("ERDOS1038_ARB_BITS", "384"))
ctx.prec = BITS

Q0 = "0.94985834582347031848349802544031979"
U0 = "0.89396612207545611611103128550805002"
V0 = "0.96455509699582140639698562612728156"
RAD = "1e-30"


def log(x):
    return x.log()


def Lambda(y):
    return log((1 + y) / (1 - y))


def pfun(q):
    return log(2 / (1 - q * q)) / Lambda(q)


def X(q, y):
    return (2 * q * q - 1 - y * y) / (1 - y * y)


def Xprime(q, y):
    return -4 * y * (1 - q * q) / (1 - y * y) ** 2


def values(q, u, v):
    p = pfun(q)
    r = X(q, u)
    z = X(q, v)
    FR = Lambda(u) - p * log((q + u) / (q - u))
    FL = Lambda(v) - p * log((q + v) / (v - q))
    C = (r * u * Lambda(u) - z * v * Lambda(v) - (r - z) * p * Lambda(q)) / (
        v * Lambda(v) - u * Lambda(u)
    )
    FRu = 2 / (1 - u * u) - 2 * p * q / (q * q - u * u)
    FLv = 2 / (1 - v * v) + 2 * p * q / (v * v - q * q)
    K = v * (z + C) * FLv / Xprime(q, v) - u * (r + C) * FRu / Xprime(q, u)
    return (FR, FL, K)


def interval(mid: str, rad: str = RAD) -> arb:
    return arb(mid, rad)


def exact_fraction_from_decimal(s: str) -> Fraction:
    return Fraction(Decimal(s))


def arb_from_fraction(x: Fraction) -> arb:
    return arb(x.numerator) / arb(x.denominator)


def sympy_inverse_preconditioner():
    q, u, v = sp.symbols("q u v")
    Lam = lambda x: sp.log((1 + x) / (1 - x))
    p = sp.log(2 / (1 - q**2)) / Lam(q)
    Xs = lambda yy: (2 * q**2 - 1 - yy**2) / (1 - yy**2)
    r, z = Xs(u), Xs(v)
    FR = Lam(u) - p * sp.log((q + u) / (q - u))
    FL = Lam(v) - p * sp.log((q + v) / (v - q))
    C = (r * u * Lam(u) - z * v * Lam(v) - (r - z) * p * Lam(q)) / (v * Lam(v) - u * Lam(u))
    Xp = lambda yy: -4 * yy * (1 - q**2) / (1 - yy**2) ** 2
    FRu = 2 / (1 - u**2) - 2 * p * q / (q**2 - u**2)
    FLv = 2 / (1 - v**2) + 2 * p * q / (v**2 - q**2)
    K = v * (z + C) * FLv / Xp(v) - u * (r + C) * FRu / Xp(u)
    F = sp.Matrix([FR, FL, K])
    J = F.jacobian([q, u, v])
    subs = {q: sp.Rational(Q0), u: sp.Rational(U0), v: sp.Rational(V0)}
    Jn = J.evalf(100, subs=subs)
    Yn = Jn.inv().evalf(90)
    # Exact decimal rationals with 75 significant digits are more than sufficient.
    Y = []
    for i in range(3):
        row = []
        for j in range(3):
            text = sp.N(Yn[i, j], 75).__str__()
            row.append(exact_fraction_from_decimal(text))
        Y.append(row)
    return Y


def mat_vec(A, x):
    return [sum((arb_from_fraction(A[i][j]) * x[j] for j in range(3)), arb(0)) for i in range(3)]


def mat_mul_interval(A, B):
    # A exact rational 3x3, B arb 3x3
    return [[sum((arb_from_fraction(A[i][k]) * B[k][j] for k in range(3)), arb(0)) for j in range(3)] for i in range(3)]


def jacobian_box(box):
    old_cap = ctx.cap
    ctx.cap = 2
    try:
        J = [[None] * 3 for _ in range(3)]
        for j in range(3):
            args = []
            for k in range(3):
                args.append(arb_series([box[k], arb(1)]) if j == k else box[k])
            out = values(*args)
            for i in range(3):
                if isinstance(out[i], arb_series):
                    coeffs = out[i].coeffs()
                    J[i][j] = coeffs[1] if len(coeffs) > 1 else arb(0)
                else:
                    J[i][j] = arb(0)
        return J
    finally:
        ctx.cap = old_cap


def strict_inside(x: arb, radius: arb) -> bool:
    return x.lower() > -radius and x.upper() < radius


def main() -> None:
    center = [arb(Q0), arb(U0), arb(V0)]
    box = [interval(Q0), interval(U0), interval(V0)]
    radius = arb(RAD)
    F0 = list(values(*center))
    Jbox = jacobian_box(box)
    Y = sympy_inverse_preconditioner()

    # Check exact preconditioner is invertible.
    Ys = sp.Matrix([[sp.Rational(y.numerator, y.denominator) for y in row] for row in Y])
    assert Ys.det() != 0
    print("PASS: rational Krawczyk preconditioner is invertible")

    YF = mat_vec(Y, F0)
    YJ = mat_mul_interval(Y, Jbox)
    M = [[(arb(1) if i == j else arb(0)) - YJ[i][j] for j in range(3)] for i in range(3)]
    delta = [arb(0, RAD) for _ in range(3)]
    Kdelta = []
    for i in range(3):
        val = -YF[i]
        for j in range(3):
            val += M[i][j] * delta[j]
        Kdelta.append(val)
        if not strict_inside(val, radius):
            raise AssertionError(f"Krawczyk inclusion failed in coordinate {i}: {val}")
    print("PASS: Krawczyk image is strictly inside the radius-1e-30 box")

    # The root lies in the Krawczyk image; evaluate constants on this enclosure.
    root_box = [center[i] + Kdelta[i] for i in range(3)]
    q, u, v = root_box
    p = pfun(q)
    alpha = 2 * q * q - 1
    r = X(q, u)
    z = X(q, v)
    D = r - z

    facts = [
        ("D < 1.836", D.upper() < arb("1.836")),
        ("D < alpha+sqrt(2)", D.upper() < (alpha + arb(2).sqrt()).lower()),
        ("0 < D-1.708", (D - arb("1.708")).lower() > 0),
        ("D-1.708 < 0.127", (D - arb("1.708")).upper() < arb("0.127")),
        ("D-1.708 < alpha", (D - arb("1.708")).upper() < alpha.lower()),
        ("D-1.708 < 2(1-alpha)", (D - arb("1.708")).upper() < (2 * (1 - alpha)).lower()),
        ("2alpha-1-(D-1.708)>0", (2 * alpha - 1 - (D - arb("1.708"))).lower() > 0),
        ("kernel lower ratio > 12/25", (1 / (2 + (D - arb("1.708")) / 2)).lower() > arb(12) / 25),
        ("kernel upper ratio < 1/2", ((D - 1) / (1 + alpha)).upper() < arb(1) / 2),
        ("0 < p < q < 1", p.lower() > 0 and p.upper() < q.lower() and q.upper() < 1),
        ("0 < u < q < v < 1", u.lower() > 0 and u.upper() < q.lower() and q.upper() < v.lower() and v.upper() < 1),
    ]
    for name, ok in facts:
        if not ok:
            raise AssertionError(f"Numerical fact failed: {name}")
        print(f"PASS: {name}")

    print("ENCLOSURES:")
    for name, val in [("q", q), ("u", u), ("v", v), ("p", p), ("alpha", alpha), ("r", r), ("z", z), ("D", D)]:
        print(f"  {name} = {val}")
    print("PASS: contact isolation and all numerical facts")


if __name__ == "__main__":
    main()
