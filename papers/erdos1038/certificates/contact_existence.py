#!/usr/bin/env python3
"""Rigorous Arb certificate for the parameter triple used in Appendix A.

This program matches the scalar existence proof in the manuscript.  It
certifies, on the interval

    I_* = [q_0-10^(-31), q_0+10^(-31)],

that 0 < p(q) < q < 1, that the two contact equations have unique roots
u(q) and v(q) inside the radius-10^(-30) face intervals, and that

    kappa(q_-) > 0,    kappa(q_+) < 0.

The intermediate value theorem then gives at least one zero of
(F_R,F_L,K) in the manuscript's box B_*.  The script also returns rigorous
Arb enclosures for p_*, alpha, r_*, z_*, and D.  Those same enclosures are
imported by erdos1038_exact_endpoint_certificate.py, so there is no
unchecked decimal handoff between the two interval certificates.

All pass/fail decisions use outward-rounded python-flint Arb arithmetic.
"""

from __future__ import annotations

import os
from decimal import Decimal
from fractions import Fraction

from flint import arb, ctx

BITS = int(os.environ.get("ERDOS1038_ARB_BITS", "384"))
ctx.prec = BITS

Q0 = Fraction(Decimal("0.94985834582347031848349802544031979"))
U0 = Fraction(Decimal("0.89396612207545611611103128550805002"))
V0 = Fraction(Decimal("0.96455509699582140639698562612728156"))
Q_RADIUS = Fraction(1, 10**31)
UV_RADIUS = Fraction(1, 10**30)
BISECTION_STEPS = int(os.environ.get("ERDOS1038_CONTACT_BISECTIONS", "80"))


def exact(value: Fraction | int) -> arb:
    """Convert an integer or rational to an exact Arb point ball."""
    if isinstance(value, int):
        return arb(value)
    return arb(value.numerator) / value.denominator


def interval(lo: Fraction, hi: Fraction) -> arb:
    """Return an Arb interval containing the two rational endpoints."""
    return exact(lo).union(exact(hi))


def Lambda(y):
    return ((1 + y) / (1 - y)).log()


def pfun(q):
    return (2 / (1 - q * q)).log() / Lambda(q)


def X(q, y):
    return (2 * q * q - 1 - y * y) / (1 - y * y)


def Xprime(q, y):
    return -4 * y * (1 - q * q) / (1 - y * y) ** 2


def F_R(q, u):
    p = pfun(q)
    return Lambda(u) - p * ((q + u) / (q - u)).log()


def F_L(q, v):
    p = pfun(q)
    return Lambda(v) - p * ((q + v) / (v - q)).log()


def C_contact(q, u, v):
    p = pfun(q)
    r = X(q, u)
    z = X(q, v)
    return (
        r * u * Lambda(u)
        - z * v * Lambda(v)
        - (r - z) * p * Lambda(q)
    ) / (v * Lambda(v) - u * Lambda(u))


def K_contact(q, u, v):
    p = pfun(q)
    r = X(q, u)
    z = X(q, v)
    C = C_contact(q, u, v)
    F_R_u = 2 / (1 - u * u) - 2 * p * q / (q * q - u * u)
    F_L_v = 2 / (1 - v * v) + 2 * p * q / (v * v - q * q)
    return (
        v * (z + C) * F_L_v / Xprime(q, v)
        - u * (r + C) * F_R_u / Xprime(q, u)
    )


def parameter_box() -> tuple[arb, arb, arb]:
    """The manuscript's certified q,u,v enclosure containing every chosen root."""
    q = interval(Q0 - Q_RADIUS, Q0 + Q_RADIUS)
    u = interval(U0 - UV_RADIUS, U0 + UV_RADIUS)
    v = interval(V0 - UV_RADIUS, V0 + UV_RADIUS)
    return q, u, v


def certified_parameter_enclosures() -> dict[str, arb]:
    """Rigorous enclosures used by all other numerical certificates."""
    q, u, v = parameter_box()
    p = pfun(q)
    alpha = 2 * q * q - 1
    r = X(q, u)
    z = X(q, v)
    D = r - z
    return {
        "q": q,
        "u": u,
        "v": v,
        "p": p,
        "alpha": alpha,
        "r": r,
        "z": z,
        "D": D,
    }


def _bisect_root(
    q: arb,
    lo: Fraction,
    hi: Fraction,
    function,
    *,
    increasing: bool,
) -> arb:
    """Enclose the unique root using certified signs at rational midpoints."""
    for _ in range(BISECTION_STEPS):
        mid = (lo + hi) / 2
        value = function(q, exact(mid))

        if value.lower() > 0:
            if increasing:
                hi = mid
            else:
                lo = mid
        elif value.upper() < 0:
            if increasing:
                lo = mid
            else:
                hi = mid
        else:
            raise AssertionError(
                "Root bisection encountered an unresolved midpoint sign; "
                "increase ERDOS1038_ARB_BITS"
            )

    return interval(lo, hi)


def certify_contact_existence() -> dict[str, arb]:
    """Run the interval proof corresponding to Lemma A.1 of the manuscript."""
    q_minus = Q0 - Q_RADIUS
    q_plus = Q0 + Q_RADIUS
    q_interval = interval(q_minus, q_plus)

    p_interval = pfun(q_interval)
    if not (
        p_interval.lower() > 0
        and p_interval.upper() < q_interval.lower()
        and q_interval.upper() < 1
    ):
        raise AssertionError(f"Could not certify 0<p(q)<q<1: p={p_interval}, q={q_interval}")
    print("PASS: 0 < p(q) < q < 1 on I_*")

    u_lo, u_hi = U0 - UV_RADIUS, U0 + UV_RADIUS
    v_lo, v_hi = V0 - UV_RADIUS, V0 + UV_RADIUS

    FR_lo = F_R(q_interval, exact(u_lo))
    FR_hi = F_R(q_interval, exact(u_hi))
    FL_lo = F_L(q_interval, exact(v_lo))
    FL_hi = F_L(q_interval, exact(v_hi))

    if not (FR_lo.lower() > 0 and FR_hi.upper() < 0):
        raise AssertionError(f"F_R face signs failed: lower={FR_lo}, upper={FR_hi}")
    if not (FL_lo.upper() < 0 and FL_hi.lower() > 0):
        raise AssertionError(f"F_L face signs failed: lower={FL_lo}, upper={FL_hi}")
    print("PASS: uniform F_R and F_L face signs")

    q_minus_arb = exact(q_minus)
    q_plus_arb = exact(q_plus)

    u_minus = _bisect_root(q_minus_arb, u_lo, u_hi, F_R, increasing=False)
    v_minus = _bisect_root(q_minus_arb, v_lo, v_hi, F_L, increasing=True)
    u_plus = _bisect_root(q_plus_arb, u_lo, u_hi, F_R, increasing=False)
    v_plus = _bisect_root(q_plus_arb, v_lo, v_hi, F_L, increasing=True)

    kappa_minus = K_contact(q_minus_arb, u_minus, v_minus)
    kappa_plus = K_contact(q_plus_arb, u_plus, v_plus)
    if not (kappa_minus.lower() > 0):
        raise AssertionError(f"kappa(q_-) is not positive: {kappa_minus}")
    if not (kappa_plus.upper() < 0):
        raise AssertionError(f"kappa(q_+) is not negative: {kappa_plus}")
    print(f"PASS: kappa(q_-) > 0: {kappa_minus}")
    print(f"PASS: kappa(q_+) < 0: {kappa_plus}")

    values = certified_parameter_enclosures()
    q, u, v = values["q"], values["u"], values["v"]
    p, alpha, r, z, D = (
        values["p"],
        values["alpha"],
        values["r"],
        values["z"],
        values["D"],
    )

    facts = [
        ("D < 1.836", D.upper() < arb("1.836")),
        ("D < alpha+sqrt(2)", D.upper() < (alpha + arb(2).sqrt()).lower()),
        ("0 < D-1.708", (D - arb("1.708")).lower() > 0),
        ("D-1.708 < 0.127", (D - arb("1.708")).upper() < arb("0.127")),
        ("D-1.708 < alpha", (D - arb("1.708")).upper() < alpha.lower()),
        (
            "D-1.708 < 2(1-alpha)",
            (D - arb("1.708")).upper() < (2 * (1 - alpha)).lower(),
        ),
        (
            "2alpha-1-(D-1.708)>0",
            (2 * alpha - 1 - (D - arb("1.708"))).lower() > 0,
        ),
        (
            "kernel lower ratio > 12/25",
            (1 / (2 + (D - arb("1.708")) / 2)).lower() > arb(12) / 25,
        ),
        (
            "kernel upper ratio < 1/2",
            ((D - 1) / (1 + alpha)).upper() < arb(1) / 2,
        ),
        (
            "0 < p < q < 1",
            p.lower() > 0 and p.upper() < q.lower() and q.upper() < 1,
        ),
        (
            "0 < u < q < v < 1",
            u.lower() > 0
            and u.upper() < q.lower()
            and q.upper() < v.lower()
            and v.upper() < 1,
        ),
    ]

    for name, ok in facts:
        if not ok:
            raise AssertionError(f"Numerical fact failed: {name}")
        print(f"PASS: {name}")

    print("ENCLOSURES:")
    for name in ("q", "u", "v", "p", "alpha", "r", "z", "D"):
        print(f"  {name} = {values[name]}")
    print("PASS: parameter-triple existence and all numerical facts")
    return values


def main() -> None:
    print(f"Arb precision: {BITS} bits; bisection steps: {BISECTION_STEPS}")
    certify_contact_existence()


if __name__ == "__main__":
    main()
