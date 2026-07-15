#!/usr/bin/env python3
"""Rigorous Arb certificate for the endpoint inequalities in Lemma 5.1.

The program evaluates the explicit endpoint formulas with second-order
automatic-differentiation jets.  It proves the inequalities on rational boxes
using interval Taylor bounds and adaptive subdivision.  The only infinite
series is Phi(y)=sum y^n/(2n+1); value and first two derivative tails are added
as rigorous symmetric Arb errors.

All pass/fail decisions use outward-rounded python-flint Arb arithmetic.
"""
from __future__ import annotations

import argparse
import os
from dataclasses import dataclass
from fractions import Fraction
from collections import deque

from flint import arb, ctx

BITS = int(os.environ.get("ERDOS1038_ARB_BITS", "384"))
ctx.prec = BITS
SERIES_TERMS = int(os.environ.get("ERDOS1038_PHI_TERMS", "40"))
MAX_DEPTH = int(os.environ.get("ERDOS1038_ENDPOINT_MAX_DEPTH", "22"))

# These balls are deliberately much wider than the Krawczyk enclosure.
ALPHA = arb("0.804461754260998666841640107869", "1e-26")
D = arb("1.834430475762661711090753635125", "1e-26")
BOUND = Fraction(127, 1000)


def exact(q: Fraction | int) -> arb:
    if isinstance(q, int):
        return arb(q)
    return arb(q.numerator) / q.denominator


def interval(lo: Fraction, hi: Fraction) -> arb:
    return exact(lo).union(exact(hi))


def symmetric(radius: arb) -> arb:
    return (-radius).union(radius)


def abs_upper(x: arb) -> arb:
    return arb(abs(x).upper())


@dataclass
class Jet2:
    v: arb
    g: tuple[arb, arb]
    H: tuple[tuple[arb, arb], tuple[arb, arb]]

    @staticmethod
    def const(x) -> "Jet2":
        value = x if isinstance(x, arb) else arb(x)
        z = arb(0)
        return Jet2(value, (z, z), ((z, z), (z, z)))

    @staticmethod
    def variable(value: arb, index: int) -> "Jet2":
        z, o = arb(0), arb(1)
        g = (o, z) if index == 0 else (z, o)
        return Jet2(value, g, ((z, z), (z, z)))

    @staticmethod
    def coerce(x) -> "Jet2":
        return x if isinstance(x, Jet2) else Jet2.const(x)

    def __add__(self, other):
        o = Jet2.coerce(other)
        return Jet2(
            self.v + o.v,
            tuple(self.g[i] + o.g[i] for i in range(2)),
            tuple(tuple(self.H[i][j] + o.H[i][j] for j in range(2)) for i in range(2)),
        )

    __radd__ = __add__

    def __neg__(self):
        return Jet2(-self.v, tuple(-x for x in self.g), tuple(tuple(-x for x in row) for row in self.H))

    def __sub__(self, other):
        return self + (-Jet2.coerce(other))

    def __rsub__(self, other):
        return Jet2.coerce(other) - self

    def __mul__(self, other):
        o = Jet2.coerce(other)
        g = tuple(self.g[i] * o.v + self.v * o.g[i] for i in range(2))
        H = []
        for i in range(2):
            row = []
            for j in range(2):
                row.append(
                    self.H[i][j] * o.v
                    + self.g[i] * o.g[j]
                    + self.g[j] * o.g[i]
                    + self.v * o.H[i][j]
                )
            H.append(tuple(row))
        return Jet2(self.v * o.v, g, tuple(H))

    __rmul__ = __mul__

    def unary(self, f0: arb, f1: arb, f2: arb) -> "Jet2":
        g = tuple(f1 * self.g[i] for i in range(2))
        H = []
        for i in range(2):
            row = []
            for j in range(2):
                row.append(f2 * self.g[i] * self.g[j] + f1 * self.H[i][j])
            H.append(tuple(row))
        return Jet2(f0, g, tuple(H))

    def inv(self):
        f0 = 1 / self.v
        f1 = -1 / (self.v * self.v)
        f2 = 2 / (self.v * self.v * self.v)
        return self.unary(f0, f1, f2)

    def __truediv__(self, other):
        return self * Jet2.coerce(other).inv()

    def __rtruediv__(self, other):
        return Jet2.coerce(other) / self

    def sqrt(self):
        root = self.v.sqrt()
        return self.unary(root, 1 / (2 * root), -1 / (4 * root * root * root))

    def log(self):
        return self.unary(self.v.log(), 1 / self.v, -1 / (self.v * self.v))


def phi_series(y: Jet2) -> Jet2:
    """Rigorous Phi(y), Phi'(y), Phi''(y) on 0 <= y < 1."""
    q = arb(abs(y.v).upper())
    if not (q.upper() < 1):
        raise ValueError("Phi interval reaches |y| >= 1")

    value = arb(0)
    derivative = arb(0)
    second = arb(0)
    power = arb(1)
    for n in range(SERIES_TERMS):
        value += power / (2 * n + 1)
        if n >= 1:
            derivative += n * (y.v ** (n - 1)) / (2 * n + 1)
        if n >= 2:
            second += n * (n - 1) * (y.v ** (n - 2)) / (2 * n + 1)
        power *= y.v

    N = SERIES_TERMS
    one = arb(1)
    value_tail = q**N / ((2 * N + 1) * (one - q))
    derivative_tail = q ** (N - 1) / (2 * (one - q))
    second_tail = arb(1) / 2 * (
        (N - 1) * q ** (N - 2) / (one - q)
        + q ** (N - 1) / (one - q) ** 2
    )
    f0 = value + symmetric(value_tail)
    f1 = derivative + symmetric(derivative_tail)
    f2 = second + symmetric(second_tail)
    return y.unary(f0, f1, f2)


def phi_below(x, a, b):
    x, a, b = Jet2.coerce(x), Jet2.coerce(a), Jet2.coerce(b)
    midpoint = (a + b) / 2
    root = ((a - x) * (b - x)).sqrt()
    return x - midpoint - root, x - midpoint + root, -root


def left_contact_coefficients(r: Jet2, h: Jet2):
    z = r - D + h
    beta = 1 + h / 2
    a = ALPHA + h
    b = beta

    w, _, _ = phi_below(-1, a, b)
    phi_z, psi_z, S_z = phi_below(z, a, b)
    phi_r, psi_r, S_r = phi_below(r, a, b)

    log_z = ((w - phi_z) / (psi_z - w)).log()
    log_r = ((phi_r - w) / (psi_r - w)).log()
    J_z = log_z / S_z
    J_r = log_r / S_r

    delta = D - h
    f_z = -(z - ALPHA) / delta
    f_r = (r - ALPHA) / delta

    l0 = -(-w / 2).log() - z * f_z * J_z - r * f_r * J_r
    l1 = -(f_z * J_z + f_r * J_r)
    return l0, l1


def right_contact_coefficients(r: Jet2, h: Jet2):
    z = r - D + h
    beta = 1 + h / 2
    a = Jet2.const(ALPHA)
    b = 1 - h / 2
    half_length = (b - a) / 2
    w = -half_length

    phi_z, psi_z, S_z = phi_below(z, a, b)
    phi_r, psi_r, S_r = phi_below(r, a, b)
    log_z = ((w - phi_z) / (psi_z - w)).log()
    log_r = ((w - phi_r) / (psi_r - w)).log()

    y = h / (beta - a)
    terminal = 2 * h * phi_series(y)

    terms = (S_z * log_z, S_r * log_r, terminal)
    poles = (z, r, beta)
    denoms = ((z - r) * (z - beta), (r - z) * (r - beta), (beta - z) * (beta - r))

    q0 = -(half_length / 2).log()
    q1 = Jet2.const(0)
    for pole, denom, term in zip(poles, denoms, terms):
        q0 -= pole / denom * term
        q1 -= term / denom
    return q0, q1


def quantities(r: Jet2, h: Jet2):
    l0, l1 = left_contact_coefficients(r, h)
    q0, q1 = right_contact_coefficients(r, h)
    C0 = -q0 / q1
    Q = l0 + l1 * C0
    L1 = l0 + l1
    z = r + h - D
    return Q, q1, -z - C0, L1


@dataclass(frozen=True)
class Box:
    r0: Fraction
    r1: Fraction
    h0: Fraction
    h1: Fraction
    depth: int = 0

    def midpoint(self):
        return ((self.r0 + self.r1) / 2, (self.h0 + self.h1) / 2)

    def radii(self):
        return ((self.r1 - self.r0) / 2, (self.h1 - self.h0) / 2)

    def split(self):
        rw = self.r1 - self.r0
        hw = self.h1 - self.h0
        if rw >= hw:
            m = (self.r0 + self.r1) / 2
            return Box(self.r0, m, self.h0, self.h1, self.depth + 1), Box(m, self.r1, self.h0, self.h1, self.depth + 1)
        m = (self.h0 + self.h1) / 2
        return Box(self.r0, self.r1, self.h0, m, self.depth + 1), Box(self.r0, self.r1, m, self.h1, self.depth + 1)


def center_and_interval(box: Box):
    rm, hm = box.midpoint()
    rr, hr = box.radii()
    rc = Jet2.variable(exact(rm), 0)
    hc = Jet2.variable(exact(hm), 1)
    ri = Jet2.variable(interval(box.r0, box.r1), 0)
    hi = Jet2.variable(interval(box.h0, box.h1), 1)
    return quantities(rc, hc), quantities(ri, hi), (exact(rr), exact(hr))


def lower_value(center: Jet2, enclosure: Jet2, radii):
    return center.v - abs_upper(enclosure.g[0]) * radii[0] - abs_upper(enclosure.g[1]) * radii[1]


def upper_value(center: Jet2, enclosure: Jet2, radii):
    return center.v + abs_upper(enclosure.g[0]) * radii[0] + abs_upper(enclosure.g[1]) * radii[1]


def lower_derivative(center: Jet2, enclosure: Jet2, component: int, radii):
    return center.g[component] - abs_upper(enclosure.H[component][0]) * radii[0] - abs_upper(enclosure.H[component][1]) * radii[1]


def upper_derivative(center: Jet2, enclosure: Jet2, component: int, radii):
    return center.g[component] + abs_upper(enclosure.H[component][0]) * radii[0] + abs_upper(enclosure.H[component][1]) * radii[1]


def lower_direction(center: Jet2, enclosure: Jet2, coeffs, radii):
    c0, c1 = coeffs
    cv = c0 * center.g[0] + c1 * center.g[1]
    row0 = c0 * enclosure.H[0][0] + c1 * enclosure.H[1][0]
    row1 = c0 * enclosure.H[0][1] + c1 * enclosure.H[1][1]
    return cv - abs_upper(row0) * radii[0] - abs_upper(row1) * radii[1]


def certify_square():
    queue = deque([Box(Fraction(0), BOUND, Fraction(0), BOUND)])
    passed = 0
    extrema = {
        "Q_h": None,
        "right_C_slope": None,
        "C_upper_gap": None,
        "L1_r": None,
        "L1_h_minus_r": None,
    }
    while queue:
        box = queue.popleft()
        try:
            center, enc, radii = center_and_interval(box)
            Qc, slope_c, gap_c, Lc = center
            Qi, slope_i, gap_i, Li = enc
            bounds = {
                "Q_h": lower_derivative(Qc, Qi, 1, radii),
                "right_C_slope": lower_value(slope_c, slope_i, radii),
                "C_upper_gap": lower_value(gap_c, gap_i, radii),
                "L1_r": upper_derivative(Lc, Li, 0, radii),
                "L1_h_minus_r": lower_direction(Lc, Li, (-1, 1), radii),
            }
            ok = (
                bounds["Q_h"].lower() > 0
                and bounds["right_C_slope"].lower() > 0
                and bounds["C_upper_gap"].lower() > 0
                and bounds["L1_r"].upper() < 0
                and bounds["L1_h_minus_r"].lower() > 0
            )
        except (ValueError, ZeroDivisionError):
            ok = False
            bounds = {}
        if ok:
            passed += 1
            for name, val in bounds.items():
                if extrema[name] is None:
                    extrema[name] = val
                elif name == "L1_r":
                    if val.upper() > extrema[name].upper():
                        extrema[name] = val
                else:
                    if val.lower() < extrema[name].lower():
                        extrema[name] = val
            continue
        if box.depth >= MAX_DEPTH:
            raise AssertionError(f"Failed to certify box at depth {box.depth}: {box}; bounds={bounds}")
        queue.extend(box.split())
    print(f"PASS: five two-variable endpoint inequalities on [0,0.127]^2 ({passed} boxes)")
    for name, value in extrema.items():
        endpoint = value.upper() if name == "L1_r" else value.lower()
        endpoint = value.upper() if name == "L1_r" else value.lower()
        print(f"  certified extremal bound {name}: {endpoint}")


def certify_convexity():
    # Direct interval enclosure of Q_rr on h=0, with adaptive 1D subdivision.
    intervals = deque([(Fraction(0), BOUND, 0)])
    passed = 0
    minimum = None
    while intervals:
        lo, hi, depth = intervals.popleft()
        r = Jet2.variable(interval(lo, hi), 0)
        h = Jet2.variable(arb(0), 1)
        try:
            Q, _, _, _ = quantities(r, h)
            val = Q.H[0][0]
            ok = val.lower() > 0
        except (ValueError, ZeroDivisionError):
            ok = False
            val = None
        if ok:
            passed += 1
            if minimum is None or val.lower() < minimum.lower():
                minimum = val
            continue
        if depth >= MAX_DEPTH:
            raise AssertionError(f"Failed Q_rr interval [{lo},{hi}] at depth {depth}: {val}")
        mid = (lo + hi) / 2
        intervals.append((lo, mid, depth + 1))
        intervals.append((mid, hi, depth + 1))
    print(f"PASS: Q_rr(r,0)>0 on [0,0.127] ({passed} intervals)")
    print(f"  certified lower bound Q_rr: {minimum.lower()}")


def certify_boundary_value():
    r = Jet2.variable(D - arb("1.708"), 0)
    h = Jet2.variable(arb(0), 1)
    l0, l1 = left_contact_coefficients(r, h)
    val = (l0 + l1).v
    if not (val.lower() > 0):
        raise AssertionError(f"Boundary value not positive: {val}")
    print(f"PASS: U_lambda_TL,1(-1) at (D-1.708,0) > 0: {val}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=1, help="accepted for compatibility; current implementation is deterministic serial")
    parser.parse_args()
    print(f"Arb precision: {BITS} bits; Phi terms: {SERIES_TERMS}")
    certify_square()
    certify_convexity()
    certify_boundary_value()
    print("PASS: all endpoint inequalities")


if __name__ == "__main__":
    main()
