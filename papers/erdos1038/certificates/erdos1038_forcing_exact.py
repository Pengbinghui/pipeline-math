#!/usr/bin/env python3

"""Rigorous Arb certificate for the numerical input to Lemma 3.2.

The program certifies, uniformly for

    -1.708 <= ell <= -sqrt(2),
    0 <= b <= 1.836 + ell,
    0 <= x <= 1,

that

    Gamma(ell,b) > 0,
    1.395 - b > 0,
    U_{nu_{ell,b}}(x) > 0,

for

    nu_{ell,b} = delta_ell
                 + (1.395-b) delta_b
                 + Gamma(ell,b) delta_{1.071-b}.

It also certifies the global lane-separation inequality

    2(1.836 + ell) < 1.071

throughout the ell-range, together with positivity of the lane length
1.836+ell.  By the definition of Gamma, one has the exact algebraic identity

    U_{nu_{ell,b}}(-1) = 10^(-4).

The measure-theoretic implication from these numerical facts to
ell <= -1.708 is proved in the manuscript; this script certifies exactly
the numerical premises used in that proof.

The triangular (ell,b)-domain is parameterized by a rational cube. Adaptive
subdivision uses only outward-rounded Arb bounds. Boxes meeting an atom are
harmless: the logarithmic singularity is positive, and the lower-bound routine
uses the farthest distance from the atom.
"""

from __future__ import annotations

import os
from collections import deque
from dataclasses import dataclass
from fractions import Fraction

from flint import arb, ctx

BITS = int(os.environ.get("ERDOS1038_ARB_BITS", "384"))
ctx.prec = BITS

MAX_DEPTH = int(os.environ.get("ERDOS1038_FORCING_MAX_DEPTH", "34"))

# All decimal constants used by the forcing family, represented as exact
# rationals before conversion to Arb.
A_LEFT = Fraction(-427, 250)       # -1.708
CAP = Fraction(459, 250)           # 1.836
WEIGHT_BASE = Fraction(279, 200)   # 1.395
SHIFT = Fraction(1071, 1000)       # 1.071
DIST_SHIFT = Fraction(2071, 1000)  # 2.071
EPSILON = Fraction(1, 10_000)      # 10^(-4)


def exact(q: Fraction | int) -> arb:
    """Convert an integer or rational to an exact Arb point ball."""
    if isinstance(q, int):
        return arb(q)
    return arb(q.numerator) / q.denominator


def interval(lo: Fraction, hi: Fraction) -> arb:
    """Return the smallest Arb interval containing the rational endpoints."""
    return exact(lo).union(exact(hi))


def gamma_value(ell: arb, b: arb) -> arb:
    """Return Gamma(ell,b), defined so that U_{nu_{ell,b}}(-1)=10^(-4)."""
    numerator = (
        -exact(EPSILON)
        - (-arb(1) - ell).log()
        - (exact(WEIGHT_BASE) - b) * (arb(1) + b).log()
    )
    return numerator / (exact(DIST_SHIFT) - b).log()


def log_recip_abs_lower(d: arb) -> arb:
    """Lower-bound inf_{t in d} log(1/|t|)."""
    # If 0 lies in d, the function has a +infinity singularity.  This does
    # not affect a lower bound, which is attained at the farthest endpoint.
    return -arb(abs(d).upper()).log()


def positive_coeff_product_lower(c: arb, lower_bound: arb) -> arb:
    """Lower-bound c*L when c is certified positive and L is an interval bound."""
    if not (c.lower() > 0):
        raise ValueError("coefficient not certified positive")

    # If L is nonnegative, the smallest coefficient is worst.  If L may be
    # negative, the largest coefficient is worst.
    if lower_bound.lower() >= 0:
        return c.lower() * lower_bound
    return c.upper() * lower_bound


def certify_global_geometry() -> tuple[arb, arb, arb]:
    """Certify the side conditions used in the measure-counting argument."""
    sqrt2 = arb(2).sqrt()
    b_min = exact(CAP + A_LEFT)
    b_max = exact(CAP) - sqrt2

    lane_gap = exact(SHIFT) - 2 * b_max
    weight_margin = exact(WEIGHT_BASE) - b_max
    c_min = exact(SHIFT) - b_max
    denominator_margin = exact(DIST_SHIFT) - b_max - arb(1)

    if not (b_min.lower() > 0):
        raise AssertionError(f"lane length not positive: {b_min}")
    if not (lane_gap.lower() > 0):
        raise AssertionError(f"forcing lanes not disjoint: gap={lane_gap}")
    if not (weight_margin.lower() > 0):
        raise AssertionError(f"1.395-b not positive: margin={weight_margin}")
    if not (c_min.lower() > 0):
        raise AssertionError(f"reflected lane not positive: c_min={c_min}")
    if not (denominator_margin.lower() > 0):
        raise AssertionError(
            f"log denominator not certified positive: margin={denominator_margin}"
        )

    return b_min, b_max, lane_gap


def box_bounds(s: arb, t: arb, x: arb) -> tuple[arb, arb | None]:
    """Return interval lower bounds for Gamma and U_nu on one parameter box."""
    sqrt2 = arb(2).sqrt()

    # s in [0,1] parametrizes ell in [-1.708,-sqrt(2)].
    ell = exact(A_LEFT) + s * (-sqrt2 - exact(A_LEFT))

    # t in [0,1] parametrizes the triangular range 0 <= b <= 1.836+ell.
    b = t * (exact(CAP) + ell)

    weight_b = exact(WEIGHT_BASE) - b
    if not (weight_b.lower() > 0):
        raise ValueError("1.395-b not certified positive")

    gam = gamma_value(ell, b)
    if not (gam.lower() > 0):
        return gam, None

    c = exact(SHIFT) - b
    l_ell = log_recip_abs_lower(x - ell)
    l_b = log_recip_abs_lower(x - b)
    l_c = log_recip_abs_lower(x - c)

    potential_lower = l_ell
    potential_lower += positive_coeff_product_lower(weight_b, l_b)
    potential_lower += positive_coeff_product_lower(gam, l_c)

    return gam, potential_lower


@dataclass(frozen=True)
class Box:
    s0: Fraction
    s1: Fraction
    t0: Fraction
    t1: Fraction
    x0: Fraction
    x1: Fraction
    depth: int = 0

    def split(self) -> tuple["Box", "Box"]:
        widths = [self.s1 - self.s0, self.t1 - self.t0, self.x1 - self.x0]
        coordinate = max(range(3), key=lambda i: widths[i])

        if coordinate == 0:
            midpoint = (self.s0 + self.s1) / 2
            return (
                Box(
                    self.s0,
                    midpoint,
                    self.t0,
                    self.t1,
                    self.x0,
                    self.x1,
                    self.depth + 1,
                ),
                Box(
                    midpoint,
                    self.s1,
                    self.t0,
                    self.t1,
                    self.x0,
                    self.x1,
                    self.depth + 1,
                ),
            )

        if coordinate == 1:
            midpoint = (self.t0 + self.t1) / 2
            return (
                Box(
                    self.s0,
                    self.s1,
                    self.t0,
                    midpoint,
                    self.x0,
                    self.x1,
                    self.depth + 1,
                ),
                Box(
                    self.s0,
                    self.s1,
                    midpoint,
                    self.t1,
                    self.x0,
                    self.x1,
                    self.depth + 1,
                ),
            )

        midpoint = (self.x0 + self.x1) / 2
        return (
            Box(
                self.s0,
                self.s1,
                self.t0,
                self.t1,
                self.x0,
                midpoint,
                self.depth + 1,
            ),
            Box(
                self.s0,
                self.s1,
                self.t0,
                self.t1,
                midpoint,
                self.x1,
                self.depth + 1,
            ),
        )


def main() -> None:
    b_min, b_max, lane_gap = certify_global_geometry()

    queue = deque(
        [
            Box(
                Fraction(0),
                Fraction(1),
                Fraction(0),
                Fraction(1),
                Fraction(0),
                Fraction(1),
            )
        ]
    )

    passed = 0
    gamma_min = None
    potential_min = None

    while queue:
        box = queue.popleft()
        s = interval(box.s0, box.s1)
        t = interval(box.t0, box.t1)
        x = interval(box.x0, box.x1)

        try:
            gam, potential = box_bounds(s, t, x)
            ok = (
                gam.lower() > 0
                and potential is not None
                and potential.lower() > 0
            )
        except (ValueError, ZeroDivisionError):
            ok = False
            gam = None
            potential = None

        if ok:
            passed += 1
            if gamma_min is None or gam.lower() < gamma_min:
                gamma_min = gam.lower()
            if potential_min is None or potential.lower() < potential_min:
                potential_min = potential.lower()
            continue

        if box.depth >= MAX_DEPTH:
            raise AssertionError(
                f"Failed box at depth {box.depth}: {box}; "
                f"Gamma={gam}; U lower={potential}"
            )
        queue.extend(box.split())

    print("PASS: global forcing geometry")
    print(f" certified lane-length range: [{b_min}, {b_max}]")
    print(f" certified lane-separation gap 1.071-2(1.836+ell): {lane_gap}")
    print(" exact identity by definition: U_nu(-1) = 0.0001")
    print(f"PASS: forcing domain covered by {passed} rational boxes")
    print(f" certified Gamma lower bound: {gamma_min}")
    print(f" certified potential lower bound on [0,1]: {potential_min}")
    print("PASS: numerical premises of Lemma 3.2")


if __name__ == "__main__":
    main()
