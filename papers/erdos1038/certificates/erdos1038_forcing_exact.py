#!/usr/bin/env python3
"""Rigorous Arb certificate for the strengthened left endpoint lemma.

The program proves, uniformly for
  -1.708 <= a <= -sqrt(2),  0 <= b <= 1.836+a,  0 <= x <= 1,
that Gamma(a,b)>0 and U_{nu_{a,b}}(x)>0 for
  nu_{a,b}=delta_a+(1.395-b)delta_b+Gamma(a,b)delta_{1.071-b}.

The triangular (a,b)-domain is parameterized by a rational cube.  Adaptive
subdivision uses only outward-rounded Arb bounds.  Boxes meeting an atom are
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


def exact(q: Fraction | int) -> arb:
    if isinstance(q, int):
        return arb(q)
    return arb(q.numerator) / q.denominator


def interval(lo: Fraction, hi: Fraction) -> arb:
    return exact(lo).union(exact(hi))


def gamma_value(a: arb, b: arb) -> arb:
    numerator = -arb("0.0001") - (-1 - a).log() - (arb("1.395") - b) * (1 + b).log()
    return numerator / (arb("2.071") - b).log()


def log_recip_abs_lower(d: arb) -> arb:
    # inf_{t in d} log(1/|t|) = -log(sup |d|); if 0 is in d the
    # upper endpoint is +infinity, which is irrelevant for a lower bound.
    return -arb(abs(d).upper()).log()


def positive_coeff_product_lower(c: arb, L: arb) -> arb:
    if not (c.lower() > 0):
        raise ValueError("coefficient not certified positive")
    # L is a lower bound.  If it is negative, the worst coefficient is c_max;
    # if nonnegative, the worst coefficient is c_min.
    if L.lower() >= 0:
        return c.lower() * L
    return c.upper() * L


def box_bounds(s: arb, t: arb, x: arb):
    sqrt2 = arb(2).sqrt()
    a = -arb("1.708") + s * (arb("1.708") - sqrt2)
    b = t * (arb("1.836") + a)
    gam = gamma_value(a, b)
    if not (gam.lower() > 0):
        return gam, None
    c = arb("1.071") - b
    L_a = log_recip_abs_lower(x - a)
    L_b = log_recip_abs_lower(x - b)
    L_c = log_recip_abs_lower(x - c)
    potential_lower = L_a
    potential_lower += positive_coeff_product_lower(arb("1.395") - b, L_b)
    potential_lower += positive_coeff_product_lower(gam, L_c)
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

    def split(self):
        widths = [self.s1-self.s0, self.t1-self.t0, self.x1-self.x0]
        k = max(range(3), key=lambda i: widths[i])
        if k == 0:
            m=(self.s0+self.s1)/2
            return (Box(self.s0,m,self.t0,self.t1,self.x0,self.x1,self.depth+1),
                    Box(m,self.s1,self.t0,self.t1,self.x0,self.x1,self.depth+1))
        if k == 1:
            m=(self.t0+self.t1)/2
            return (Box(self.s0,self.s1,self.t0,m,self.x0,self.x1,self.depth+1),
                    Box(self.s0,self.s1,m,self.t1,self.x0,self.x1,self.depth+1))
        m=(self.x0+self.x1)/2
        return (Box(self.s0,self.s1,self.t0,self.t1,self.x0,m,self.depth+1),
                Box(self.s0,self.s1,self.t0,self.t1,m,self.x1,self.depth+1))


def main():
    q=deque([Box(Fraction(0),Fraction(1),Fraction(0),Fraction(1),Fraction(0),Fraction(1))])
    passed=0
    gamma_min=None
    pot_min=None
    while q:
        box=q.popleft()
        s=interval(box.s0,box.s1); t=interval(box.t0,box.t1); x=interval(box.x0,box.x1)
        try:
            gam, pot=box_bounds(s,t,x)
            ok=gam.lower()>0 and pot is not None and pot.lower()>0
        except (ValueError, ZeroDivisionError):
            ok=False; gam=pot=None
        if ok:
            passed+=1
            if gamma_min is None or gam.lower()<gamma_min:
                gamma_min=gam.lower()
            if pot_min is None or pot.lower()<pot_min:
                pot_min=pot.lower()
            continue
        if box.depth>=MAX_DEPTH:
            raise AssertionError(f"Failed box at depth {box.depth}: {box}; Gamma={gam}; U lower={pot}")
        q.extend(box.split())
    print(f"PASS: forcing domain covered by {passed} rational boxes")
    print(f"  certified Gamma lower bound: {gamma_min}")
    print(f"  certified potential lower bound: {pot_min}")
    print("PASS: strengthened left endpoint forcing certificate")


if __name__=='__main__':
    main()
