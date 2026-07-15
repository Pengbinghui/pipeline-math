#!/usr/bin/env python3
"""Exact symbolic checks for the contact identities in Lemma B.1.

This script verifies the algebraic reductions from (B.4)-(B.5) at h=0,
the residual identity, and the chain-rule reduction of the contact derivative
to K/(pD).  Logarithms are represented by independent symbols once their
real-domain arguments have been identified; every subsequent calculation is
exact algebra.
"""
from __future__ import annotations

import sympy as sp


def check(name: str, expr: sp.Expr) -> None:
    value = sp.cancel(sp.together(expr))
    if value != 0:
        raise AssertionError(f"FAIL: {name}\nResidual: {sp.factor(value)}")
    print(f"PASS: {name}")


# Joukowski specializations at alpha=2q^2-1.
q, y = sp.symbols("q y", nonzero=True)
alpha = 2 * q**2 - 1
X = (alpha - y**2) / (1 - y**2)
check("1-X_q(y)", 1 - X - 2 * (1 - q**2) / (1 - y**2))
check("alpha-X_q(y)", alpha - X - 2 * y**2 * (1 - q**2) / (1 - y**2))
root = 2 * y * (1 - q**2) / (1 - y**2)  # positive on 0<y<1
J = (alpha + 1 - 2 * X + 2 * root) / (1 - alpha)
check("J_{alpha,1}(X_q(y))=(1+y)/(1-y)", J - (1 + y) / (1 - y))
check("X_q(q)=-1", X.subs(y, q) + 1)
check("square-root ratio 1", root / (X - 1) + y)
check("square-root ratio 2", (X - alpha) / root + y)

# Exact specialized endpoint identities.
p, C, r, z, D = sp.symbols("p C r z D", nonzero=True)
u, v = sp.symbols("u v", nonzero=True)
Lq, Lu, Lv, MR, ML = sp.symbols("Lq Lu Lv MR ML")
FR = Lu - p * MR
FL = Lv - p * ML
R = p * Lq + (v * (z + C) * Lv - u * (r + C) * Lu) / D
L = (p - 1) * Lq + (
    v * (z + C) * (Lv - ML) - u * (r + C) * (Lu - MR)
) / D
residual = (v * (z + C) * FL - u * (r + C) * FR) / (p * D)
check("exact left-right residual identity", L - (p - 1) * R / p - residual)

# The zero of the right contact is the displayed C(q,u,v).
Cstar = (r * u * Lu - z * v * Lv - D * p * Lq) / (v * Lv - u * Lu)
check("right contact vanishes at Cstar (using D=r-z)", (R.subs(C, Cstar)).subs(D, r-z))

# Chain-rule calculation.  Treat q,p,D as constants and r as the path
# parameter, with z'=1, u'=1/Xu, v'=1/Xv, C'=Cp.
Xu, Xv, FRu, FLv, Cp = sp.symbols("Xu Xv FRu FLv Cp", nonzero=True)
up = 1 / Xu
vp = 1 / Xv
# Product-rule derivative of the numerator of H.
d_num = (
    (vp * (z + C) + v * (1 + Cp)) * FL
    + v * (z + C) * FLv * vp
    - (up * (r + C) + u * (1 + Cp)) * FR
    - u * (r + C) * FRu * up
)
dH = d_num / (p * D)
contact_dH = sp.simplify(dH.subs({FR: 0, FL: 0}))
K = v * (z + C) * FLv / Xv - u * (r + C) * FRu / Xu
check("chain-rule derivative reduces to K/(pD)", contact_dH - K / (p * D))
check("C0 derivative cancels at contact", sp.diff(residual, C).subs({FR: 0, FL: 0}))

# Elementary logarithmic argument simplifications used to pass from (B.5)
# to the specialized formula.  A(t)=(1+t)/(1-t).
t = sp.symbols("t")
A = lambda s: (1 + s) / (1 - s)
ratio_v = (A(v) - A(q)) / (A(q) - 1 / A(v))
ratio_u = (A(u) - A(q)) / (A(q) - 1 / A(u))
check("v logarithmic ratio", ratio_v - A(v) * (v - q) / (v + q))
# For u<q the raw ratio is negative; its absolute value reverses the sign.
check("u logarithmic ratio before absolute value", ratio_u + A(u) * (q - u) / (q + u))

print("PASS: all exact symbolic contact checks")
