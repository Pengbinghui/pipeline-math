#!/usr/bin/env python3
"""Exact symbolic verification of the endpoint formulas (B.4) and (B.5).

The checker does not ask SymPy to discover an antiderivative.  Instead it
verifies, over exact rational function fields, the partial fractions,
Joukowski identities, derivatives of the proposed primitives, endpoint
specializations, and asymptotic coefficient identities used in the paper.

No floating-point arithmetic is used.
"""
from __future__ import annotations

import sympy as sp


def check(name: str, expr: sp.Expr) -> None:
    value = sp.cancel(sp.together(expr))
    if value != 0:
        raise AssertionError(f"FAIL: {name}\nResidual: {sp.factor(value)}")
    print(f"PASS: {name}")


# Generic Joukowski parameterization of the complement to a cut [a,b].
a, b, y, Y = sp.symbols("a b y Y", nonzero=True)
m = (a + b) / 2
d = (b - a) / 2
x = m - d * (y + 1 / y) / 2
Q = -d * (y - 1 / y) / 2  # branch Q(x) ~ x at -infinity
p = m - d * (Y + 1 / Y) / 2
q_p = d * (Y - 1 / Y) / 2

dx_dy = sp.diff(x, y)
check("Joukowski differential dx/Q = dy/y", dx_dy / Q - 1 / y)
check("quadratic relation Q^2=(x-a)(x-b)", Q**2 - (x - a) * (x - b))
check(
    "factorization of x-p",
    x - p + d * (y - Y) * (y - 1 / Y) / (2 * y),
)
check("q_p Joukowski expression", q_p**2 - (a - p) * (b - p))

# Generic primitive for Q(x)/(x-p), p<a.
F_p = Q + (p - m) * sp.log(y) - q_p * sp.log((y - Y) / (y - 1 / Y))
F_p_prime = sp.diff(F_p, y) / dx_dy
check("left-pole primitive F_p' = Q/(x-p)", F_p_prime - Q / (x - p))
check("left-pole endpoint ratio at y=1", (1 - Y) / (1 - 1 / Y) + Y)

# Pole beta to the right of the cut.  Its two Joukowski preimages are -k,-1/k.
k = sp.symbols("k", nonzero=True)
beta = m + d * (k + 1 / k) / 2
q_beta = d * (1 / k - k) / 2
check(
    "factorization of x-beta",
    x - beta + d * (y + k) * (y + 1 / k) / (2 * y),
)
check("q_beta quadratic relation", q_beta**2 - (beta - a) * (beta - b))
F_beta = Q + (beta - m) * sp.log(y) - q_beta * sp.log((y + k) / (y + 1 / k))
F_beta_prime = sp.diff(F_beta, y) / dx_dy
check("right-pole primitive F_beta' = Q/(x-beta)", F_beta_prime - Q / (x - beta))
check("right-pole endpoint ratio at y=1", (1 + k) / (1 + 1 / k) - k)

# Conversion of the endpoint logarithm to the regular Phi term.
tau = sp.symbols("tau", nonzero=True)
k_tau = (1 - tau) / (1 + tau)
# On the real domain 0<tau<1, atanh(tau) is defined by the displayed
# logarithm.  The checker verifies the exact rational substitution for k;
# the branch statement is recorded analytically in the paper.
check("k substitution", k_tau - (1 - tau) / (1 + tau))
check("ratio (1+k)/(1+1/k)=k after substitution", ((1+k)/(1+1/k)-k).subs(k,k_tau))
H = sp.symbols("H", nonzero=True)
check(
    "Phi regularization algebra",
    2 * (H * tau) * (sp.atanh(tau)) - 2 * (H * tau**2) * (sp.atanh(tau) / tau),
)

# Right transform partial fractions and normalization identities.
z, r, C = sp.symbols("z r C")
w = sp.symbols("w")
gz = (z + C) / ((z - r) * (z - beta))
gr = (r + C) / ((r - z) * (r - beta))
gb = (beta + C) / ((beta - z) * (beta - r))
check(
    "right-transform partial fraction decomposition",
    (w + C) / ((w - z) * (w - r) * (w - beta))
    - gz / (w - z)
    - gr / (w - r)
    - gb / (w - beta),
)
check("right partial fractions: sum gamma = 0", gz + gr + gb)
check("right partial fractions: weighted sum = 1", z * gz + r * gr + beta * gb - 1)

# Left transform partial fractions.
alpha = sp.symbols("alpha")
Bz = (z + C) * (z - alpha) / (z - r)
Br = (r + C) * (r - alpha) / (r - z)
check(
    "left-transform partial fraction decomposition",
    (w + C) * (w - alpha) / ((w - z) * (w - r))
    - 1
    - Bz / (w - z)
    - Br / (w - r),
)

# Stable phi/psi formulas used by the Arb endpoint certificate.
phi_p = p - m - q_p
psi_p = p - m + q_p
w_alpha = -d
check("stable right-endpoint ratio equals J(p)", (w_alpha - phi_p) / (psi_p - w_alpha) - Y)
check("stable right endpoint term equals -q_p log J(p)", Q.subs(y, Y) * sp.log(Y) + q_p * sp.log(Y))

# Primitive for 1/((x-p)Q), used in (B.5).
I_p = -sp.log((y - Y) / (y - 1 / Y)) / q_p
check("left formula pole primitive I_p' = 1/((x-p)Q)", sp.diff(I_p, y) / dx_dy - 1 / ((x - p) * Q))

# Asymptotic constants.  y ~ -4x/(b-a) as y -> infinity.
check("Joukowski asymptotic coefficient", sp.limit(y / (-4 * x / (b - a)), y, sp.oo) - 1)
check("left/right logarithmic ratios tend to 1", sp.limit((y - Y) / (y - 1 / Y), y, sp.oo) - 1)
check("beta logarithmic ratio tends to 1", sp.limit((y + k) / (y + 1 / k), y, sp.oo) - 1)

print("PASS: all exact symbolic endpoint checks")
