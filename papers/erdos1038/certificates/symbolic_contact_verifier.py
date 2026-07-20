#!/usr/bin/env python3
"""Exact symbolic checks for the h=0 contact identities.

This strengthened verifier constructs the literal h=0 specializations of both
manuscript endpoint formulas, R(r,0,C) and L(r,0,C).  It then checks the
Joukowski, square-root, absolute-value, and logarithmic-argument reductions
needed to obtain the specialized contact formulas.  Only after those literal
reductions have been certified does it verify the left-right residual identity,
the formula for the zero C(q,u,v), and the chain-rule reduction to K/(pD).

Domain convention: 0 < u < q < v < 1.  Positivity claims used to resolve real
absolute values and logarithms are checked after an exact positive-parameter
substitution in odds-ratio coordinates.
"""

from __future__ import annotations

import sympy as sp


def reduce_exact(expr: sp.Expr) -> sp.Expr:
    """Normalize log arguments, then reduce with logarithms treated as atoms."""
    normalized = expr.replace(
        lambda node: node.func == sp.log,
        lambda node: sp.log(sp.factor(sp.cancel(sp.together(node.args[0])))),
    )
    return sp.factor(sp.cancel(sp.together(normalized)))


def check(name: str, expr: sp.Expr) -> None:
    value = reduce_exact(expr)
    if value != 0:
        raise AssertionError(f"FAIL: {name}\nResidual: {value}")
    print(f"PASS: {name}")


def _poly_has_nonnegative_coefficients(
    poly: sp.Expr, variables: tuple[sp.Symbol, ...]
) -> bool:
    p = sp.Poly(sp.expand(poly), *variables)
    coeffs = p.coeffs()
    return (
        bool(coeffs)
        and all(c.is_number and c >= 0 for c in coeffs)
        and any(c > 0 for c in coeffs)
    )


def check_positive_rational(
    name: str,
    expr: sp.Expr,
    variables: tuple[sp.Symbol, ...],
) -> None:
    """Prove positivity when numerator and denominator have nonnegative coefficients."""
    numerator, denominator = sp.fraction(sp.cancel(expr))
    if not _poly_has_nonnegative_coefficients(numerator, variables):
        raise AssertionError(
            f"FAIL: could not prove positive numerator for {name}: "
            f"{sp.factor(numerator)}"
        )
    if not _poly_has_nonnegative_coefficients(denominator, variables):
        raise AssertionError(
            f"FAIL: could not prove positive denominator for {name}: "
            f"{sp.factor(denominator)}"
        )
    print(f"PASS: positive-domain check: {name}")


# ---------------------------------------------------------------------------
# Joukowski specialization at alpha = 2 q^2 - 1.
# ---------------------------------------------------------------------------
q, y = sp.symbols("q y", real=True, nonzero=True)
alpha = 2 * q**2 - 1
X = (alpha - y**2) / (1 - y**2)
root = 2 * y * (1 - q**2) / (1 - y**2)
J = (alpha + 1 - 2 * X + 2 * root) / (1 - alpha)

check("1-X_q(y)", 1 - X - 2 * (1 - q**2) / (1 - y**2))
check("alpha-X_q(y)", alpha - X - 2 * y**2 * (1 - q**2) / (1 - y**2))
check("J_{alpha,1}(X_q(y))=(1+y)/(1-y)", J - (1 + y) / (1 - y))
check("X_q(q)=-1", X.subs(y, q) + 1)
check("square-root ratio root/(X-1)=-y", root / (X - 1) + y)
check("square-root ratio (X-alpha)/root=-y", (X - alpha) / root + y)

u, v, C = sp.symbols("u v C", real=True, nonzero=True)


def Xq(s: sp.Expr) -> sp.Expr:
    return (alpha - s**2) / (1 - s**2)


def positive_root(s: sp.Expr) -> sp.Expr:
    return 2 * s * (1 - q**2) / (1 - s**2)


def J_at_Xq(s: sp.Expr) -> sp.Expr:
    x_s = Xq(s)
    return (alpha + 1 - 2 * x_s + 2 * positive_root(s)) / (1 - alpha)


def A(s: sp.Expr) -> sp.Expr:
    return (1 + s) / (1 - s)


def Lambda(s: sp.Expr) -> sp.Expr:
    return sp.log(A(s))


r = Xq(u)
z = Xq(v)
D = r - z
J_u = J_at_Xq(u)
J_q = J_at_Xq(q)
J_v = J_at_Xq(v)
root_u = positive_root(u)
root_v = positive_root(v)

# Encode 0<u<q<v<1 by increasing positive odds ratios
# A(u)=1+e_u, A(q)=1+e_u+e_q, A(v)=1+e_u+e_q+e_v.
e_u, e_q, e_v = sp.symbols("e_u e_q e_v", positive=True)
A_u_dom = 1 + e_u
A_q_dom = 1 + e_u + e_q
A_v_dom = 1 + e_u + e_q + e_v
odds_domain = {
    u: (A_u_dom - 1) / (A_u_dom + 1),
    q: (A_q_dom - 1) / (A_q_dom + 1),
    v: (A_v_dom - 1) / (A_v_dom + 1),
}
posvars = (e_u, e_q, e_v)

check_positive_rational("u", u.subs(odds_domain), posvars)
check_positive_rational("q-u", (q - u).subs(odds_domain), posvars)
check_positive_rational("v-q", (v - q).subs(odds_domain), posvars)
check_positive_rational("1-v", (1 - v).subs(odds_domain), posvars)
check_positive_rational("A(u)", A(u).subs(odds_domain), posvars)
check_positive_rational("A(q)", A(q).subs(odds_domain), posvars)
check_positive_rational("A(v)", A(v).subs(odds_domain), posvars)
check_positive_rational("positive root at u", root_u.subs(odds_domain), posvars)
check_positive_rational("positive root at v", root_v.subs(odds_domain), posvars)

# ---------------------------------------------------------------------------
# Literal right-endpoint formula at h=0.
# ---------------------------------------------------------------------------
right_constant_argument = (1 - alpha) / 4
check(
    "right h=0 constant logarithm arguments are reciprocal",
    right_constant_argument * (2 / (1 - q**2)) - 1,
)
check_positive_rational(
    "right constant logarithm argument",
    right_constant_argument.subs(odds_domain),
    posvars,
)
check("right h=0 Joukowski argument at -1", J_q - A(q))
check("right h=0 Joukowski argument at r", J_u - A(u))
check("right h=0 Joukowski argument at z", J_v - A(v))
check("right h=0 square-root coefficient at r", root_u / (r - 1) + u)
check("right h=0 square-root coefficient at z", root_v / (z - 1) + v)

R0_literal = (
    -sp.log(right_constant_argument)
    + (z + C) * root_v / ((z - r) * (z - 1)) * sp.log(J_v)
    + (r + C) * root_u / ((r - z) * (r - 1)) * sp.log(J_u)
)

p = sp.log(2 / (1 - q**2)) / Lambda(q)
R0_reduced = R0_literal.subs(
    {
        -sp.log(right_constant_argument): p * Lambda(q),
        sp.log(J_u): Lambda(u),
        sp.log(J_v): Lambda(v),
    },
    simultaneous=True,
)
R0_target = p * Lambda(q) + (
    v * (z + C) * Lambda(v) - u * (r + C) * Lambda(u)
) / D
check("complete literal right endpoint specialization R(r,0,C)", R0_reduced - R0_target)

# ---------------------------------------------------------------------------
# Literal left-endpoint formula at h=0.
# ---------------------------------------------------------------------------
# These are exactly the two raw ratios inside the absolute values in the
# displayed manuscript formula after h=0, beta=1, and -1=X_q(q).
ratio_v_raw = (J_v - J_q) / (J_q - 1 / J_v)
ratio_u_raw = (J_u - J_q) / (J_q - 1 / J_u)
ratio_v_positive = A(v) * (v - q) / (v + q)
ratio_u_absolute = A(u) * (q - u) / (q + u)

check("left v logarithmic ratio before absolute value", ratio_v_raw - ratio_v_positive)
check("left u logarithmic ratio before absolute value", ratio_u_raw + ratio_u_absolute)
check_positive_rational(
    "left v absolute logarithm argument",
    ratio_v_positive.subs(odds_domain),
    posvars,
)
check_positive_rational(
    "left u absolute logarithm argument",
    ratio_u_absolute.subs(odds_domain),
    posvars,
)

constant_argument = (1 - alpha) * J_q / 4
check(
    "left h=0 constant logarithm argument",
    constant_argument - (1 + q) ** 2 / 2,
)
check_positive_rational(
    "left constant logarithm argument",
    constant_argument.subs(odds_domain),
    posvars,
)

# Literal h=0 specialization of the displayed formula for mathsf L, including
# the two absolute values exactly as printed in the manuscript.
abs_ratio_v = sp.Abs(ratio_v_raw)
abs_ratio_u = sp.Abs(ratio_u_raw)
L0_literal = (
    -sp.log(constant_argument)
    + (z + C) * (z - alpha) / ((z - r) * root_v) * sp.log(abs_ratio_v)
    + (r + C) * (r - alpha) / ((r - z) * root_u) * sp.log(abs_ratio_u)
)

# Resolve the absolute values using the exact sign checks above.
L0_abs_resolved = L0_literal.xreplace(
    {
        abs_ratio_v: ratio_v_positive,
        abs_ratio_u: ratio_u_absolute,
    }
)

M_R = sp.log((q + u) / (q - u))
M_L = sp.log((q + v) / (v - q))
check_positive_rational("right contact log argument", ((q + u) / (q - u)).subs(odds_domain), posvars)
check_positive_rational("left contact log argument", ((q + v) / (v - q)).subs(odds_domain), posvars)

# Certify the three real logarithm rewrites by equality of their positive
# arguments.  No unqualified force=True log expansion is used.
check(
    "left constant log rewrite argument identity",
    A(q) / (constant_argument * (2 / (1 - q**2))) - 1,
)
check(
    "left v log rewrite argument identity",
    ratio_v_positive / (A(v) / ((q + v) / (v - q))) - 1,
)
check(
    "left u log rewrite argument identity",
    ratio_u_absolute / (A(u) / ((q + u) / (q - u))) - 1,
)

# Apply only the three certified real-log rewrites.
L0_reduced = L0_abs_resolved.xreplace(
    {
        sp.log(constant_argument): -(p - 1) * Lambda(q),
        sp.log(ratio_v_positive): Lambda(v) - M_L,
        sp.log(ratio_u_absolute): Lambda(u) - M_R,
    }
)
L0_target = (p - 1) * Lambda(q) + (
    v * (z + C) * (Lambda(v) - M_L)
    - u * (r + C) * (Lambda(u) - M_R)
) / D
check("complete literal left endpoint specialization L(r,0,C)", L0_reduced - L0_target)

# ---------------------------------------------------------------------------
# Contact residual, C-star, and chain rule, now tied to the literal reductions.
# ---------------------------------------------------------------------------
F_R = Lambda(u) - p * M_R
F_L = Lambda(v) - p * M_L
residual = (
    v * (z + C) * F_L - u * (r + C) * F_R
) / (p * D)
check(
    "exact left-right residual identity from literal endpoint formulas",
    L0_target - (p - 1) * R0_target / p - residual,
)

C_star = (
    r * u * Lambda(u)
    - z * v * Lambda(v)
    - D * p * Lambda(q)
) / (v * Lambda(v) - u * Lambda(u))
check("right contact vanishes at C(q,u,v)", R0_target.subs(C, C_star))

# Verify the derivative formulas entering K.
X_u = sp.diff(Xq(u), u)
X_v = sp.diff(Xq(v), v)
F_R_u = sp.diff(F_R, u)
F_L_v = sp.diff(F_L, v)
check(
    "X_q'(u) formula",
    X_u + 4 * u * (1 - q**2) / (1 - u**2) ** 2,
)
check(
    "X_q'(v) formula",
    X_v + 4 * v * (1 - q**2) / (1 - v**2) ** 2,
)
check(
    "partial_u F_R formula",
    F_R_u - (2 / (1 - u**2) - 2 * p * q / (q**2 - u**2)),
)
check(
    "partial_v F_L formula",
    F_L_v - (2 / (1 - v**2) + 2 * p * q / (v**2 - q**2)),
)

# Abstract only the final chain-rule bookkeeping.  The objects substituted into
# it have just been identified with the literal endpoint/contact expressions.
pA, CA, rA, zA, DA = sp.symbols("pA CA rA zA DA", nonzero=True)
uA, vA = sp.symbols("uA vA", nonzero=True)
FRA, FLA = sp.symbols("FRA FLA")
XuA, XvA, FRuA, FLvA, CpA = sp.symbols(
    "XuA XvA FRuA FLvA CpA", nonzero=True
)
up = 1 / XuA
vp = 1 / XvA
d_numerator = (
    (vp * (zA + CA) + vA * (1 + CpA)) * FLA
    + vA * (zA + CA) * FLvA * vp
    - (up * (rA + CA) + uA * (1 + CpA)) * FRA
    - uA * (rA + CA) * FRuA * up
)
dH = d_numerator / (pA * DA)
contact_dH = sp.simplify(dH.subs({FRA: 0, FLA: 0}))
K = (
    vA * (zA + CA) * FLvA / XvA
    - uA * (rA + CA) * FRuA / XuA
)
check("chain-rule derivative reduces to K/(pD)", contact_dH - K / (pA * DA))

residual_abstract = (
    vA * (zA + CA) * FLA - uA * (rA + CA) * FRA
) / (pA * DA)
check(
    "C0 derivative cancels at contact",
    sp.diff(residual_abstract, CA).subs({FRA: 0, FLA: 0}),
)

print("PASS: literal h=0 contact verifier for both endpoint formulas")
