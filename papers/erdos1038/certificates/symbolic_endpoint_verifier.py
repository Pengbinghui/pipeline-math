#!/usr/bin/env python3
"""Strict exact verifier for the two compressed-endpoint formulas.

1. The density in Definition 4.1 is *derived from the jump* of the proposed
   Cauchy transform, and the atomic masses are *derived from its residues*.
2. The transform has mass one at infinity.  Hence the jump/residue data identify
   the literal positive measure used in the manuscript (by the standard slit-
   plane residue argument proved there).
3. A displayed primitive is differentiated exactly and shown to have derivative
   equal to that Cauchy transform.
4. Its normalization at -infinity and its real endpoint limits are checked.
5. The resulting endpoint values are reduced exactly to the manuscript's
   formulas (B.4) and (B.5).




Real-domain conventions
-----------------------
For a<b, Q_{a,b}(w)=sqrt((w-a)(w-b)) is the branch holomorphic on
C\\[a,b] with Q(w)/w -> 1 at infinity.  For p<a,
Q(p)=-sqrt((a-p)(b-p)).  The real logarithms below are logarithms of absolute
values when a primitive crosses a real pole.  The needed orderings are encoded
by positive-parameter substitutions and checked algebraically near the end of
the script.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


# ---------------------------------------------------------------------------
# Exact-checking helpers.
# ---------------------------------------------------------------------------

def exact_reduce(expr: sp.Expr) -> sp.Expr:
    """Reduce an exact rational expression whose transcendental terms are atoms."""
    return sp.factor(sp.cancel(sp.together(expr)))


def check_zero(name: str, expr: sp.Expr) -> None:
    value = exact_reduce(expr)
    if value != 0:
        raise AssertionError(f"FAIL: {name}\nResidual: {value}")
    print(f"PASS: {name}")


def _normalize_log_arguments(expr: sp.Expr) -> sp.Expr:
    """Algebraically normalize each log argument without using a log law."""
    return expr.replace(
        lambda node: node.func == sp.log,
        lambda node: sp.log(sp.factor(sp.cancel(sp.together(node.args[0])))),
    )


def check_log_zero(name: str, expr: sp.Expr) -> None:
    """Use only log laws justified by SymPy's positivity assumptions."""
    value = _normalize_log_arguments(expr)
    value = sp.expand_log(value, force=False)
    value = sp.simplify(value)
    value = exact_reduce(value)
    if value != 0:
        raise AssertionError(f"FAIL: {name}\nResidual after safe log expansion: {value}")
    print(f"PASS: {name}")




def _poly_has_nonnegative_coefficients(poly: sp.Expr, variables: tuple[sp.Symbol, ...]) -> bool:
    P = sp.Poly(sp.expand(poly), *variables)
    coeffs = P.coeffs()
    return bool(coeffs) and all(c.is_number and c >= 0 for c in coeffs) and any(c > 0 for c in coeffs)


def check_positive_rational(
    name: str,
    expr: sp.Expr,
    variables: tuple[sp.Symbol, ...],
) -> None:
    """Certify positivity when numerator/denominator have nonnegative coefficients.

    All variables supplied to this helper are assumed strictly positive.  This
    is a deliberately small exact sign prover, sufficient for the branch/order
    checks used below.
    """
    num, den = sp.fraction(sp.cancel(expr))
    if not _poly_has_nonnegative_coefficients(num, variables):
        raise AssertionError(f"FAIL: could not prove positive numerator for {name}: {sp.factor(num)}")
    if not _poly_has_nonnegative_coefficients(den, variables):
        raise AssertionError(f"FAIL: could not prove positive denominator for {name}: {sp.factor(den)}")
    print(f"PASS: positive-domain check: {name}")


# ---------------------------------------------------------------------------
# Generic Joukowski coordinate and normalized square-root branch.
# ---------------------------------------------------------------------------
a, b, y = sp.symbols("a b y", real=True, nonzero=True)
m = (a + b) / 2
d = (b - a) / 2
x = m - d * (y + 1 / y) / 2
Q = -d * (y - 1 / y) / 2
dx_dy = sp.diff(x, y)

Y = sp.symbols("Y", positive=True)
p = m - d * (Y + 1 / Y) / 2
q_p = d * (Y - 1 / Y) / 2
J_p = exact_reduce((a + b - 2 * p + 2 * q_p) / (b - a))

check_zero("Joukowski differential dx/Q=dy/y", dx_dy / Q - 1 / y)
check_zero("Q^2=(x-a)(x-b)", Q**2 - (x - a) * (x - b))
check_zero("q_p^2=(a-p)(b-p)", q_p**2 - (a - p) * (b - p))
check_zero("J_{a,b}(p)=Y", J_p - Y)
check_zero("left real branch Q(p)=-q_p", Q.subs(y, Y) + q_p)


@dataclass(frozen=True)
class LeftPole:
    coordinate: sp.Expr
    pole: sp.Expr
    root: sp.Expr
    ratio: sp.Expr
    F: sp.Expr
    I: sp.Expr


def left_pole(Yp: sp.Expr) -> LeftPole:
    pole = m - d * (Yp + 1 / Yp) / 2
    root = d * (Yp - 1 / Yp) / 2
    ratio = (y - Yp) / (y - 1 / Yp)
    # On each real component away from the pole, d log|ratio| = d log(ratio).
    F = Q + (pole - m) * sp.log(y) - root * sp.log(ratio)
    I = -sp.log(ratio) / root
    return LeftPole(Yp, pole, root, ratio, F, I)


generic = left_pole(Y)
check_zero(
    "left-pole primitive derivative",
    sp.diff(generic.F, y) / dx_dy - Q / (x - p),
)
check_zero(
    "inverse-Q pole primitive derivative",
    sp.diff(generic.I, y) / dx_dy - 1 / ((x - p) * Q),
)
check_zero("left-pole endpoint absolute ratio", generic.ratio.subs(y, 1) + Y)
eps_y, gap_y = sp.symbols("eps_y gap_y", positive=True)
real_endpoint_ratio = generic.ratio.subs({y: 1 + eps_y, Y: 1 + gap_y})
check_log_zero(
    "left-pole real logarithm has endpoint value log(Y)",
    sp.limit(sp.log(sp.Abs(real_endpoint_ratio)), eps_y, 0, dir="+")
    - sp.log(1 + gap_y),
)
check_zero(
    "Joukowski asymptotic coefficient",
    sp.limit(y / (-4 * x / (b - a)), y, sp.oo) - 1,
)
check_zero("left-pole ratio tends to one", sp.limit(generic.ratio, y, sp.oo) - 1)


# ---------------------------------------------------------------------------
# Right compression: density/atoms, transform primitive, endpoint value.
# ---------------------------------------------------------------------------
Yz, Yr, k = sp.symbols("Yz Yr k", positive=True)
C = sp.symbols("C", real=True)
w, Qw = sp.symbols("w Qw")
zdata = left_pole(Yz)
rdata = left_pole(Yr)
z, qz, Rz, Fz = zdata.pole, zdata.root, zdata.ratio, zdata.F
r, qr, Rr, Fr = rdata.pole, rdata.root, rdata.ratio, rdata.F

beta = m + d * (k + 1 / k) / 2
q_beta = d * (1 / k - k) / 2
Rbeta = (y + k) / (y + 1 / k)
Fbeta = Q + (beta - m) * sp.log(y) - q_beta * sp.log(Rbeta)

check_zero("q_beta^2=(beta-a)(beta-b)", q_beta**2 - (beta - a) * (beta - b))
check_zero("right real branch Q(beta)=q_beta", Q.subs(y, -1 / k) - q_beta)
check_zero("right-pole primitive derivative", sp.diff(Fbeta, y) / dx_dy - Q / (x - beta))
check_zero("right-pole endpoint ratio", Rbeta.subs(y, 1) - k)
check_zero("right-pole ratio tends to one", sp.limit(Rbeta, y, sp.oo) - 1)

gz = (z + C) / ((z - r) * (z - beta))
gr = (r + C) / ((r - z) * (r - beta))
gb = (beta + C) / ((beta - z) * (beta - r))
# For T_R=(b,beta), chi_{a,beta}*chi_{b,beta}=Q_{a,b}/(w-beta).
# Squaring and using Q^2=(w-a)(w-b) verifies the algebraic reduction; both
# sides tend to +1 at infinity, fixing the same branch.
right_chi_square = (w - a) * (w - b) / (w - beta) ** 2
right_Q_square = (Qw / (w - beta)) ** 2
check_zero(
    "right compressed chi-product reduction",
    right_Q_square.subs(Qw**2, (w - a) * (w - b)) - right_chi_square,
)
S_R_w = (w + C) * Qw / ((w - z) * (w - r) * (w - beta))
S_R = S_R_w.subs({w: x, Qw: Q})

check_zero(
    "right transform partial fractions",
    S_R - gz * Q / (x - z) - gr * Q / (x - r) - gb * Q / (x - beta),
)
check_zero("right partial fractions: sum", gz + gr + gb)
check_zero("right partial fractions: first moment", z * gz + r * gr + beta * gb - 1)
check_zero("right transform has mass one", sp.limit(x * S_R, y, sp.oo) - 1)

# Residues are the atom masses.  The residues are computed from the same
# transform object used by the primitive and jump checks.
def branch_residue(transform: sp.Expr, pole: sp.Expr, branch_value: sp.Expr) -> sp.Expr:
    cancelled = sp.cancel((w - pole) * transform)
    return exact_reduce(cancelled.subs({w: pole, Qw: branch_value}))


mz_R = -(z + C) * qz / ((z - r) * (z - beta))
mr_R = -(r + C) * qr / ((r - z) * (r - beta))
mb_R = (beta + C) * q_beta / ((beta - z) * (beta - r))
check_zero("right z atom equals residue", mz_R - branch_residue(S_R_w, z, -qz))
check_zero("right r atom equals residue", mr_R - branch_residue(S_R_w, r, -qr))
check_zero("right beta atom equals residue", mb_R - branch_residue(S_R_w, beta, q_beta))

s = sp.symbols("s", real=True)
qcut = sp.symbols("qcut", positive=True)
# Definition 4.1 for T_R=(b,beta) contains the two square-root factors
# sqrt((s-a)/(beta-s)) and sqrt((b-s)/(beta-s)).  Their product is
# qcut/(beta-s), where qcut=sqrt((s-a)(b-s)).
check_zero(
    "right compressed density square-root reduction",
    (s - a) * (b - s) / (beta - s) ** 2
    - ((s - a) / (beta - s)) * ((b - s) / (beta - s)),
)
S_R_plus = S_R_w.subs({w: s, Qw: sp.I * qcut})
S_R_minus = S_R_w.subs({w: s, Qw: -sp.I * qcut})
rho_R_from_jump = exact_reduce(-(S_R_plus - S_R_minus) / (2 * sp.pi * sp.I))
rho_R_manuscript = (s + C) * qcut / (sp.pi * (s - z) * (s - r) * (beta - s))
check_zero("right jump gives the manuscript density", rho_R_from_jump - rho_R_manuscript)


P_R = gz * Fz + gr * Fr + gb * Fbeta
check_zero("right assembled primitive derivative", sp.diff(P_R, y) / dx_dy - S_R)
check_zero("right primitive Q coefficient vanishes", gz + gr + gb)
check_zero(
    "right primitive log(y) coefficient is one",
    gz * (z - m) + gr * (r - m) + gb * (beta - m) - 1,
)

# At y=1 (x=a), Q=0 and log(y)=0.  The real parts of the pole
# logarithms are log of the following positive absolute ratios.
check_zero("right z endpoint absolute ratio is Yz", Rz.subs(y, 1) + Yz)
check_zero("right r endpoint absolute ratio is Yr", Rr.subs(y, 1) + Yr)
check_zero("right beta endpoint ratio is k", Rbeta.subs(y, 1) - k)
P_R_at_a = -gz * qz * sp.log(Yz) - gr * qr * sp.log(Yr) - gb * q_beta * sp.log(k)
U_R_from_transform = -sp.log((b - a) / 4) - P_R_at_a

# First compare with the same endpoint formula written with log(k), before the
# Phi rewrite.  Coefficients are transcribed independently from (B.4).
R_logk = (
    -sp.log((b - a) / 4)
    + (z + C) * qz * sp.log(Yz) / ((z - r) * (z - beta))
    + (r + C) * qr * sp.log(Yr) / ((r - z) * (r - beta))
    + (beta + C) * q_beta * sp.log(k) / ((beta - z) * (beta - r))
)
check_zero("right normalized transform value equals the log(k) endpoint formula", U_R_from_transform - R_logk)

# Verify the real identity converting the beta term to Phi.  Put
# tau=(1-k)/(1+k), H=beta-a, h=H*tau^2.  On 0<k<1,
# Phi(tau^2)=atanh(tau)/tau=log((1+tau)/(1-tau))/(2*tau).
tau = (1 - k) / (1 + k)
H = beta - a
h = beta - b
Phi_tau_squared = sp.log((1 + tau) / (1 - tau)) / (2 * tau)
check_zero("right geometry q_beta=(beta-a)*tau", q_beta - H * tau)
check_zero("right geometry beta-b=(beta-a)*tau^2", h - H * tau**2)

R_B4 = (
    -sp.log((b - a) / 4)
    + (z + C) * qz * sp.log(Yz) / ((z - r) * (z - beta))
    + (r + C) * qr * sp.log(Yr) / ((r - z) * (r - beta))
    - 2 * h * (beta + C) * Phi_tau_squared / ((beta - z) * (beta - r))
)

# Encode b-a>0 and 0<k<1 by b=a+2*d0, k=1/(1+eta), with d0,eta>0.
# We simplify the domain parameters *before* forming logarithms.  This lets
# SymPy use only positivity-justified log rules; no forced expansion is needed.
d0, eta = sp.symbols("d0 eta", positive=True)
k_dom = 1 / (1 + eta)
tau_dom = eta / (eta + 2)
right_domain = {b: a + 2 * d0, k: k_dom}
beta_dom = sp.factor(beta.subs(right_domain))
q_beta_dom = sp.factor(q_beta.subs(right_domain))
h_dom = sp.factor(h.subs(right_domain))
gb_dom = sp.factor(gb.subs(right_domain))
phi_ratio_dom = sp.factor(sp.cancel((1 + tau_dom) / (1 - tau_dom)))
Phi_dom = sp.log(phi_ratio_dom) / (2 * tau_dom)

check_log_zero(
    "right beta log(k) term equals the Phi term",
    gb_dom * q_beta_dom * sp.log(k_dom) + 2 * h_dom * gb_dom * Phi_dom,
)
# Directly check the manuscript expression R_B4.  Log arguments are normalized
# algebraically before applying only positivity-justified real log laws.
check_log_zero(
    "Equation (B.6), right endpoint: transform potential equals R(r,h,C)",
    (U_R_from_transform - R_B4).subs(right_domain),
)

# The h=0 endpoint is the continuous k->1 limit (eta->0).
check_log_zero("Phi(tau^2) tends to one as h->0", sp.limit(Phi_dom, eta, 0, dir="+") - 1)
check_log_zero(
    "right terminal term tends to zero as h->0",
    sp.limit(2 * h_dom * gb_dom * Phi_dom, eta, 0, dir="+"),
)
check_zero(
    "right beta atom tends to zero as h->0",
    sp.limit(mb_R.subs(right_domain), eta, 0, dir="+"),
)


# ---------------------------------------------------------------------------
# Left compression: density/atoms, transform primitive, endpoint value.
# ---------------------------------------------------------------------------
alpha = sp.symbols("alpha", real=True)
Bz = (z + C) * (z - alpha) / (z - r)
Br = (r + C) * (r - alpha) / (r - z)
# For T_L=(alpha,a), chi_{alpha,b}*chi_{alpha,a}=(w-alpha)/Q_{a,b}.
# Again the squared identity plus normalization at infinity fixes the branch.
left_chi_square = (w - alpha) ** 2 / ((w - a) * (w - b))
left_Q_square = ((w - alpha) / Qw) ** 2
check_zero(
    "left compressed chi-product reduction",
    left_Q_square.subs(Qw**2, (w - a) * (w - b)) - left_chi_square,
)
S_L_w = (w + C) * (w - alpha) / ((w - z) * (w - r) * Qw)
S_L = S_L_w.subs({w: x, Qw: Q})
check_zero(
    "left transform partial fractions",
    (x + C) * (x - alpha) / ((x - z) * (x - r)) - 1 - Bz / (x - z) - Br / (x - r),
)
check_zero("left transform has mass one", sp.limit(x * S_L, y, sp.oo) - 1)

mz_L = -(z + C) * (z - alpha) / ((z - r) * qz)
mr_L = -(r + C) * (r - alpha) / ((r - z) * qr)
check_zero("left z atom equals residue", mz_L - branch_residue(S_L_w, z, -qz))
check_zero("left r atom equals residue", mr_L - branch_residue(S_L_w, r, -qr))

S_L_plus = S_L_w.subs({w: s, Qw: sp.I * qcut})
S_L_minus = S_L_w.subs({w: s, Qw: -sp.I * qcut})
# Definition 4.1 for T_L=(alpha,a) contains
# sqrt((s-alpha)/(b-s))*sqrt((s-alpha)/(s-a)); its product is
# (s-alpha)/qcut on a<s<b.
check_zero(
    "left compressed density square-root reduction",
    (s - alpha) ** 2 / ((s - a) * (b - s))
    - ((s - alpha) / (b - s)) * ((s - alpha) / (s - a)),
)
rho_L_from_jump = exact_reduce(-(S_L_plus - S_L_minus) / (2 * sp.pi * sp.I))
rho_L_manuscript = (s + C) * (s - alpha) / (sp.pi * (s - z) * (s - r) * qcut)
check_zero("left jump gives the manuscript density", rho_L_from_jump - rho_L_manuscript)

P_L = sp.log(y) + Bz * zdata.I + Br * rdata.I
check_zero("left assembled primitive derivative", sp.diff(P_L, y) / dx_dy - S_L)
check_zero("left z inverse-Q ratio tends to one", sp.limit(Rz, y, sp.oo) - 1)
check_zero("left r inverse-Q ratio tends to one", sp.limit(Rr, y, sp.oo) - 1)

Y0 = sp.symbols("Y0", positive=True)
x0 = m - d * (Y0 + 1 / Y0) / 2
q0 = d * (Y0 - 1 / Y0) / 2
check_zero(
    "left evaluation coordinate J_{a,b}(x0)=Y0",
    (a + b - 2 * x0 + 2 * q0) / (b - a) - Y0,
)

ratio_z_abs = (Yz - Y0) / (Y0 - 1 / Yz)
ratio_r_abs = (Y0 - Yr) / (Y0 - 1 / Yr)
check_zero(
    "left z-pole absolute endpoint ratio",
    Rz.subs(y, Y0) + ratio_z_abs,
)
check_zero(
    "left r-pole absolute endpoint ratio",
    Rr.subs(y, Y0) - ratio_r_abs,
)

P_L_at_x0 = sp.log(Y0) - Bz * sp.log(ratio_z_abs) / qz - Br * sp.log(ratio_r_abs) / qr
U_L_from_transform = -sp.log((b - a) / 4) - P_L_at_x0

# Split-log version follows directly from the normalized primitive.  The final
# product-log version is exactly (B.5), with no forced log expansion.
L_B5_split = (
    -sp.log((b - a) / 4)
    - sp.log(Y0)
    + (z + C) * (z - alpha) * sp.log(ratio_z_abs) / ((z - r) * qz)
    + (r + C) * (r - alpha) * sp.log(ratio_r_abs) / ((r - z) * qr)
)
check_zero("left normalized transform value equals split-log formula", U_L_from_transform - L_B5_split)

L_B5 = (
    -sp.log((b - a) * Y0 / 4)
    + (z + C) * (z - alpha) * sp.log(ratio_z_abs) / ((z - r) * qz)
    + (r + C) * (r - alpha) * sp.log(ratio_r_abs) / ((r - z) * qr)
)
left_log_domain = {b: a + 2 * d0}
check_log_zero(
    "Equation (B.6), left endpoint: transform potential equals L(r,h,C)",
    (U_L_from_transform - L_B5).subs(left_log_domain),
)


# ---------------------------------------------------------------------------
# Exact real-ordering and branch-domain checks.
# ---------------------------------------------------------------------------
# Encode Yz>Y0>Yr>1 by positive gaps.  These checks ensure that every
# logarithm argument used above is positive after taking the stated absolute
# value, and that the geometric ordering is z<x0<r<a.
e_r, e_0, e_z = sp.symbols("e_r e_0 e_z", positive=True)
ordered = {
    Yr: 1 + e_r,
    Y0: 1 + e_r + e_0,
    Yz: 1 + e_r + e_0 + e_z,
    b: a + 2 * d0,
}
posvars = (d0, e_r, e_0, e_z)

check_positive_rational("Yr-1", (Yr - 1).subs(ordered), posvars)
check_positive_rational("Y0-Yr", (Y0 - Yr).subs(ordered), posvars)
check_positive_rational("Yz-Y0", (Yz - Y0).subs(ordered), posvars)
check_positive_rational("left z absolute log ratio", ratio_z_abs.subs(ordered), posvars)
check_positive_rational("left r absolute log ratio", ratio_r_abs.subs(ordered), posvars)
check_positive_rational("x0-z", (x0 - z).subs(ordered), posvars)
check_positive_rational("r-x0", (r - x0).subs(ordered), posvars)
check_positive_rational("a-r", (a - r).subs(ordered), posvars)

# Encode 0<k<1 by k=1/(1+eta).  This also proves beta>b and 0<tau<1,
# justifying the real atanh/log identity used in the Phi reduction.
right_order = {b: a + 2 * d0, k: 1 / (1 + eta)}
right_posvars = (d0, eta)
check_positive_rational("k", k.subs(right_order), right_posvars)
check_positive_rational("1-k", (1 - k).subs(right_order), right_posvars)
check_positive_rational("beta-b", (beta - b).subs(right_order), right_posvars)
check_positive_rational("tau", tau.subs(right_order), right_posvars)
check_positive_rational("1-tau", (1 - tau).subs(right_order), right_posvars)
check_positive_rational("1+tau", (1 + tau).subs(right_order), right_posvars)
check_zero(
    "real atanh ratio (1+tau)/(1-tau)=1/k",
    ((1 + tau) / (1 - tau) - 1 / k).subs(right_order),
)


def main() -> None:
    print("PASS: strict symbolic endpoint verifier, including both identities in (B.6)")


if __name__ == "__main__":
    main()
