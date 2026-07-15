# Verification bundle for Erdős Problem 1038

## Environment

The archived run used:

- Python 3.13.5
- `python-flint` 0.8.0
- SymPy 1.14.0
- Arb precision: 384 bits

Run everything with:

```bash
python run_all_certificates.py
```

Each program also runs independently. Every interval-certificate pass/fail decision is based on an outward-rounded Arb enclosure. The two symbolic programs use exact SymPy rational-function algebra and do not use floating-point arithmetic.

## Programs

### `contact_isolator.py`

Certifies:

- the Krawczyk image of the radius-`1e-30` box is strictly inside that box;
- the exact rational preconditioner is invertible;
- existence and uniqueness of the zero of `(F_R,F_L,K)` within the box;
- every inequality in Lemma 1.2;
- rigorous enclosures of `q_*`, `u_*`, `v_*`, `p_*`, `alpha`, `r_*`, `z_*`, and `D`.

### `erdos1038_forcing_exact.py`

Covers the complete forcing domain by rational boxes and certifies `Gamma(a,b)>0` and `U_{nu_{a,b}}(x)>0`, proving the strengthened left-endpoint input.

### `erdos1038_exact_endpoint_certificate.py`

Uses second-order Arb jets, interval Taylor bounds, and adaptive rational subdivision to certify all derivative and boundary inequalities in Lemma 5.1. It evaluates `Phi`, `Phi'`, and `Phi''` by a power series with rigorous analytic tail bounds.

### `symbolic_endpoint_verifier.py`

Exactly checks the algebra behind (B.4) and (B.5): Joukowski identities, partial fractions, derivatives of the proposed primitives, endpoint substitutions, and normalization at infinity. It never calls a symbolic integrator.

### `symbolic_contact_verifier.py`

Exactly checks the reductions used in Lemma B.1, including the specialized endpoint formulas, the residual identity, the logarithmic-ratio simplifications, and the reduction of the total derivative to `K/(pD)`.

The `logs/` directory contains the complete output of the archived run; each log ends in `PASS`.
