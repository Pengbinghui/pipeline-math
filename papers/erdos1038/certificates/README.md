# Certificates for Erdős Problem 1038

This directory contains the five proof scripts used by the accompanying LaTeX
manuscript, together with a driver that runs them in the required dependency
order.

## Environment

The interval-arithmetic certificates require Python 3.13 and
`python-flint` 0.8.0. They use 384-bit Arb precision by default. The exact
symbolic verifiers require SymPy 1.14.

## Proof scripts

* `contact_existence.py` implements the scalar intermediate-value proof in the
  parameter-triple appendix. It certifies the two contact-root face signs,
  encloses the unique roots `u(q)` and `v(q)` at the two endpoints of `I_*`,
  proves the opposite signs of `kappa`, and exports rigorous enclosures for
  `q,u,v,p,alpha,r,z,D`. These same enclosures are imported by the endpoint
  certificate, so there is no independent decimal handoff between the two
  interval computations.

* `erdos1038_forcing_exact.py` certifies precisely the numerical premises used
  in the left-endpoint lemma: positivity of `Gamma(ell,b)`, positivity of the
  three-atom comparison potential on `[0,1]`, positivity of the coefficient
  `1.395-b`, and separation of the two swept intervals. The duality and
  measure-counting argument that uses these premises is given in the
  manuscript.

* `erdos1038_exact_endpoint_certificate.py` certifies every strict inequality
  in the endpoint-computer lemma. It uses second-order automatic-differentiation
  jets, rational box subdivision, interval Taylor bounds, and rigorous tails
  for the series defining `Phi`. The rigorous enclosures of `alpha` and `D`
  are imported directly from `contact_existence.py`.

* `symbolic_endpoint_verifier.py` checks the exact algebraic and branch
  calculations used in the derivation of the two endpoint-potential formulas
  in (B.6). For each compressed interval, it verifies the compressed Cauchy
  transform, its residues and jump density, the mass-one asymptotic,
  differentiation and normalization of an explicit Joukowski primitive, the
  relevant real-domain and branch conventions, and the reduction of the
  resulting endpoint boundary expression to the displayed function
  `R(r,h,C)` or `L(r,h,C)`.

  The analytic identification of the primitive with
  [
  \int \operatorname{Log}(w-s),d\lambda(s)
  ]
  and hence with the logarithmic potential is supplied by the complex-analytic
  argument in the manuscript. The degenerate case `h=0` is obtained there by
  continuity. The script uses neither floating-point arithmetic nor symbolic
  integration.

* `symbolic_contact_verifier.py` constructs the literal `h=0` right-endpoint
  formula and verifies exactly that
  [
  \mathsf R(r,0,C)
  ================

  p\Lambda(q)
  +\frac{v(z+C)\Lambda(v)-u(r+C)\Lambda(u)}{D}.
  ]
  It also checks the Joukowski, square-root, and logarithmic simplifications
  used in this specialization, the exact left-right contact residual identity
  for the specialized expressions, the formula for `C(q,u,v)`, and the
  chain-rule reduction of the composite derivative to `K/(pD)`.


## Scope of the certificates

The three Arb programs certify the stated numerical inequalities using
outward-rounded interval arithmetic. The two SymPy programs certify the
explicit algebraic identities described above.

The measure-theoretic and complex-analytic steps connecting these identities
to logarithmic potentials—including differentiation under the integral,
identification of normalized primitives, and the continuity argument at
`h=0`—are proved in the manuscript rather than delegated to the symbolic
scripts.

The endpoint certificate imports parameter enclosures produced from the same
rational parameter box used by `contact_existence.py`. A complete verification
run should therefore use the driver below, which executes the scripts in the
required order.

## Running the bundle

Run all certificates with

```bash
python run_all_certificates.py
```

The driver sets the default Arb precision and `Phi` truncation length, runs the
five proof scripts in dependency order, creates a local `logs/` directory,
writes one combined standard-output and standard-error log per script, and
stops at the first failure. A successful complete run ends with

```text
PASS: all certificates
```

The scripts may also be run individually:

```bash
python contact_existence.py
ERDOS1038_ARB_BITS=384 python erdos1038_forcing_exact.py
ERDOS1038_ARB_BITS=384 \
  python erdos1038_exact_endpoint_certificate.py --workers 1
python symbolic_endpoint_verifier.py
python symbolic_contact_verifier.py
```
