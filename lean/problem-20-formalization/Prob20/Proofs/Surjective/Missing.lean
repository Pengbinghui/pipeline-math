import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.Surjective.GMem
import Prob20.Proofs.KeyObs.Valuation

/-!
# Stage 4.2 — `theta2_missing` : `P = g(XY) ∈ Int(D²)` but `P ∉ im θ₂`

We prove `theta2_missing` (frozen in `Prob20/Theorems.lean`):

* **Conjunct 1** `PMv ∈ IntPolyN Dom Kt 2` : for every `d : Fin 2 → Dom`,
  `P(d₀, d₁) = g(d₀·d₁)`, and `d₀·d₁ : Dom`, so by `g_mem` the value lies in
  `ι(Dom)`. Quantified over all `d : Fin 2 → Dom` (no sampling).
* **Conjunct 2** `PMv ∉ Set.range (thetaN Dom Kt 2)` : the finite-difference /
  valuation argument (SKETCH *Failure of Surjectivity*).
-/

open scoped nonZeroDivisors TensorProduct

open Prob20 Prob20.Proofs.Domain Prob20.Proofs.KeyObs

namespace Prob20.Proofs.Surjective

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

open Polynomial MvPolynomial

/-! ## Conjunct 1 — `PMv ∈ IntPolyN Dom Kt 2` -/

/-- `P(d₀,d₁) = g(d₀·d₁)`: evaluating `PMv = g(X₀X₁)` at a point factors through the
univariate evaluation of `gPoly` at the product. -/
theorem eval_PMv (φ : Fin 2 → Kt) :
    MvPolynomial.eval φ PMv = Polynomial.aeval (φ 0 * φ 1) gPoly := by
  rw [show MvPolynomial.eval φ PMv = MvPolynomial.aeval φ PMv from
      (congrFun (MvPolynomial.aeval_eq_eval φ) PMv).symm]
  rw [PMv,
    ← Polynomial.aeval_algHom_apply (MvPolynomial.aeval φ) (MvPolynomial.X 0 * MvPolynomial.X 1) gPoly]
  congr 1
  simp

/-- **Conjunct 1.** `PMv ∈ IntPolyN Dom Kt 2`. -/
theorem theta2_missing_mem : PMv ∈ IntPolyN Dom Kt 2 := by
  intro d
  rw [eval_PMv]
  have hprod : algebraMap Dom Kt (d 0) * algebraMap Dom Kt (d 1)
      = algebraMap Dom Kt (d 0 * d 1) := by rw [map_mul]
  rw [hprod]
  exact g_mem_proof (d 0 * d 1)

/-! ## Conjunct 2 — the finite-difference functional

`Δ_a(F) = F(a,a) − F(a,0) − F(0,a) + F(0,0)`.  On a separated product
`F = f(X)·h(Y)` it telescopes to `(f(a)−f(0))·(h(a)−h(0))`; on `PMv = g(XY)` it
collapses to `g(a²) − g(0) = g(a²)`. -/

/-- The mixed second finite difference of a bivariate polynomial at the point `a`
(in both variables), against the base point `0`. -/
noncomputable def Delta (a : Kt) (F : MvPolynomial (Fin 2) Kt) : Kt :=
  MvPolynomial.eval ![a, a] F - MvPolynomial.eval ![a, 0] F
    - MvPolynomial.eval ![0, a] F + MvPolynomial.eval ![0, 0] F

/-- `g(0) = 0`. -/
theorem aeval0_gPoly : Polynomial.aeval (0 : Kt) gPoly = 0 := by
  simp [gPoly, qPoly, pPoly]

/-- `Δ_a(PMv) = g(a²)`. -/
theorem Delta_PMv (a : Kt) : Delta a PMv = Polynomial.aeval (a * a) gPoly := by
  rw [Delta]
  rw [eval_PMv ![a, a], eval_PMv ![a, 0], eval_PMv ![0, a], eval_PMv ![0, 0]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_mul, aeval0_gPoly]
  ring

/-! ### The special elements `u_N = π(t+1)^N`

`u_N ∈ 𝔪 ⊆ Dom` (it vanishes at both places), with image `π·(t+1)^N` in `Kt`. -/

/-- `u_N = π·(t+1)^N`, as an element of `Dom` (it lies in `𝔪`). -/
noncomputable def uN (N : ℕ) : Dom := ⟨piTsub * (tT + 1) ^ N, mul_piTsub_mem _⟩

/-- The image of `u_N` in `Kt` is `π·(t+1)^N`. -/
theorem uK_eq (N : ℕ) : algebraMap Dom Kt (uN N) = piElt * (tElt + 1) ^ N := by
  rw [domToKt_eq, uN]
  show ((piTsub * (tT + 1) ^ N : Tsub) : Kt) = piElt * (tElt + 1) ^ N
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_add, Subalgebra.coe_one,
    coe_tT, coe_piTsub]

/-! ### Place-0 computation : `g(u_N²) ∉ 𝔪²`

`g(u_N²) = π·A_N` with `A_N : T` and `res0 A_N = 1`.  If `g(u_N²) ∈ 𝔪² ⊆ π²T` then
cancelling one `π` would force `res0 A_N = 0`, a contradiction.  This is the
place-`t=0` valuation computation (the order of `g(u_N²)` at `t=0` is exactly `1`,
because `(t+1)^N` is a unit there). -/

/-- The cofactor `B_N = (t+1)^{2N}·(π²(t+1)^{2N}+1) : T`. -/
noncomputable def Bel (N : ℕ) : Tsub :=
  ((tT + 1) ^ N) ^ 2 * (piTsub ^ 2 * ((tT + 1) ^ N) ^ 2 + 1)

/-- The cofactor `A_N = B_N·(π·B_N + 1) : T`, so that `g(u_N²) = π·A_N`. -/
noncomputable def Ael (N : ℕ) : Tsub := Bel N * (piTsub * Bel N + 1)

theorem coe_Bel (N : ℕ) :
    (Bel N : Kt) = ((tElt + 1) ^ N) ^ 2 * (piElt ^ 2 * ((tElt + 1) ^ N) ^ 2 + 1) := by
  simp only [Bel, Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_pow,
    Subalgebra.coe_one, coe_tT, coe_piTsub]

theorem coe_Ael (N : ℕ) : (Ael N : Kt) = (Bel N : Kt) * (piElt * (Bel N : Kt) + 1) := by
  simp only [Ael, Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one, coe_piTsub]

/-- `res0 A_N = 1` : the value of the cofactor at the place `t = 0` is the unit `1`. -/
theorem res0_Ael (N : ℕ) : res0 (Ael N) = 1 := by
  have hc : res0 ((tT + 1) ^ N) = 1 := by
    rw [map_pow, map_add, map_one, res0_tT, zero_add, one_pow]
  have hB : res0 (Bel N) = 1 := by
    simp only [Bel, map_mul, map_add, map_pow, map_one, hc, res0_piTsub]
    ring
  simp only [Ael, map_mul, map_add, map_one, hB, res0_piTsub]
  ring

/-- The factorization `g(u_N²) = π·A_N`. -/
theorem g_usq_factor (N : ℕ) :
    Polynomial.aeval (algebraMap Dom Kt (uN N) * algebraMap Dom Kt (uN N)) gPoly
      = piElt * (Ael N : Kt) := by
  rw [coe_Ael, coe_Bel, uK_eq, gPoly, qPoly, pPoly]
  simp only [map_add, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_self_apply]
  have hpi : piElt ≠ 0 := piElt_ne_zero
  field_simp

/-- **Place-0 non-membership.** `g(u_N²) ∉ 𝔪²` for every `N`. -/
theorem g_usq_not_mem (N : ℕ) :
    ¬ ∃ w : Dom, w ∈ mIdeal * mIdeal ∧
      algebraMap Dom Kt w
        = Polynomial.aeval (algebraMap Dom Kt (uN N) * algebraMap Dom Kt (uN N)) gPoly := by
  rintro ⟨w, hw, hweq⟩
  obtain ⟨s, hs⟩ := m2_sub w hw
  -- `ι w = π² · s` in `Kt`
  have hwk : algebraMap Dom Kt w = piElt ^ 2 * (s : Kt) := by
    rw [domToKt_eq, hs, Subalgebra.coe_mul, Subalgebra.coe_pow, coe_piTsub]
  rw [g_usq_factor, hwk] at hweq
  -- cancel one `π`: `π · A_N = π · (π · s)`
  have hpi : piElt ≠ 0 := piElt_ne_zero
  have hcancel : (Ael N : Kt) = piElt * (s : Kt) :=
    mul_left_cancel₀ hpi (by linear_combination -hweq)
  -- transfer to `Tsub` and apply `res0`
  have hTsub : Ael N = piTsub * s := by
    apply Subtype.val_injective
    simp only [Subalgebra.coe_mul, coe_piTsub]
    rw [hcancel]
  have := congrArg res0 hTsub
  rw [res0_Ael, map_mul, res0_piTsub, zero_mul] at this
  exact absurd this (by decide)

/-! ## Conjunct 2 — the tensor / finite-difference reduction

The image of `θ₂` is spanned by separated products `f(X₀)·h(X₁)`.  Applying the
finite-difference functional `Δ_a` to such a product telescopes to
`(f(a)−f(0))·(h(a)−h(0))`.  With `a = u_N` and `N` large, each factor lies in `𝔪`
(this is the **crux lemma `KEY`**, discharged unconditionally by `KEY_proof` in
`Place1.lean`), so `Δ_{u_N}(θ₂ τ) ∈ 𝔪²`
for every `τ`.  But `Δ_{u_N}(P) = g(u_N²) ∉ 𝔪²` (place-0 computation above) —
contradiction. -/

/-- `Δ` is additive in the polynomial argument. -/
theorem Delta_add (a : Kt) (F G : MvPolynomial (Fin 2) Kt) :
    Delta a (F + G) = Delta a F + Delta a G := by
  simp only [Delta, map_add]; ring

/-- `Δ` is `Dom`-semilinear in the polynomial argument: scaling by `r : Dom` pulls
out the scalar `ι r`. -/
theorem Delta_smul (a : Kt) (r : Dom) (F : MvPolynomial (Fin 2) Kt) :
    Delta a (r • F) = algebraMap Dom Kt r * Delta a F := by
  rw [show (r • F) = (algebraMap Dom Kt r) • F from (algebraMap_smul Kt r F).symm]
  simp only [Delta, MvPolynomial.smul_eval]; ring

/-- `incl i f = f(Xᵢ)`. -/
theorem incl_apply (i : Fin 2) (f : ↥(IntPoly Dom Kt)) :
    incl Dom Kt 2 i f = Polynomial.aeval (MvPolynomial.X i) (f : Polynomial Kt) := rfl

/-- `θ₂` on a pure tensor is the separated product `∏ᵢ (m i)(Xᵢ)`. -/
theorem thetaMul_apply (m : Fin 2 → ↥(IntPoly Dom Kt)) :
    thetaMul Dom Kt 2 m
      = ∏ i : Fin 2, Polynomial.aeval (MvPolynomial.X i) ((m i : Polynomial Kt)) := by
  simp only [thetaMul, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    AlgHom.toLinearMap_apply, incl_apply]

/-- Evaluating `aeval (Xᵢ) p` at `φ` substitutes `φ i` for `X`. -/
theorem eval_aeval_X (φ : Fin 2 → Kt) (i : Fin 2) (p : Polynomial Kt) :
    MvPolynomial.eval φ (Polynomial.aeval (MvPolynomial.X i) p) = Polynomial.aeval (φ i) p := by
  rw [show MvPolynomial.eval φ (Polynomial.aeval (MvPolynomial.X i) p)
      = MvPolynomial.aeval φ (Polynomial.aeval (MvPolynomial.X i) p) from
      congrFun (MvPolynomial.aeval_eq_eval φ) _]
  rw [← Polynomial.aeval_algHom_apply]
  simp

/-- `eval φ` of the separated product. -/
theorem eval_thetaMul (φ : Fin 2 → Kt) (m : Fin 2 → ↥(IntPoly Dom Kt)) :
    MvPolynomial.eval φ (thetaMul Dom Kt 2 m)
      = Polynomial.aeval (φ 0) ((m 0 : Polynomial Kt))
        * Polynomial.aeval (φ 1) ((m 1 : Polynomial Kt)) := by
  rw [thetaMul_apply, map_prod, Fin.prod_univ_two, eval_aeval_X, eval_aeval_X]

/-- **The telescoping identity.** `Δ_a(f(X)h(Y)) = (f(a)−f(0))·(h(a)−h(0))`. -/
theorem Delta_thetaMul (a : Kt) (m : Fin 2 → ↥(IntPoly Dom Kt)) :
    Delta a (thetaMul Dom Kt 2 m)
      = (Polynomial.aeval a ((m 0 : Polynomial Kt)) - Polynomial.aeval (0 : Kt) ((m 0 : Polynomial Kt)))
        * (Polynomial.aeval a ((m 1 : Polynomial Kt)) - Polynomial.aeval (0 : Kt) ((m 1 : Polynomial Kt))) := by
  simp only [Delta, eval_thetaMul, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `θ₂` on a pure tensor equals the separated product. -/
theorem thetaN_tprod (m : Fin 2 → ↥(IntPoly Dom Kt)) :
    thetaN Dom Kt 2 (PiTensorProduct.tprod Dom m) = thetaMul Dom Kt 2 m := by
  rw [thetaN, PiTensorProduct.lift.tprod]

/-- `θ₂` is additive. -/
theorem thetaN_add (x y : ⨂[Dom] (_ : Fin 2), IntPoly Dom Kt) :
    thetaN Dom Kt 2 (x + y) = thetaN Dom Kt 2 x + thetaN Dom Kt 2 y :=
  map_add _ _ _

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **The tensor reduction (conditional on `KEY`).** For every `τ`, the finite
difference `Δ_{u_N}(θ₂ τ)` lies in `ι(𝔪²)` once `N` is large enough.  The crux
hypothesis `KEY` (`f(u_N) − f(0) ∈ 𝔪` for `N` large) is the only input. -/
theorem tensor_Delta_eventually
    (hKEY : ∀ f : ↥(IntPoly Dom Kt), ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        ∃ w : Dom, w ∈ mIdeal ∧ algebraMap Dom Kt w
          = Polynomial.aeval (algebraMap Dom Kt (uN N)) ((f : Polynomial Kt))
              - Polynomial.aeval (0 : Kt) ((f : Polynomial Kt)))
    (τ : ⨂[Dom] (_ : Fin 2), IntPoly Dom Kt) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ w : Dom, w ∈ mIdeal * mIdeal ∧
      algebraMap Dom Kt w = Delta (algebraMap Dom Kt (uN N)) (thetaN Dom Kt 2 τ) := by
  induction τ using PiTensorProduct.induction_on' with
  | tprodCoeff r m =>
      obtain ⟨N0, hN0⟩ := hKEY (m 0)
      obtain ⟨N1, hN1⟩ := hKEY (m 1)
      refine ⟨max N0 N1, fun N hN => ?_⟩
      obtain ⟨w0, hw0, hw0eq⟩ := hN0 N (le_trans (le_max_left _ _) hN)
      obtain ⟨w1, hw1, hw1eq⟩ := hN1 N (le_trans (le_max_right _ _) hN)
      refine ⟨r * (w0 * w1), Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hw0 hw1), ?_⟩
      show algebraMap Dom Kt (r * (w0 * w1))
          = Delta (algebraMap Dom Kt (uN N)) (r • thetaMul Dom Kt 2 m)
      rw [Delta_smul, Delta_thetaMul, ← hw0eq, ← hw1eq, map_mul, map_mul]
  | add x y hx hy =>
      obtain ⟨Nx, hNx⟩ := hx
      obtain ⟨Ny, hNy⟩ := hy
      refine ⟨max Nx Ny, fun N hN => ?_⟩
      obtain ⟨wx, hwx, hwxeq⟩ := hNx N (le_trans (le_max_left _ _) hN)
      obtain ⟨wy, hwy, hwyeq⟩ := hNy N (le_trans (le_max_right _ _) hN)
      refine ⟨wx + wy, Ideal.add_mem _ hwx hwy, ?_⟩
      rw [thetaN_add, Delta_add, ← hwxeq, ← hwyeq, map_add]

/-- **Conjunct 2 (conditional on `KEY`).** `PMv ∉ Set.range (θ₂)`. -/
theorem theta2_missing_not_range
    (hKEY : ∀ f : ↥(IntPoly Dom Kt), ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        ∃ w : Dom, w ∈ mIdeal ∧ algebraMap Dom Kt w
          = Polynomial.aeval (algebraMap Dom Kt (uN N)) ((f : Polynomial Kt))
              - Polynomial.aeval (0 : Kt) ((f : Polynomial Kt))) :
    PMv ∉ Set.range (thetaN Dom Kt 2) := by
  rintro ⟨τ, hτ⟩
  obtain ⟨N₀, hN₀⟩ := tensor_Delta_eventually hKEY τ
  obtain ⟨w, hw, hweq⟩ := hN₀ N₀ (le_refl N₀)
  rw [hτ, Delta_PMv] at hweq
  exact g_usq_not_mem N₀ ⟨w, hw, hweq⟩

/-!
### The crux lemma `KEY` (discharged in `Place1.lean`)

`theta2_missing` is reduced here (sorry-free, clean axioms) to the hypothesis

> `KEY : ∀ f ∈ Int(D), ∃ N₀, ∀ N ≥ N₀, f(u_N) − f(0) ∈ 𝔪`     (with `u_N = π(t+1)^N`).

**Why `KEY` is true and (unlike the Stage-2.2 lemma `L`) elementary here.**
For `f ∈ Int(D)`, both `f(u_N)` and `f(0)` lie in `D` (as `u_N, 0 ∈ D`), so their
difference `d_N := f(u_N) − f(0)` lies in `D`, whence `res0 d_N = res1 d_N`.  It
therefore suffices to show `res1 d_N = 0` for `N` large.  Writing `f.val = Σ cₖ Xᵏ`,
`d_N = Σ_{k≥1} cₖ (π(t+1)^N)ᵏ`, and at the place `t = 1` the factor `(t+1)^N` has
order `N`; choosing `N` larger than the (place-`t=1`) pole orders of the finitely
many coefficients `cₖ` forces `v₁(d_N) ≥ 1`, i.e. `(t+1) ∣ d_N` in `T`, i.e.
`res1 d_N = res1(t+1)·res1(d_N/(t+1)) = 0`.  Then `res0 d_N = res1 d_N = 0`, so
`d_N ∈ 𝔪`.

This is **strictly more tractable than the Stage-2.2 lemma `L`**: `L` is at the
*fixed* order-`1` element `π` (needing genuine two-place reduction-compatibility),
whereas `KEY` lets `N → ∞`, so a *one-place* (place-`t=1`) pole-killing estimate
plus the `D`-equalizer transfer `res0 = res1` suffices — no compatibility lemma.

**Status: discharged.**  `KEY` is proved unconditionally as `KEY_proof` in
`Place1.lean` (the place-`t=1` valuation / pole-order argument sketched above), so
`theta2_missing_proof := theta2_missing_of_KEY KEY_proof` (`Place1.lean`) is the
frozen statement — no remaining gap.
-/

/-- **`theta2_missing`, conditional on the crux lemma `KEY`.**  This is the full
frozen statement, modulo `KEY` — which is supplied unconditionally by `KEY_proof`
in `Place1.lean`, so the composed `theta2_missing_proof` there is unconditional. -/
theorem theta2_missing_of_KEY
    (hKEY : ∀ f : ↥(IntPoly Dom Kt), ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        ∃ w : Dom, w ∈ mIdeal ∧ algebraMap Dom Kt w
          = Polynomial.aeval (algebraMap Dom Kt (uN N)) ((f : Polynomial Kt))
              - Polynomial.aeval (0 : Kt) ((f : Polynomial Kt))) :
    PMv ∈ IntPolyN Dom Kt 2 ∧ PMv ∉ Set.range (thetaN Dom Kt 2) :=
  ⟨theta2_missing_mem, theta2_missing_not_range hKEY⟩

end Prob20.Proofs.Surjective
