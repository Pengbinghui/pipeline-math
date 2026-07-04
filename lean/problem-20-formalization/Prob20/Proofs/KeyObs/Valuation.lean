import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.Domain.FractionField
import Prob20.Proofs.KeyObs.KeyMembership

/-!
# Stage 2.2 helpers — the place-order / valuation infrastructure (`KeyObs/Valuation.lean`)

This file supports `LinIndep.lean` by providing, **`sorry`-free**:

* `m_sub` : the structural fact `𝔪 ⊆ πT` — every `a ∈ mIdeal` is `π · s` for some
  `s : Tsub` (a polynomial-divisibility computation: `res0 a = res1 a = 0` force
  both `t` and `t+1` to divide a numerator of `a`, hence `π = t(t+1) ∣ a`).
* `m2_sub` : consequently `𝔪² ⊆ π²T`.
* the divided-difference functional reduction `p_tp_linindep_of_L`, which derives
  the three non-memberships `p, tp, (t+1)p ∉ 𝔪·Int(D)` (hence the frozen joint
  independence) **from the single crux hypothesis `L`**:

  > `L : ∀ g ∈ Int(D), g(π) − g(0) ∈ ι(𝔪)`   (i.e. `resD (g(π)) = resD (g(0))`).

  `L` is the crux fact: its single-place analogue is *false* (the `(X²+X)/t`
  binomial obstruction), so it needs the two-place fixed-divisor structure.  Here
  we reduce *everything else* to `L`; `L` itself is discharged unconditionally as
  `L_proof` in `CruxL.lean` (a two-place CRT / divisibility argument).

The reduction: from a representation `p = Σ mᵢ·fᵢ ∈ 𝔪·Int(D)`, evaluating at
`π` and `0` and subtracting gives `δ(p) := p(π) − p(0) ∈ ι(𝔪²)` (via
`Submodule.smul_induction_on`, using `L` at the base case `δ(m·f) = ι m · δ f`).
But `δ(p) = π²+π`, `δ(tp) = t(π²+π)`, `δ((t+1)p) = (t+1)(π²+π)` are each **not**
in `ι(𝔪²) ⊆ π²T`, detected by `res0`/`res1` after cancelling one factor of `π`.
-/

open scoped nonZeroDivisors

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Prob20.Proofs.KeyObs

open Prob20 Polynomial
open Prob20.Proofs.Domain

/-- **`𝔪 ⊆ πT`.** Every `a ∈ mIdeal` factors as `π · s` with `s : Tsub`.
Because `res0 a = res1 a = 0`, a numerator of `a` (over `𝔽₂[t]`) vanishes at both
`t = 0` and `t = 1`, so is divisible by `t` and `t+1`, hence by `π = t(t+1)`. -/
theorem m_sub (a : Dom) (ha : a ∈ mIdeal) :
    ∃ s : Tsub, (a : Tsub) = piTsub * s := by
  -- the two residues of `a` vanish
  have h0 : res0 (a : Tsub) = 0 := RingHom.mem_ker.mp ha
  have h1 : res1 (a : Tsub) = 0 := a.2.symm.trans h0
  -- a localization representation `a = num / den`, `den ∈ Sset`
  obtain ⟨⟨num, den⟩, hrep⟩ := IsLocalization.surj (M := Sset) (a : Tsub)
  simp only at hrep
  -- `hrep : (a:Tsub) * algebraMap _ _ den = algebraMap _ _ num`
  have hden_unit : IsUnit (algebraMap (Polynomial (ZMod 2)) Tsub (den : Polynomial (ZMod 2))) :=
    IsLocalization.map_units Tsub den
  -- apply `res0`, `res1` to the representation; `resᵢ (algebraMap p) = evalᵢ p`
  have e0 : eval0 num = 0 := by
    have h := congrArg res0 hrep
    rw [map_mul,
      show res0 (algebraMap (Polynomial (ZMod 2)) Tsub num) = eval0 num from
        IsLocalization.lift_eq hu0 num,
      show res0 (algebraMap (Polynomial (ZMod 2)) Tsub (den : Polynomial (ZMod 2)))
          = eval0 (den : Polynomial (ZMod 2)) from IsLocalization.lift_eq hu0 _,
      h0, zero_mul] at h
    exact h.symm
  have e1 : eval1 num = 0 := by
    have h := congrArg res1 hrep
    rw [map_mul,
      show res1 (algebraMap (Polynomial (ZMod 2)) Tsub num) = eval1 num from
        IsLocalization.lift_eq hu1 num,
      show res1 (algebraMap (Polynomial (ZMod 2)) Tsub (den : Polynomial (ZMod 2)))
          = eval1 (den : Polynomial (ZMod 2)) from IsLocalization.lift_eq hu1 _,
      h1, zero_mul] at h
    exact h.symm
  -- hence `X ∣ num` and `X+1 ∣ num`
  have hX : (Polynomial.X : Polynomial (ZMod 2)) ∣ num := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    simpa [eval0] using e0
  have hX1 : (Polynomial.X + 1 : Polynomial (ZMod 2)) ∣ num := by
    have hroot : num.IsRoot 1 := by
      show Polynomial.eval 1 num = 0
      simpa [eval1] using e1
    have hdvd : (Polynomial.X - Polynomial.C (1 : ZMod 2)) ∣ num :=
      (Polynomial.dvd_iff_isRoot).mpr hroot
    rwa [show (Polynomial.X - Polynomial.C (1 : ZMod 2))
          = (Polynomial.X + 1 : Polynomial (ZMod 2)) by
        rw [CharTwo.sub_eq_add, Polynomial.C_1]] at hdvd
  -- coprimality gives `X(X+1) ∣ num`
  have hcop : IsCoprime (Polynomial.X : Polynomial (ZMod 2)) (Polynomial.X + 1) := by
    have h := Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (R := ZMod 2) (a := 0) (b := 1)
      (by rw [show ((0 : ZMod 2) - 1) = 1 by decide]; exact isUnit_one)
    rwa [show (Polynomial.X - Polynomial.C (0 : ZMod 2)) = (Polynomial.X : Polynomial (ZMod 2)) by
          rw [Polynomial.C_0, sub_zero],
        show (Polynomial.X - Polynomial.C (1 : ZMod 2)) = (Polynomial.X + 1 : Polynomial (ZMod 2)) by
          rw [CharTwo.sub_eq_add, Polynomial.C_1]] at h
  obtain ⟨c, hc⟩ := hcop.mul_dvd hX hX1
  -- now `num = X(X+1)·c`, so `a · algebraMap den = piTsub · algebraMap c`
  set u := hden_unit.unit with hu_def
  refine ⟨(↑u⁻¹ : Tsub) * algebraMap (Polynomial (ZMod 2)) Tsub c, ?_⟩
  have key : (a : Tsub) * algebraMap (Polynomial (ZMod 2)) Tsub (den : Polynomial (ZMod 2))
      = piTsub * algebraMap (Polynomial (ZMod 2)) Tsub c := by
    rw [hrep, hc]
    rw [show (Polynomial.X * (Polynomial.X + 1) * c : Polynomial (ZMod 2))
          = (Polynomial.X * (Polynomial.X + 1)) * c by ring, map_mul]
    rfl
  -- cancel the unit `algebraMap den`
  have hu : (algebraMap (Polynomial (ZMod 2)) Tsub (den : Polynomial (ZMod 2)))
      = (u : Tsub) := rfl
  have h2 : (a : Tsub) * (u : Tsub) = piTsub * algebraMap (Polynomial (ZMod 2)) Tsub c := by
    rw [← hu]; exact key
  have hinv : (a : Tsub)
      = (piTsub * algebraMap (Polynomial (ZMod 2)) Tsub c) * (↑u⁻¹ : Tsub) := by
    calc (a : Tsub) = (a : Tsub) * ((u : Tsub) * (↑u⁻¹ : Tsub)) := by
            rw [Units.mul_inv, mul_one]
      _ = ((a : Tsub) * (u : Tsub)) * (↑u⁻¹ : Tsub) := by ring
      _ = (piTsub * algebraMap (Polynomial (ZMod 2)) Tsub c) * (↑u⁻¹ : Tsub) := by rw [h2]
  rw [hinv]; ring

/-- **`𝔪² ⊆ π²T`.** Every `w ∈ mIdeal * mIdeal` factors as `π² · s`, `s : Tsub`. -/
theorem m2_sub (w : Dom) (hw : w ∈ mIdeal * mIdeal) :
    ∃ s : Tsub, (w : Tsub) = piTsub ^ 2 * s := by
  refine Submodule.mul_induction_on hw ?_ ?_
  · intro a ha b hb
    obtain ⟨sa, hsa⟩ := m_sub a ha
    obtain ⟨sb, hsb⟩ := m_sub b hb
    refine ⟨sa * sb, ?_⟩
    have hcoe : ((a * b : Dom) : Tsub) = (a : Tsub) * (b : Tsub) := rfl
    rw [hcoe, hsa, hsb]; ring
  · rintro x y ⟨sx, hsx⟩ ⟨sy, hsy⟩
    refine ⟨sx + sy, ?_⟩
    have hcoe : ((x + y : Dom) : Tsub) = (x : Tsub) + (y : Tsub) := rfl
    rw [hcoe, hsx, hsy]; ring

/-! ### The element `π` as a `Dom`/`Kt` value, and the `t`-residues -/

/-- `π = t(t+1)` as an element of `Dom`. -/
noncomputable def piD : Dom := ⟨piTsub, by simpa using mul_piTsub_mem 1⟩

/-- `π` viewed in `Kt`. -/
noncomputable def piK : Kt := algebraMap Dom Kt piD

theorem piK_eq : piK = (piTsub : Kt) := rfl

theorem piK_ne_zero : piK ≠ 0 := by
  rw [piK_eq]
  intro h
  exact piTsub_ne_zero (Subtype.val_injective (by rw [h]; simp))

/-- `tT = algebraMap 𝔽₂[t] T (X)`. -/
theorem tT_eq : tT = algebraMap (Polynomial (ZMod 2)) Tsub Polynomial.X := by
  apply Subtype.val_injective
  show (tElt : Kt) = ((algebraMap (Polynomial (ZMod 2)) Tsub Polynomial.X : Tsub) : Kt)
  rw [tElt, ← RatFunc.algebraMap_X (K := ZMod 2)]
  exact (IsScalarTower.algebraMap_apply (Polynomial (ZMod 2)) Tsub Kt Polynomial.X)

theorem res0_tT : res0 tT = 0 := by
  rw [tT_eq, show res0 (algebraMap (Polynomial (ZMod 2)) Tsub Polynomial.X)
        = eval0 Polynomial.X from IsLocalization.lift_eq hu0 _]
  simp [eval0]

theorem res1_tT : res1 tT = 1 := by
  rw [tT_eq, show res1 (algebraMap (Polynomial (ZMod 2)) Tsub Polynomial.X)
        = eval1 Polynomial.X from IsLocalization.lift_eq hu1 _]
  simp [eval1]

/-! ### The divided-difference engine (the crux `L` enters here as a hypothesis) -/

/-- **`core`.** From a representation of `h ∈ 𝔪·Int(D)`, the divided difference
`h(π) − h(0)` lies in `ι(𝔪²)` — **given the crux lemma `L`** (here a hypothesis
`hL`).  Proved by `Submodule.smul_induction_on`: the base case `δ(m·f) = ιm · δf`
with `δf ∈ ι(𝔪)` (by `L`) lands in `ι(𝔪·𝔪) = ι(𝔪²)`. -/
theorem core (h : Polynomial Kt)
    (hL : ∀ n : ↥(IntPoly Dom Kt), ∃ w : Dom, w ∈ mIdeal ∧
        algebraMap Dom Kt w =
          Polynomial.aeval piK (n : Polynomial Kt) - Polynomial.aeval (0 : Kt) (n : Polynomial Kt))
    (hmem : h ∈ mIntPoly) :
    ∃ w : Dom, w ∈ mIdeal * mIdeal ∧
      algebraMap Dom Kt w = Polynomial.aeval piK h - Polynomial.aeval (0 : Kt) h := by
  rw [mIntPoly, Submodule.mem_map] at hmem
  obtain ⟨y, hy, hyh⟩ := hmem
  have hyval : (y : Polynomial Kt) = h := hyh
  have hP : ∃ w : Dom, w ∈ mIdeal * mIdeal ∧
      algebraMap Dom Kt w =
        Polynomial.aeval piK (y : Polynomial Kt) - Polynomial.aeval (0 : Kt) (y : Polynomial Kt) := by
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro m hm n hn
      obtain ⟨wn, hwn_mem, hwn⟩ := hL n
      refine ⟨m * wn, Ideal.mul_mem_mul hm hwn_mem, ?_⟩
      have hscal : ((m • n : ↥(IntPoly Dom Kt)) : Polynomial Kt)
          = Polynomial.C (algebraMap Dom Kt m) * (n : Polynomial Kt) := by
        rw [Algebra.smul_def]; rfl
      rw [hscal]
      simp only [map_mul, Polynomial.aeval_C, Algebra.algebraMap_self_apply]
      rw [← mul_sub, ← hwn]
    · rintro x z ⟨wx, hwx, hwxeq⟩ ⟨wz, hwz, hwzeq⟩
      refine ⟨wx + wz, Ideal.add_mem _ hwx hwz, ?_⟩
      have hadd : ((x + z : ↥(IntPoly Dom Kt)) : Polynomial Kt)
          = (x : Polynomial Kt) + (z : Polynomial Kt) := by
        rw [AddMemClass.coe_add]
      rw [map_add, hadd, map_add, map_add, hwxeq, hwzeq]
      ring
  obtain ⟨w, hw, hweq⟩ := hP
  exact ⟨w, hw, by rw [hweq, hyval]⟩

/-- **`sep`** (the valuation detector).  If `ι w = (c:Kt)·π·(π+1)` with `w ∈ 𝔪²`
and a place `res` with `res π = 0`, `res c = 1`, this is impossible: cancelling one
`π` and applying `res` gives `0 = 1`. -/
theorem sep (c : Tsub) (res : Tsub →+* ZMod 2) (hpi : res piTsub = 0) (hc : res c = 1)
    (w : Dom) (hw : w ∈ mIdeal * mIdeal)
    (heq : algebraMap Dom Kt w = (c : Kt) * piK * (piK + 1)) : False := by
  obtain ⟨s, hs⟩ := m2_sub w hw
  have hwk : algebraMap Dom Kt w = piK ^ 2 * (s : Kt) := by
    rw [domToKt_eq, hs]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
    rw [piK_eq]
  rw [hwk] at heq
  have hcancel : piK * (s : Kt) = (c : Kt) * (piK + 1) :=
    mul_left_cancel₀ piK_ne_zero (by linear_combination heq)
  have htsub : piTsub * s = c * (piTsub + 1) := by
    apply Subtype.val_injective
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one]
    rw [← piK_eq]
    linear_combination hcancel
  have hres := congrArg res htsub
  rw [map_mul, map_mul, map_add, map_one, hpi, hc] at hres
  simp only [zero_mul, one_mul, zero_add] at hres
  exact absurd hres (by decide)

/-- **The three non-memberships, conditional on `L`.**  Each of `p, tp, (t+1)p`
has divided difference `c·π·(π+1)` with `c ∈ {1, t, t+1}`, none of which lies in
`ι(𝔪²)` (detected by `res0` for `p, (t+1)p` and `res1` for `tp`). -/
theorem three_not_mem_of_L
    (hL : ∀ n : ↥(IntPoly Dom Kt), ∃ w : Dom, w ∈ mIdeal ∧
        algebraMap Dom Kt w =
          Polynomial.aeval piK (n : Polynomial Kt) - Polynomial.aeval (0 : Kt) (n : Polynomial Kt)) :
    pPoly ∉ mIntPoly ∧ tpPoly ∉ mIntPoly ∧ t1pPoly ∉ mIntPoly := by
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨w, hw, hweq⟩ := core pPoly hL hmem
    refine sep 1 res0 res0_piTsub (map_one res0) w hw ?_
    rw [hweq]
    simp only [pPoly, map_add, map_pow, Polynomial.aeval_X, Subalgebra.coe_one]
    ring
  · intro hmem
    obtain ⟨w, hw, hweq⟩ := core tpPoly hL hmem
    refine sep tT res1 res1_piTsub res1_tT w hw ?_
    rw [hweq]
    simp only [tpPoly, pPoly, map_mul, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply, coe_tT]
    ring
  · intro hmem
    obtain ⟨w, hw, hweq⟩ := core t1pPoly hL hmem
    refine sep (tT + 1) res0 res0_piTsub (by rw [map_add, res0_tT, map_one, zero_add]) w hw ?_
    rw [hweq]
    simp only [t1pPoly, pPoly, map_mul, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply, Subalgebra.coe_add, Subalgebra.coe_one, coe_tT]
    ring

end Prob20.Proofs.KeyObs
