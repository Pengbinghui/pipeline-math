import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.KeyObs.Valuation
import Prob20.Proofs.KeyObs.CruxL

/-!
# Stage 2.2 — `p_tp_linindep` : `𝔽₂`-independence of `p̄, t̄p̄` in `Int(D)/𝔪·Int(D)`

The frozen statement (`Prob20.p_tp_linindep`) is the **joint** `𝔽₂`-linear
independence: any `𝔽₂`-combination `a·p + b·tp` that lands in `𝔪·Int(D)` forces
`a = b = 0`.

## What this file contains (sorry-free)

* `combo a b` — the frozen combination `C (ι a) · p + C (ι b) · tp`.
* The char-2 algebra reducing the four values of `(a, b) : (ZMod 2)²` to the three
  explicit polynomials:
  `combo 0 0 = 0`, `combo 1 0 = pPoly`, `combo 0 1 = tpPoly`,
  `combo 1 1 = t1pPoly` (`= (t+1)p`).
* `p_tp_linindep_of_not_mem` — the **reduction lemma**: the frozen statement
  follows from the three non-memberships
  `pPoly ∉ mIntPoly`, `tpPoly ∉ mIntPoly`, `t1pPoly ∉ mIntPoly`
  (plus `0 ∈ mIntPoly`, which holds for any submodule).

## Status (iter4): COMPLETE — `p_tp_linindep_proof` is sorry-free

The crux lemma `L` is now proved **unconditionally** in `KeyObs/CruxL.lean`
(`Prob20.Proofs.KeyObs.L_proof`), so `p_tp_linindep_proof` (at the end of this
file) discharges the frozen `Prob20.p_tp_linindep` via `p_tp_linindep_of_L
L_proof`.  The reduction below records how it follows from the crux lemma `hL`:

> `L : ∀ g ∈ Int(D), g(π) − g(0) ∈ ι(𝔪)`  (i.e. `resD (g(π)) = resD (g(0))`).

Everything else is `sorry`-free in `KeyObs/Valuation.lean`:

* `m_sub`/`m2_sub` : `𝔪 ⊆ πT` and `𝔪² ⊆ π²T` (polynomial-divisibility detector);
* `core` : the divided-difference engine — from `h ∈ 𝔪·Int(D)`,
  `h(π) − h(0) ∈ ι(𝔪²)` (via `Submodule.smul_induction_on`, base case
  `δ(m·f) = ιm·δf ∈ ι(𝔪·𝔪)` using `L`);
* `sep` : the place detector — `c·π·(π+1) ∉ ι(𝔪²)` for `c ∈ {1, t, t+1}`
  (`res0`/`res1` give `0 = 1` after cancelling one `π`);
* `three_not_mem_of_L` : the three non-memberships `p, tp, (t+1)p ∉ 𝔪·Int(D)`.

Everything is therefore reduced to the single fact `L`.  `L` is *true*
for this two-place pullback `D` but its single-place analogue is *false* (the
`(X²+X)/t` binomial obstruction: it is integer-valued at one place yet `g(π) ∉ D`
fails the other place), so its proof needs the fixed-divisor / two-place structure.
`L` is discharged unconditionally as `L_proof` in `CruxL.lean`, and
`p_tp_linindep_proof := p_tp_linindep_of_L L_proof` closes the frozen theorem.
-/

namespace Prob20.Proofs.KeyObs

open Prob20 Polynomial

/-- The frozen `𝔽₂`-combination `C (ι a) · p + C (ι b) · tp` of `p` and `tp`. -/
noncomputable def combo (a b : ZMod 2) : Polynomial Kt :=
  Polynomial.C (algebraMap (ZMod 2) Kt a) * pPoly
    + Polynomial.C (algebraMap (ZMod 2) Kt b) * tpPoly

theorem combo_zero_zero : combo 0 0 = 0 := by
  simp [combo]

theorem combo_one_zero : combo 1 0 = pPoly := by
  simp [combo]

theorem combo_zero_one : combo 0 1 = tpPoly := by
  simp [combo]

/-- `combo 1 1 = (t+1)·p = t1pPoly`: in characteristic two,
`p + t·p = (1 + t)·p = (t + 1)·p`. -/
theorem combo_one_one : combo 1 1 = t1pPoly := by
  simp only [combo, map_one, one_mul, tpPoly, t1pPoly]
  rw [Polynomial.C_add, Polynomial.C_1, add_mul, one_mul, add_comm]

/-- **Reduction lemma.**  The frozen joint `𝔽₂`-independence statement
`p_tp_linindep` follows from the three non-membership facts
`p, tp, (t+1)p ∉ 𝔪·Int(D)`.  (`0 ∈ mIntPoly` for free, being a submodule.)

This isolates the genuine content — the "valuation argument" — into the three
hypotheses, which a follow-up agent must supply (see the module docstring and the
`PROGRESS.md ⚠️` entry). -/
theorem p_tp_linindep_of_not_mem
    (hp : pPoly ∉ mIntPoly) (htp : tpPoly ∉ mIntPoly) (ht1p : t1pPoly ∉ mIntPoly) :
    ∀ a b : ZMod 2,
      Polynomial.C (algebraMap (ZMod 2) Kt a) * pPoly
        + Polynomial.C (algebraMap (ZMod 2) Kt b) * tpPoly ∈ mIntPoly →
      a = 0 ∧ b = 0 := by
  intro a b hmem
  -- `hmem` says `combo a b ∈ mIntPoly`.
  have hmem' : combo a b ∈ mIntPoly := hmem
  -- Every element of `ZMod 2` is `0` or `1`.
  have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcase a with rfl | rfl <;> rcases hcase b with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [combo_zero_one] at hmem'; exact absurd hmem' htp
  · rw [combo_one_zero] at hmem'; exact absurd hmem' hp
  · rw [combo_one_one] at hmem'; exact absurd hmem' ht1p

/-- **The frozen joint `𝔽₂`-independence, reduced to the single crux lemma `L`.**

Given `L` (here the hypothesis `hL` : every `g ∈ Int(D)` has
`g(π) − g(0) ∈ ι(𝔪)`), the three non-memberships `p, tp, (t+1)p ∉ 𝔪·Int(D)`
hold (`three_not_mem_of_L` in `Valuation.lean`, proved sorry-free via the
divided-difference functional + the `𝔪 ⊆ πT` valuation detector), and feeding
them to `p_tp_linindep_of_not_mem` yields the frozen statement.

This isolates everything into `hL`.  `L` is **true** for this two-place pullback
`D` (its single-place analogue is *false* — the `(X²+X)/t` binomial obstruction —
so its proof needs the two-place fixed-divisor structure), and it is discharged
unconditionally as `L_proof` in `CruxL.lean`. -/
theorem p_tp_linindep_of_L
    (hL : ∀ n : ↥(IntPoly Dom Kt), ∃ w : Dom, w ∈ mIdeal ∧
        algebraMap Dom Kt w =
          Polynomial.aeval piK (n : Polynomial Kt) - Polynomial.aeval (0 : Kt) (n : Polynomial Kt)) :
    ∀ a b : ZMod 2,
      Polynomial.C (algebraMap (ZMod 2) Kt a) * pPoly
        + Polynomial.C (algebraMap (ZMod 2) Kt b) * tpPoly ∈ mIntPoly →
      a = 0 ∧ b = 0 := by
  obtain ⟨hp, htp, ht1p⟩ := three_not_mem_of_L hL
  exact p_tp_linindep_of_not_mem hp htp ht1p

/-- **Stage 2.2, complete.**  The frozen joint `𝔽₂`-independence of `p̄, t̄p̄` in
`Int(D)/𝔪·Int(D)`, with the crux lemma `L` (`Prob20.Proofs.KeyObs.L_proof`) now
discharged unconditionally. -/
theorem p_tp_linindep_proof :
    ∀ a b : ZMod 2,
      Polynomial.C (algebraMap (ZMod 2) Kt a) * pPoly
        + Polynomial.C (algebraMap (ZMod 2) Kt b) * tpPoly ∈ mIntPoly →
      a = 0 ∧ b = 0 :=
  p_tp_linindep_of_L L_proof

end Prob20.Proofs.KeyObs
