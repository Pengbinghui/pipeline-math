/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Theorems
import Prob30c.Proofs.Cancellation.Basic
import Prob30c.Proofs.PolyCancel.Basic
import Prob30c.Proofs.LowerA.Basic
import Prob30c.Proofs.UpperA.Basic
import Prob30c.Proofs.LowerAX.Basic
import Prob30c.Proofs.UpperAX.Basic
import Prob30c.Proofs.Wrap.Basic

/-!
# Solution: the frozen statements, proven (clean, named results)

`Theorems.lean` holds the immutable *spec* (each theorem is `:= sorry`). This file
restates each of those statements **verbatim** in the `Prob30c.Solution` namespace
and proves it with the corresponding sorry-free `*_proof` declaration from
`Proofs/`. Each `:= …_proof` typechecks only if the proof has *exactly* the frozen
proposition, so this file is simultaneously the no-drift certificate and the
clean, named result that `verify.sh` audits via
`#print axioms Prob30c.Solution.<name>`.

All ten frozen statements are proved: each is restated below and bound to its
sorry-free `*_proof` from `Proofs/`. This file stays `sorry`-free and compiles.
-/

namespace Prob30c.Solution

open Prob30c

open scoped Polynomial

-- Step 2  (the constant cancellation — the obstruction that vanishes over R[X])
theorem cancel_const (q : ℕ) (x y : A q) (hx : x ∈ J q) (hy : y ∈ J q)
    (hxy : x * y ∈ sComponent q) : x * y ∈ tSComponent q := cancel_const_proof q x y hx hy hxy

-- Step 4  (the new polynomial cancellation — free u₁,u₂ parts cancel in char 2)
theorem cancel_poly (q : ℕ) :
    fPoly q * gPoly q
      = Polynomial.C (s q) * (Polynomial.X * (1 + Polynomial.X)) := cancel_poly_proof q

-- Step 3 lower  (ω_{A q}(0) ≥ q+1 : the length-(q+1) irredundant zero-product s·t^q)
theorem A_not_qAbsorbing (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing q (⊥ : Ideal (A q)) := A_not_qAbsorbing_proof q hq

-- Step 3 upper  (ω_{A q}(0) ≤ q+1 : every (q+2)-factor zero-product has an omit-one zero)
theorem A_succAbsorbing (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (q + 1) (⊥ : Ideal (A q)) := A_succAbsorbing_proof q hq

-- Step 5  (ω_{(A q)[X]}(0) ≥ q+2 : the length-(q+2) witness f,g,t,…,t)
theorem AX_not_succAbsorbing (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (q + 1) (⊥ : Ideal (Polynomial (A q))) := AX_not_succAbsorbing_proof q hq

-- Step 6  (ω_{(A q)[X]}(0) ≤ q+2 : matching upper bound over D[X])
theorem AX_succ2Absorbing (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (q + 2) (⊥ : Ideal (Polynomial (A q))) := AX_succ2Absorbing_proof q hq

-- Step 3  (the exact down-stairs value ω_{A q}(0) = q+1)  ★ MILESTONE
theorem omega_A (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (A q)) = q + 1 := omega_A_proof q hq

-- Step 6  (the exact up-stairs value ω_{(A q)[X]}(0) = q+2)
theorem omega_AX (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (Polynomial (A q))) = q + 2 := omega_AX_proof q hq

-- Conclusion  (polynomial extension strictly increases ω by exactly 1)
theorem omega_polynomial_increase (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (Polynomial (A q)))
      = absorbingNumber (⊥ : Ideal (A q)) + 1 := omega_polynomial_increase_proof q hq

-- Headline  (refutation of Problem 30(c))
theorem problem30c_false :
    ∃ (R : Type) (_ : CommRing R) (I : Ideal R),
      absorbingNumber (I.map (Polynomial.C : R →+* Polynomial R)) ≠ absorbingNumber I :=
  problem30c_false_proof

end Prob30c.Solution
