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
# Discharge: each frozen theorem is proven by its `Proofs/` counterpart

The frozen `Theorems.lean` holds the immutable *statements* (as `sorry`). The
real proofs live in `Proofs/` as `*_proof` declarations. Once a frozen theorem
is proved, this file adds an `example : @Frozen = @Proof := rfl`, which compiles
**iff** the proven version has *exactly* the frozen proposition — a
machine-checked guarantee that no statement drifted and nothing was weakened.

All ten frozen theorems are proved: `Proofs/**` supplies each `*_proof`, and the
ten no-drift `@Frozen = @Proof := rfl` gates below are in place. This file stays
`sorry`-free and compiles.
-/

namespace Prob30c

-- The ten `@Frozen = @Proof := rfl` no-drift gates: each compiles iff the proof
-- has *exactly* the frozen proposition.
example : @Prob30c.cancel_const = @Prob30c.cancel_const_proof := rfl
example : @Prob30c.cancel_poly = @Prob30c.cancel_poly_proof := rfl
example : @Prob30c.A_not_qAbsorbing = @Prob30c.A_not_qAbsorbing_proof := rfl
example : @Prob30c.A_succAbsorbing = @Prob30c.A_succAbsorbing_proof := rfl
example : @Prob30c.AX_not_succAbsorbing = @Prob30c.AX_not_succAbsorbing_proof := rfl
example : @Prob30c.AX_succ2Absorbing = @Prob30c.AX_succ2Absorbing_proof := rfl
example : @Prob30c.omega_A = @Prob30c.omega_A_proof := rfl
example : @Prob30c.omega_AX = @Prob30c.omega_AX_proof := rfl
example : @Prob30c.omega_polynomial_increase = @Prob30c.omega_polynomial_increase_proof := rfl
example : @Prob30c.problem30c_false = @Prob30c.problem30c_false_proof := rfl

end Prob30c
