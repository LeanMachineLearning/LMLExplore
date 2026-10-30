/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Applying the inverse of an invertible continuous linear endomorphism

For an invertible continuous linear endomorphism `V`, its inverse `Ring.inverse V` in the monoid
`M →L[R] M` is a two-sided inverse of `V` as a function.

## Main statements

* `ContinuousLinearMap.apply_ringInverse_apply`: `V (Ring.inverse V y) = y` for invertible `V`.
* `ContinuousLinearMap.ringInverse_apply_apply`: `Ring.inverse V (V y) = y` for invertible `V`.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- An invertible continuous linear endomorphism `V` satisfies `V (V⁻¹ y) = y`,
where `V⁻¹ = Ring.inverse V`. -/
@[simp]
theorem apply_ringInverse_apply (V : M →L[R] M) (hV : IsUnit V) (y : M) :
    V (Ring.inverse V y) = y := by
  rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel V hV, one_apply_eq_self]

/-- An invertible continuous linear endomorphism `V` satisfies `V⁻¹ (V y) = y`,
where `V⁻¹ = Ring.inverse V`. -/
@[simp]
theorem ringInverse_apply_apply (V : M →L[R] M) (hV : IsUnit V) (y : M) :
    Ring.inverse V (V y) = y := by
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel V hV, one_apply_eq_self]

end ContinuousLinearMap
