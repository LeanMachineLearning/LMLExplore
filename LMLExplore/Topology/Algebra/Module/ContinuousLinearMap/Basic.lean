/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# The inverse of an invertible continuous linear endomorphism

For an invertible continuous linear endomorphism `V` of a topological module, its inverse
`Ring.inverse V` in the monoid `M →L[R] M` is a two-sided inverse of `V` as a function.

For normed spaces, Tau Ceti provides the pointwise forms
`ContinuousLinearMap.apply_ringInverse_apply` and `ContinuousLinearMap.ringInverse_apply_apply`;
the statements here need no norm.

## Main statements

* `ContinuousLinearMap.leftInverse_ringInverse`: `Ring.inverse V (V y) = y` for invertible `V`.
* `ContinuousLinearMap.rightInverse_ringInverse`: `V (Ring.inverse V y) = y` for invertible `V`.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  {V : M →L[R] M}

/-- The inverse `Ring.inverse V` of an invertible continuous linear endomorphism `V` is a left
inverse of `V`: `Ring.inverse V (V y) = y`. -/
theorem leftInverse_ringInverse (hV : IsUnit V) : Function.LeftInverse ⇑(Ring.inverse V) V :=
  fun y ↦ by rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel V hV, one_apply_eq_self]

/-- The inverse `Ring.inverse V` of an invertible continuous linear endomorphism `V` is a right
inverse of `V`: `V (Ring.inverse V y) = y`. -/
theorem rightInverse_ringInverse (hV : IsUnit V) : Function.RightInverse ⇑(Ring.inverse V) V :=
  fun y ↦ by rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel V hV, one_apply_eq_self]

end ContinuousLinearMap
