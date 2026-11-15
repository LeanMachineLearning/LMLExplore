/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous linear endomorphisms: inverses and `1 - T`

For an invertible continuous linear endomorphism `V` of a topological module, its inverse
`Ring.inverse V` in the monoid `M →L[R] M` is a two-sided inverse of `V` as a function.

For normed spaces, Tau Ceti provides the pointwise forms
`ContinuousLinearMap.apply_ringInverse_apply` and `ContinuousLinearMap.ringInverse_apply_apply`;
the statements here need no norm.

For a continuous linear endomorphism `T` of a topological module over a ring, `1 - T` acts as
`x ↦ x - T x`, and its kernel is the space of fixed points of `T`.

## Main statements

* `ContinuousLinearMap.leftInverse_ringInverse`: `Ring.inverse V (V y) = y` for invertible `V`.
* `ContinuousLinearMap.rightInverse_ringInverse`: `V (Ring.inverse V y) = y` for invertible `V`.
* `ContinuousLinearMap.one_sub_apply`: `(1 - T) x = x - T x`.
* `ContinuousLinearMap.mem_ker_one_sub_iff`: `x ∈ ker (1 - T)` iff `T x = x`.
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

section Ring

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [IsTopologicalAddGroup E]

/-- `(1 - T) x = x - T x`. -/
lemma one_sub_apply (T : E →L[R] E) (x : E) : (1 - T) x = x - T x := by
  rw [sub_apply, one_apply_eq_self]

/-- The kernel of `1 - T` is the space of fixed points of `T`. -/
lemma mem_ker_one_sub_iff {T : E →L[R] E} {x : E} : x ∈ (1 - T).ker ↔ T x = x := by
  rw [LinearMap.mem_ker, coe_coe, one_sub_apply, sub_eq_zero, eq_comm]

end Ring

end ContinuousLinearMap
