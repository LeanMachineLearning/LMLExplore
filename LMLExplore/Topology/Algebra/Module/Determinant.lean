/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Algebra.Module.Determinant

/-!
# The determinant of the inverse of a continuous linear endomorphism

For an invertible continuous linear endomorphism `V` of a topological module over a commutative
ring, the determinant of its inverse `Ring.inverse V` in the monoid `M →L[R] M` is the inverse of
`det V`: their product is `1`, the determinant of `Ring.inverse V * V = 1`.

## Main statements

* `ContinuousLinearMap.det_ringInverse_mul_det`: `det (Ring.inverse V) * det V = 1` for
  invertible `V`.
-/

public section

namespace ContinuousLinearMap

variable {R M : Type*} [CommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {V : M →L[R] M}

/-- The determinant of the inverse `Ring.inverse V` of an invertible continuous linear
endomorphism `V` is an inverse of `det V`: `det (Ring.inverse V) * det V = 1`. -/
theorem det_ringInverse_mul_det (hV : IsUnit V) : (Ring.inverse V).det * V.det = 1 := by
  rw [← LinearMap.det_comp, ← toLinearMap_comp, ← mul_def, Ring.inverse_mul_cancel V hV,
    toLinearMap_one, map_one]

end ContinuousLinearMap
