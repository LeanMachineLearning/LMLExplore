/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.LinearAlgebra.Pi

/-!
# Linear maps on `R × (ι → R)`

A linear map on `R × (ι → R)`, for a finite type `ι`, is determined by its values on the
coordinate vectors `(1, 0)` and `(0, Pi.single i 1)`. This is the analogue for the product with an
extra coordinate of Mathlib's `LinearMap.pi_apply_eq_sum_univ`.

## Main statements

* `LinearMap.prod_pi_apply_eq_sum_univ`: the expansion of `f (t, u)` along the coordinate vectors.
-/

public section

namespace LinearMap

variable {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A linear map on `R × (ι → R)` is determined by its values on the coordinate vectors
`(1, 0)` and `(0, Pi.single i 1)`. -/
theorem prod_pi_apply_eq_sum_univ [Fintype ι] [DecidableEq ι] (f : R × (ι → R) →ₗ[R] M) (t : R)
    (u : ι → R) : f (t, u) = t • f (1, 0) + ∑ i, u i • f (0, Pi.single i 1) := by
  have hdec : (t, u) = t • ((1 : R), (0 : ι → R)) + ∑ i, u i • ((0 : R), Pi.single i (1 : R)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Pi.single_apply]
  rw [hdec, map_add, map_smul, map_sum]
  simp only [map_smul]

end LinearMap
