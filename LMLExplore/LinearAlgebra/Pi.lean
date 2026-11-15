/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Linear maps on `R × (ι → R)` and on `ι → 𝕜`

A linear map on `R × (ι → R)`, for a finite type `ι`, is determined by its values on the
coordinate vectors `(1, 0)` and `(0, Pi.single i 1)`. This is the analogue for the product with an
extra coordinate of Mathlib's `LinearMap.pi_apply_eq_sum_univ`. A linear functional on `ι → 𝕜`,
for an ordered field `𝕜`, that is bounded above on the nonpositive vectors is nonnegative at the
coordinate vectors.

## Main statements

* `LinearMap.prod_pi_apply_eq_sum_univ`: the expansion of `f (t, u)` along the coordinate vectors.
* `LinearMap.apply_single_nonneg_of_forall_nonpos_lt`: a linear functional on `ι → 𝕜` that is
  below `u` at every nonpositive vector is nonnegative at every coordinate vector.
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

/-- A linear functional on `ι → 𝕜` that is below `u` at every nonpositive vector is nonnegative at
every coordinate vector `Pi.single i 1`. -/
theorem apply_single_nonneg_of_forall_nonpos_lt {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [DecidableEq ι] (φ : (ι → 𝕜) →ₗ[𝕜] 𝕜) {u : 𝕜}
    (h : ∀ v : ι → 𝕜, v ≤ 0 → φ v < u) (i : ι) : 0 ≤ φ (Pi.single i 1) := by
  have hu0 : 0 < u := by simpa using h 0 le_rfl
  by_contra hneg
  have hneg' : φ (Pi.single i 1) < 0 := lt_of_not_ge hneg
  have hc : 0 ≤ u / -φ (Pi.single i 1) := div_nonneg hu0.le (neg_nonneg.2 hneg'.le)
  have := h ((u / -φ (Pi.single i 1)) • -Pi.single i 1) fun j ↦ by
    simp only [Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hc (by rw [Pi.single_apply]; split_ifs <;> simp)
  rw [map_smul, map_neg, smul_eq_mul, div_mul_cancel₀ _ (neg_pos.2 hneg').ne'] at this
  exact lt_irrefl _ this

end LinearMap
