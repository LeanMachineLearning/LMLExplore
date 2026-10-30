/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The inverse of a positive operator

## Main statements

* `ContinuousLinearMap.IsPositive.ringInverse`: the inverse `Ring.inverse V` of a positive
  continuous linear operator `V` is positive. In particular `0 ≤ ⟪v, V⁻¹ v⟫` for every `v`, by
  `IsPositive.inner_nonneg_right`.
* `ContinuousLinearMap.IsPositive.one_add_inner_ringInverse_pos`: for a positive operator `V` on
  a real inner product space, `0 < 1 + ⟪x, V⁻¹ x⟫`.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inverse `Ring.inverse V` of a positive continuous linear operator `V` is positive.
If `V` is not invertible, then `Ring.inverse V = 0`, which is positive. -/
theorem IsPositive.ringInverse {V : E →L[𝕜] E} (hV : V.IsPositive) :
    (Ring.inverse V).IsPositive := by
  by_cases hu : IsUnit V
  · refine ⟨hV.isSymmetric.ringInverse, fun y ↦ ?_⟩
    have := hV.re_inner_nonneg_right (Ring.inverse V y)
    rwa [V.apply_ringInverse_apply hu] at this
  · rw [Ring.inverse_non_unit V hu]
    exact isPositive_zero

/-- For a positive operator `V` on a real inner product space, `0 < 1 + ⟪x, V⁻¹ x⟫`. -/
theorem IsPositive.one_add_inner_ringInverse_pos {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {V : F →L[ℝ] F} (hV : V.IsPositive) (x : F) :
    0 < 1 + ⟪x, Ring.inverse V x⟫_ℝ :=
  add_pos_of_pos_of_nonneg one_pos (hV.ringInverse.inner_nonneg_right x)

end ContinuousLinearMap
