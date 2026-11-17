/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Weighted maximum norms on `ι → ℝ`

For positive weights `v : ι → ℝ` on a finite type `ι`, the maximum norm weighted by `v` is
`‖y / v‖ = max_i |y i| / v i`, written with the sup norm of `ι → ℝ` and the coordinatewise
quotient.

## Main statements

* `LMLExplore.abs_div_le_norm_div`: each coordinate `|y i / v i|` is at most `‖y / v‖`.
* `LMLExplore.norm_le_norm_mul_norm_div`: the maximum norm `‖y‖` is at most `‖v‖ * ‖y / v‖`.
-/

public section

namespace LMLExplore

variable {ι : Type*} [Fintype ι]

/-- A coordinate of `y / v` is bounded by the weighted maximum norm `‖y / v‖`. -/
theorem abs_div_le_norm_div (y v : ι → ℝ) (i : ι) : |y i / v i| ≤ ‖y / v‖ := by
  simpa [abs_div] using norm_le_pi_norm (y / v) i

/-- The maximum norm is bounded by the weighted maximum norm, for positive weights `v`. -/
theorem norm_le_norm_mul_norm_div {v : ι → ℝ} (hv : ∀ i, 0 < v i) (y : ι → ℝ) :
    ‖y‖ ≤ ‖v‖ * ‖y / v‖ := by
  have : y = v * (y / v) := by
    ext i
    simp [mul_div_cancel₀ _ (hv i).ne']
  calc ‖y‖ = ‖v * (y / v)‖ := congrArg _ this
    _ ≤ ‖v‖ * ‖y / v‖ := norm_mul_le _ _

end LMLExplore
