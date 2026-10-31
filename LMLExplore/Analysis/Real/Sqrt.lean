/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Square roots of quotients

## Main statements

* `Real.mul_sqrt_div_eq_sqrt_mul`: `x * √(y / x) = √(y * x)` for `x ≥ 0`. It converts a confidence
  width `√(c / s)` for an empirical mean of `s` samples into the width `√(c s)` for their sum.
-/

public section

namespace Real

/-- For `x ≥ 0`, `x * √(y / x) = √(y * x)`. -/
theorem mul_sqrt_div_eq_sqrt_mul (y : ℝ) {x : ℝ} (hx : 0 ≤ x) : x * √(y / x) = √(y * x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  calc x * √(y / x)
  _ = √(x ^ 2) * √(y / x) := by rw [sqrt_sq hx.le]
  _ = √(y * x) := by
    rw [← sqrt_mul (sq_nonneg _)]
    congr 1
    field_simp

end Real
