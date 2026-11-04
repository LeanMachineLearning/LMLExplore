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
* `Real.div_sqrt_add_sqrt_mul_div_two`: `a / η + η b / 2 = √(2 b a)` for `η = √(2 a / b)` and
  `b ≥ 0`. It is the tuning of the learning rate `η` in regret bounds of the form
  `log k / η + η n / 2`, as for exponential weights, Exp3 and Exp4.
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

/-- For `b ≥ 0` and `η = √(2 a / b)`, `a / η + η b / 2 = √(2 b a)`: this learning rate balances the
two terms of a regret bound `a / η + η b / 2`. -/
theorem div_sqrt_add_sqrt_mul_div_two (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    a / √(2 * a / b) + √(2 * a / b) * b / 2 = √(2 * b * a) := by
  -- for `a ≤ 0`, both sides vanish
  rcases le_or_gt a 0 with ha | ha
  · have h2a : 2 * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos zero_le_two ha
    rw [sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg h2a hb),
      sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg zero_le_two hb) ha)]
    simp
  rcases hb.eq_or_lt with rfl | hb
  · simp
  have hη : 0 < √(2 * a / b) := sqrt_pos.2 (by positivity)
  have hsq : √(2 * a / b) ^ 2 = 2 * a / b := sq_sqrt (by positivity)
  -- `a / η = η b / 2` and `√(2 b a) = b η`
  have h : a / √(2 * a / b) = √(2 * a / b) * b / 2 := by
    rw [div_eq_iff hη.ne', show √(2 * a / b) * b / 2 * √(2 * a / b) =
      √(2 * a / b) ^ 2 * b / 2 by ring, hsq]
    field_simp
  rw [h, mul_right_comm 2 b a, ← mul_sqrt_div_eq_sqrt_mul _ hb.le]
  ring

end Real
