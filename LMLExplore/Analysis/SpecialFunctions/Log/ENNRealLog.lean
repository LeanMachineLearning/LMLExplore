/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.Data.EReal.Inv

/-!
# Bounds on the logarithm of extended nonnegative reals

## Main statements

* `ENNReal.log_ofReal_exp`: the logarithm of `exp x` is `x`.
* `ENNReal.log_le_log_add_of_div_le`: if `x / y ≤ exp c`, then `log x ≤ log y + c`.
* `ENNReal.le_neg_log_div_of_le_ofReal_exp`: for `0 < n`, if `x ≤ exp (-(n r))`, then
  `r ≤ -(log x) / n`.
* `ENNReal.neg_log_div_le_of_ofReal_exp_le`: for `0 < n`, if `exp (-(n r)) ≤ x`, then
  `-(log x) / n ≤ r`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- The logarithm of `exp x`, as an extended nonnegative real, is `x`. It is not a simp lemma:
simp rewrites its left-hand side with `ENNReal.log_ofReal` first. -/
lemma log_ofReal_exp (x : ℝ) : log (ENNReal.ofReal (Real.exp x)) = x := by
  rw [log_ofReal_of_pos (Real.exp_pos x), Real.log_exp]

/-- If `x / y ≤ exp c`, then `log x ≤ log y + c`. -/
lemma log_le_log_add_of_div_le {x y : ℝ≥0∞} {c : ℝ}
    (h : x / y ≤ ENNReal.ofReal (Real.exp c)) : log x ≤ log y + c := by
  rcases eq_or_ne y ∞ with rfl | hy
  · simp
  rcases eq_or_ne y 0 with rfl | hy0
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · simp [ENNReal.div_zero hx0] at h
  have hle : x ≤ ENNReal.ofReal (Real.exp c) * y :=
    (ENNReal.div_le_iff hy0 hy).1 h
  calc log x ≤ log (ENNReal.ofReal (Real.exp c) * y) := log_le_log hle
  _ = log y + c := by
    rw [log_mul_add, log_ofReal_exp, add_comm]

/-- For `0 < n`, an `x` at most `exp (-(n r))` has `r ≤ -(log x) / n`. -/
lemma le_neg_log_div_of_le_ofReal_exp {x : ℝ≥0∞} {n : ℕ} {r : ℝ} (hn : 0 < n)
    (h : x ≤ ENNReal.ofReal (Real.exp (-(n * r)))) : (r : EReal) ≤ -log x / (n : EReal) := by
  have hlog := log_le_log h
  rw [log_ofReal_exp, EReal.coe_neg] at hlog
  rw [EReal.coe_le_div_natCast_iff hn]
  exact EReal.le_neg_of_le_neg hlog

/-- For `0 < n`, an `x` at least `exp (-(n r))` has `-(log x) / n ≤ r`. -/
lemma neg_log_div_le_of_ofReal_exp_le {x : ℝ≥0∞} {n : ℕ} {r : ℝ} (hn : 0 < n)
    (h : ENNReal.ofReal (Real.exp (-(n * r))) ≤ x) : -log x / (n : EReal) ≤ r := by
  have hlog := log_le_log h
  rw [log_ofReal_exp, EReal.coe_neg] at hlog
  rw [EReal.div_natCast_le_coe_iff hn]
  exact EReal.neg_le_of_neg_le hlog

end ENNReal
