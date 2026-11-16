/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Bounds on the logarithm of extended nonnegative reals

## Main statements

* `ENNReal.log_ofReal_exp`: the logarithm of `exp x` is `x`.
* `ENNReal.log_le_log_add_of_div_le`: if `x / y ≤ exp c`, then `log x ≤ log y + c`.
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

end ENNReal
