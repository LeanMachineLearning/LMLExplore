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

* `ENNReal.log_le_log_add_of_div_lt`: if `x / y < exp c`, then `log x ≤ log y + c`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- If `x / y < exp c`, then `log x ≤ log y + c`. -/
lemma log_le_log_add_of_div_lt {x y : ℝ≥0∞} {c : ℝ}
    (h : x / y < ENNReal.ofReal (Real.exp c)) : log x ≤ log y + c := by
  rcases eq_or_ne y ∞ with rfl | hy
  · simp
  rcases eq_or_ne y 0 with rfl | hy0
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · simp [ENNReal.div_zero hx0] at h
  have hlt : x < ENNReal.ofReal (Real.exp c) * y :=
    (ENNReal.div_lt_iff (Or.inl hy0) (Or.inl hy)).1 h
  calc log x ≤ log (ENNReal.ofReal (Real.exp c) * y) := log_le_log hlt.le
  _ = log y + c := by
    rw [log_mul_add, log_ofReal_of_pos (Real.exp_pos c), Real.log_exp, add_comm]

end ENNReal
