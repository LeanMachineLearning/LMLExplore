/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Real continuous linear functionals and the operator norm

A real continuous linear functional `f` satisfies `f x ≤ ‖f‖ * ‖x‖`, the form of the operator
norm bound `ContinuousLinearMap.le_opNorm` that pairs a loss or a dual vector with a
displacement in online learning and convex analysis.

## Main statements

* `ContinuousLinearMap.apply_le_opNorm_mul_norm`: `f x ≤ ‖f‖ * ‖x‖` for `f : E →L[ℝ] ℝ`.
* `ContinuousLinearMap.exists_lt_apply_of_lt_opNorm_real`: below `‖f‖`, the values of `f` on the
  open unit ball exceed every `r < ‖f‖`, without absolute values.
-/

public section

namespace ContinuousLinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real continuous linear functional is bounded above by its operator norm times the norm of
its argument: `f x ≤ ‖f‖ * ‖x‖`. -/
theorem apply_le_opNorm_mul_norm (f : E →L[ℝ] ℝ) (x : E) : f x ≤ ‖f‖ * ‖x‖ :=
  (Real.le_norm_self _).trans (f.le_opNorm x)

/-- Every real `r < ‖f‖` is exceeded by a value of the real continuous linear functional `f` on
the open unit ball: this is `ContinuousLinearMap.exists_lt_apply_of_lt_opNorm` without the absolute
value, using `f (-x) = -f x`. -/
theorem exists_lt_apply_of_lt_opNorm_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) {r : ℝ} (hr : r < ‖f‖) : ∃ x : E, ‖x‖ < 1 ∧ r < f x := by
  obtain ⟨x, hx1, hrx⟩ := f.exists_lt_apply_of_lt_opNorm hr
  rw [Real.norm_eq_abs] at hrx
  rcases abs_choice (f x) with h | h
  · exact ⟨x, hx1, h ▸ hrx⟩
  · exact ⟨-x, by rwa [norm_neg], by rwa [map_neg, ← h]⟩

end ContinuousLinearMap
