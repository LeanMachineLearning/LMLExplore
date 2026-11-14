/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Real continuous linear functionals and the operator norm

A real continuous linear functional `f` satisfies `f x ≤ ‖f‖ * ‖x‖`, the form of the operator
norm bound `ContinuousLinearMap.le_opNorm` that pairs a loss or a dual vector with a
displacement in online learning and convex analysis.

## Main statements

* `ContinuousLinearMap.apply_le_opNorm_mul_norm`: `f x ≤ ‖f‖ * ‖x‖` for `f : E →L[ℝ] ℝ`.
-/

public section

namespace ContinuousLinearMap

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A real continuous linear functional is bounded above by its operator norm times the norm of
its argument: `f x ≤ ‖f‖ * ‖x‖`. -/
theorem apply_le_opNorm_mul_norm (f : E →L[ℝ] ℝ) (x : E) : f x ≤ ‖f‖ * ‖x‖ :=
  (Real.le_norm_self _).trans (f.le_opNorm x)

end ContinuousLinearMap
