/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-!
# The exponential of a nonnegative real cast to `EReal`

Bounds of the form `exp (-a x)`, for an exponent `x : ℝ≥0∞` such as a supremum of real
parameters, are stated with the exponential `EReal.exp` of the cast of `x` to `EReal`. This file
identifies `EReal.exp (-x)`, for `x = ofReal y` with `y ≥ 0`, with the real exponential.

## Main statements

* `EReal.exp_neg_coe_ennreal_ofReal`: `exp (-ofReal y) = ofReal (exp (-y))` for `y ≥ 0`.
-/

public section

open scoped ENNReal

namespace EReal

/-- For `y ≥ 0`, the exponential of `-ofReal y`, with `ofReal y : ℝ≥0∞` cast to `EReal`, is the
real exponential `exp (-y)`. -/
lemma exp_neg_coe_ennreal_ofReal {y : ℝ} (hy : 0 ≤ y) :
    exp (-(ENNReal.ofReal y : EReal)) = ENNReal.ofReal (Real.exp (-y)) := by
  rw [coe_ennreal_ofReal, max_eq_left hy, ← coe_neg, exp_coe]

end EReal
