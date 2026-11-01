/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The sigmoid function with values in the unit interval

## Main statements

* `unitInterval.coe_sigmoid`: the real number underlying `unitInterval.sigmoid x` is
  `Real.sigmoid x`.
-/

public section

namespace unitInterval

/-- The sigmoid function with values in the unit interval is `Real.sigmoid`. -/
@[simp]
lemma coe_sigmoid (x : ℝ) : (sigmoid x : ℝ) = Real.sigmoid x := (rfl)

end unitInterval
