/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Powers of extended nonnegative reals

A complement to `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`.

## Main statements

* `ENNReal.rpow_add_one`: `x ^ (y + 1) = x ^ y * x` for `x ≠ 0, ∞`, the `ℝ≥0∞` counterpart of
  Mathlib's `NNReal.rpow_add_one`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- `x ^ (y + 1) = x ^ y * x` for `x ≠ 0, ∞`. -/
theorem rpow_add_one {x : ℝ≥0∞} (hx : x ≠ 0) (hx' : x ≠ ∞) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add _ _ hx hx', rpow_one]

end ENNReal
