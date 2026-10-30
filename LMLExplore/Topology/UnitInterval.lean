/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.UnitInterval

/-!
# The coercion from the unit interval to `ℝ≥0`

## Main statements

* `unitInterval.toNNReal_eq_zero`: `toNNReal p = 0 ↔ p = 0`.
-/

public section

namespace unitInterval

/-- The coercion `unitInterval.toNNReal` vanishes exactly at `0`. -/
@[simp]
lemma toNNReal_eq_zero {p : I} : toNNReal p = 0 ↔ p = 0 := by
  rw [← NNReal.coe_eq_zero, coe_toNNReal, Set.Icc.coe_eq_zero]

end unitInterval
