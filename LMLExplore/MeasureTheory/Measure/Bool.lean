/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Probability measures on `Bool`

A probability measure `π` on `Bool` is described by its two masses `π {false}` and `π {true}`,
which sum to `1`, so that their product is at most `1 / 4`. This complements Statlib's
`Statlib.ForMathlib.MeasureTheory.Measure.Bool`.

## Main statements

* `MeasureTheory.Measure.prob_false_add_prob_true`: `π {false} + π {true} = 1`.
* `MeasureTheory.Measure.four_mul_prob_false_mul_prob_true_le_one`:
  `4 * (π {false} * π {true}) ≤ 1`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable (π : Measure Bool) [IsProbabilityMeasure π]

/-- The two masses of a probability measure on `Bool` sum to `1`. -/
lemma prob_false_add_prob_true : π {false} + π {true} = 1 := by
  rw [← prob_add_prob_compl (μ := π) (measurableSet_singleton false), Bool.compl_singleton,
    Bool.not_false]

/-- For a probability measure `π` on `Bool`, `4 * (π {false} * π {true}) ≤ 1`: the product of two
masses of sum `1` is at most `1 / 4`. -/
lemma four_mul_prob_false_mul_prob_true_le_one : 4 * (π {false} * π {true}) ≤ 1 := by
  have hsum := prob_false_add_prob_true π
  rw [← ENNReal.coe_toNNReal (measure_ne_top π {false}),
    ← ENNReal.coe_toNNReal (measure_ne_top π {true})] at hsum ⊢
  have hsum' : (π {false}).toNNReal + (π {true}).toNNReal = 1 := by exact_mod_cast hsum
  have h := four_mul_le_sq_add (π {false}).toNNReal (π {true}).toNNReal
  rw [hsum', one_pow, mul_assoc] at h
  exact_mod_cast h

end MeasureTheory.Measure
