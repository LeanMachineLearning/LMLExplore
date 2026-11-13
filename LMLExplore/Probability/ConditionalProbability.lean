/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.ConditionalProbability

/-!
# Conditional probability measures

Complements to Mathlib's `ProbabilityTheory.cond`.

## Main statements

* `ProbabilityTheory.cond_smul`: conditioning a measure on a set does not change when the measure
  is multiplied by a constant `c ∉ {0, ∞}`.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Conditioning a measure on a set does not change when the measure is multiplied by a constant
`c ∉ {0, ∞}`. -/
lemma cond_smul (μ : Measure Ω) (s : Set Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    (c • μ)[|s] = μ[|s] := by
  rw [cond, cond, Measure.restrict_smul, smul_apply, smul_eq_mul, smul_smul,
    ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), mul_right_comm, ENNReal.inv_mul_cancel hc0 hc,
    one_mul]

end ProbabilityTheory
