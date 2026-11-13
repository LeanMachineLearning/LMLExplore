/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Conditional probability measures

Complements to Mathlib's `ProbabilityTheory.cond`.

## Main statements

* `ProbabilityTheory.cond_smul`: conditioning a measure on a set does not change when the measure
  is multiplied by a constant `c ∉ {0, ∞}`.
* `ProbabilityTheory.cond_map`: conditioning the image of a measure on a set is the image of the
  measure conditioned on the preimage of that set.
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

/-- Conditioning the image of `μ` by `f` on a measurable set `s` is the image by `f` of `μ`
conditioned on the preimage `f ⁻¹' s`. -/
lemma cond_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω} {f : Ω → Ω'}
    (hf : AEMeasurable f μ) {s : Set Ω'} (hs : MeasurableSet s) :
    (μ.map f)[|s] = (μ[|f ⁻¹' s]).map f := by
  rw [cond, cond, Measure.map_smul _ (hf.mono_measure Measure.restrict_le_self),
    Measure.restrict_map_of_aemeasurable hf hs, Measure.map_apply_of_aemeasurable hf hs]

end ProbabilityTheory
