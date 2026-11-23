/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# Finite convex combinations of probability measures

A combination `∑ i, w i • P i` of finitely many probability measures with weights `w i : ℝ≥0` of
sum `1` is a probability measure. This is the finite form of Tau Ceti's
`TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul`, for two measures.

## Main statements

* `MeasureTheory.isProbabilityMeasure_sum_smul`: a finite convex combination of probability
  measures is a probability measure.
* `MeasureTheory.convex_isProbabilityMeasure`: the probability measures form a convex set of
  measures over `ℝ≥0∞`.
-/

public section

open scoped ENNReal NNReal

namespace MeasureTheory

/-- A combination of probability measures with weights in `ℝ≥0` of sum `1` is a probability
measure. -/
lemma isProbabilityMeasure_sum_smul {α ι : Type*} {mα : MeasurableSpace α} [Fintype ι]
    {P : ι → Measure α} [∀ i, IsProbabilityMeasure (P i)] {w : ι → ℝ≥0} (hw : ∑ i, w i = 1) :
    IsProbabilityMeasure (∑ i, w i • P i) := by
  constructor
  simp only [sum_apply, smul_apply, measure_univ, ENNReal.smul_one]
  exact_mod_cast hw

/-- The probability measures form a convex set of measures over `ℝ≥0∞`. -/
lemma convex_isProbabilityMeasure {α : Type*} {mα : MeasurableSpace α} :
    Convex ℝ≥0∞ {P : Measure α | IsProbabilityMeasure P} := by
  intro P (_ : IsProbabilityMeasure P) Q (_ : IsProbabilityMeasure Q) a b _ _ hab
  exact TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul hab P Q

end MeasureTheory
