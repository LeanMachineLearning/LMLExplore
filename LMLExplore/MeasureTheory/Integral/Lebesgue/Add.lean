/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Lebesgue integral of a finite sum of indicators

## Main statements

* `MeasureTheory.lintegral_finsetSum_indicator_one`: the Lebesgue integral of a finite sum of
  indicators of measurable sets is the sum of their measures, and
  `MeasureTheory.lintegral_finsetSum_indicator_one₀`, its version for null measurable sets.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α ι : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Finset ι} {S : ι → Set α}

/-- The Lebesgue integral of a finite sum of indicators of null measurable sets is the sum of their
measures. -/
lemma lintegral_finsetSum_indicator_one₀ (hS : ∀ i ∈ s, NullMeasurableSet (S i) μ) :
    ∫⁻ a, ∑ i ∈ s, (S i).indicator 1 a ∂μ = ∑ i ∈ s, μ (S i) := by
  rw [lintegral_finsetSum' (f := fun i ↦ (S i).indicator 1) _
    fun i hi ↦ measurable_one.aemeasurable.indicator₀ (hS i hi)]
  exact Finset.sum_congr rfl fun i hi ↦ lintegral_indicator_one₀ (hS i hi)

/-- The Lebesgue integral of a finite sum of indicators of measurable sets is the sum of their
measures. -/
lemma lintegral_finsetSum_indicator_one (hS : ∀ i ∈ s, MeasurableSet (S i)) :
    ∫⁻ a, ∑ i ∈ s, (S i).indicator 1 a ∂μ = ∑ i ∈ s, μ (S i) :=
  lintegral_finsetSum_indicator_one₀ fun i hi ↦ (hS i hi).nullMeasurableSet

end MeasureTheory
