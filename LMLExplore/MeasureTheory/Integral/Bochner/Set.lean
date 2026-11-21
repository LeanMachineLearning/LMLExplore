/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bochner integrals of indicators

The integral of a finite sum of indicators of events is the expected number of the events that
occur. This is the Bochner counterpart of `MeasureTheory.lintegral_finsetSum_indicator_one`.
Under a probability measure, a constant plus a constant indicator integrates to the constant plus
the probability of the event times the value of the indicator.

## Main statements

* `MeasureTheory.integral_finsetSum_indicator_one`: the Bochner integral of a finite sum of
  indicators of measurable sets of finite measure is the sum of their real measures.
* `MeasureTheory.integral_const_add_indicator_const`: under a probability measure `P`, the integral
  of `c + 1_s b` is `c + P(s) • b`.
-/

public section

namespace MeasureTheory

variable {α ι : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Finset ι} {S : ι → Set α}

/-- The Bochner integral of a finite sum of indicators of measurable sets of finite measure is the
sum of their real measures. -/
lemma integral_finsetSum_indicator_one (hS : ∀ i ∈ s, MeasurableSet (S i))
    (hμS : ∀ i ∈ s, μ (S i) ≠ ⊤) :
    ∫ a, ∑ i ∈ s, (S i).indicator 1 a ∂μ = ∑ i ∈ s, μ.real (S i) := by
  rw [integral_finsetSum (f := fun i ↦ (S i).indicator 1) _ fun i hi ↦
    (integrable_indicator_iff (hS i hi)).mpr (integrableOn_const (hμS i hi))]
  exact Finset.sum_congr rfl fun i hi ↦ integral_indicator_one (hS i hi)

/-- Under a probability measure `P`, the integral of a constant `c` plus the indicator of a
measurable set `s` with constant value `b` is `c + P(s) • b`. -/
lemma integral_const_add_indicator_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [IsProbabilityMeasure μ] (c b : E) {s : Set α} (hs : MeasurableSet s) :
    ∫ a, (c + s.indicator (fun _ ↦ b) a) ∂μ = c + μ.real s • b := by
  simp [integral_add, (integrable_const b).indicator hs, integral_indicator_const _ hs]

end MeasureTheory
