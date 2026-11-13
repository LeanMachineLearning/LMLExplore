/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bochner integral of a finite sum of indicators

The integral of a finite sum of indicators of events is the expected number of the events that
occur. This is the Bochner counterpart of `MeasureTheory.lintegral_finsetSum_indicator_one`.

## Main statements

* `MeasureTheory.integral_finsetSum_indicator_one`: the Bochner integral of a finite sum of
  indicators of measurable sets of finite measure is the sum of their real measures.
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

end MeasureTheory
