/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Lebesgue integral of a function of a map to a finite type

## Main statements

* `MeasureTheory.lintegral_comp_eq_sum_measure_preimage_singleton`: the integral of `g ∘ φ`, for a
  map `φ` to a finite type, is `∑ i, g i * μ (φ ⁻¹' {i})`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- The integral of a function of a map `φ` with values in a finite type is the sum, over the
values `i`, of the value at `i` times the mass of the fibre of `i`. -/
lemma lintegral_comp_eq_sum_measure_preimage_singleton {κ : Type*} [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] {φ : α → κ} (hφ : AEMeasurable φ μ)
    (g : κ → ℝ≥0∞) :
    ∫⁻ x, g (φ x) ∂μ = ∑ i, g i * μ (φ ⁻¹' {i}) := by
  rw [← lintegral_map' (measurable_of_finite g).aemeasurable hφ, lintegral_fintype]
  simp_rw [Measure.map_apply_of_aemeasurable hφ (measurableSet_singleton _)]

end MeasureTheory
