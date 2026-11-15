/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Lebesgue integrals as finite sums

In a space with measurable singletons, the lower Lebesgue integral of any function, measurable or
not, against a measure carried by a finite set `s` is the finite sum `∑ x ∈ s, f x * μ {x}`, and
each atom contributes at most the whole integral. The integral of a function of a map to a finite
type is the sum over the values of the value times the mass of its fibre.

## Main statements

* `MeasureTheory.lintegral_eq_sum_of_measure_compl_eq_zero`: the integral against a measure
  carried by a finite set is a finite sum over its atoms.
* `MeasureTheory.mul_measure_singleton_le_lintegral`: `f x * μ {x} ≤ ∫⁻ y, f y ∂μ`.
* `MeasureTheory.lintegral_comp_eq_sum_measure_preimage_singleton`: the integral of `g ∘ φ`, for a
  map `φ` to a finite type, is `∑ i, g i * μ (φ ⁻¹' {i})`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

section MeasurableSingletonClass

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ : Measure α}

/-- The integral of any function against a measure carried by a finite set `s` is the finite sum
`∑ x ∈ s, f x * μ {x}`. -/
theorem lintegral_eq_sum_of_measure_compl_eq_zero {s : Finset α} (hs : μ (↑s)ᶜ = 0)
    (f : α → ℝ≥0∞) : ∫⁻ x, f x ∂μ = ∑ x ∈ s, f x * μ {x} := by
  rw [← lintegral_finset, Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hs)]

/-- The contribution `f x * μ {x}` of an atom is at most the integral of `f`. -/
theorem mul_measure_singleton_le_lintegral (f : α → ℝ≥0∞) (x : α) :
    f x * μ {x} ≤ ∫⁻ y, f y ∂μ :=
  (lintegral_singleton f x).symm.trans_le (setLIntegral_le_lintegral _ _)

end MeasurableSingletonClass

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
