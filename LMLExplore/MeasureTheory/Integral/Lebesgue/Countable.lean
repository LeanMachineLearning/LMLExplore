/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Lebesgue integrals against measures carried by a finite set

In a space with measurable singletons, the lower Lebesgue integral of any function, measurable or
not, against a measure carried by a finite set `s` is the finite sum `∑ x ∈ s, f x * μ {x}`, and
each atom contributes at most the whole integral.

## Main statements

* `MeasureTheory.lintegral_eq_sum_of_measure_compl_eq_zero`: the integral against a measure
  carried by a finite set is a finite sum over its atoms.
* `MeasureTheory.mul_measure_singleton_le_lintegral`: `f x * μ {x} ≤ ∫⁻ y, f y ∂μ`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

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

end MeasureTheory
