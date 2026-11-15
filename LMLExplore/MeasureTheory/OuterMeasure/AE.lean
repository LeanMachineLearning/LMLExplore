/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Almost everywhere properties from a set of full measure

A property that holds at every point of a set whose complement is null holds almost everywhere.
This is `Filter.eventually_of_mem` for the filter `MeasureTheory.ae μ`, stated with the measure of
the complement, the form in which sets of full measure usually arise.

## Main statements

* `MeasureTheory.ae_of_forall_mem_of_measure_compl_eq_zero`: if `μ sᶜ = 0` and `p` holds on `s`,
  then `p` holds `μ`-almost everywhere.
-/

public section

namespace MeasureTheory

variable {α F : Type*} [FunLike F (Set α) ENNReal] [OuterMeasureClass F α] {μ : F} {s : Set α}
  {p : α → Prop}

/-- A property that holds on a set whose complement is null holds almost everywhere. -/
theorem ae_of_forall_mem_of_measure_compl_eq_zero (hs : μ sᶜ = 0) (hp : ∀ x ∈ s, p x) :
    ∀ᵐ x ∂μ, p x :=
  Filter.eventually_of_mem (mem_ae_iff.2 hs) hp

end MeasureTheory
