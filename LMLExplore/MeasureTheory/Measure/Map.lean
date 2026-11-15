/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Map

/-!
# Mixtures of invariant measures

If two measures are invariant under a measurable map `f`, so is every combination
`p • μ + q • ν` of them with weights in `ℝ≥0∞`. With weights summing to `1`, this says that the
probability measures invariant under `f` are closed under mixtures.

## Main statements

* `MeasureTheory.Measure.map_smul_add_smul_of_map_eq`: if `μ.map f = μ` and `ν.map f = ν`, then
  `(p • μ + q • ν).map f = p • μ + q • ν`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {f : α → α} {μ ν : Measure α}

/-- A combination `p • μ + q • ν` of measures that are invariant under a measurable map `f` is
invariant under `f`. -/
theorem map_smul_add_smul_of_map_eq (hf : Measurable f) (hμ : μ.map f = μ) (hν : ν.map f = ν)
    (p q : ℝ≥0∞) : (p • μ + q • ν).map f = p • μ + q • ν := by
  rw [Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable, hμ, hν]

end MeasureTheory.Measure
