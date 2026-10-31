/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Restricting a composition-product to a set of first coordinates

Restricting the first marginal of `μ ⊗ₘ κ` to a measurable set `s` is the same as restricting the
composition-product to the cylinder `s ×ˢ univ`. This is the measure version of Mathlib's
`ProbabilityTheory.Kernel.compProd_restrict_left`.

## Main statements

* `MeasureTheory.Measure.compProd_restrict_left`:
  `μ.restrict s ⊗ₘ κ = (μ ⊗ₘ κ).restrict (s ×ˢ univ)`.
-/

public section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {κ : Kernel α β} {s : Set α}

/-- Restricting the first marginal of a composition-product to `s` is restricting the
composition-product to `s ×ˢ univ`. -/
lemma compProd_restrict_left [SFinite μ] [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    μ.restrict s ⊗ₘ κ = (μ ⊗ₘ κ).restrict (s ×ˢ univ) := by
  ext t ht
  rw [restrict_apply ht, compProd_apply ht, compProd_apply (ht.inter (hs.prod .univ)),
    ← lintegral_indicator hs]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : a ∈ s <;> simp [ha, Set.preimage, Set.indicator]

end MeasureTheory.Measure
