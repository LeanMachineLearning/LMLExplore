/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Product measures and pairings with a constant

## Main statements

* `MeasureTheory.Measure.prod_preimage_fst`: `μ.prod ν (Prod.fst ⁻¹' s) = ν univ * μ s`, for any
  set `s`, measurable or not.
* `MeasureTheory.Measure.ae_map_prodMk_right_snd_eq`: under the image of `μ` by `a ↦ (a, b)`,
  the second coordinate is almost surely `b`.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Under a product measure, the preimage of a set by the first projection has measure
`ν univ * μ s`. The set `s` need not be measurable. -/
@[simp]
lemma prod_preimage_fst (μ : Measure α) (ν : Measure β) [SFinite ν] (s : Set α) :
    μ.prod ν (Prod.fst ⁻¹' s) = ν univ * μ s := by
  rw [← prod_univ, prod_prod, mul_comm]

/-- Under the image of `μ` by `a ↦ (a, b)`, the second coordinate is almost surely `b`. -/
lemma ae_map_prodMk_right_snd_eq [MeasurableSingletonClass β] (μ : Measure α) (b : β) :
    ∀ᵐ p ∂(μ.map fun a ↦ (a, b)), p.2 = b :=
  (ae_map_iff measurable_prodMk_right.aemeasurable
    (measurable_snd (measurableSet_singleton b))).2 (.of_forall fun _ ↦ rfl)

end MeasureTheory.Measure
