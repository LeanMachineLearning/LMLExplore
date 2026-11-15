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
* `MeasureTheory.Measure.prod_apply_ne_zero_iff`,
  `MeasureTheory.Measure.prod_apply_ne_zero_iff_symm`: a product measure charges a measurable set
  exactly when the set of points whose slice of it is charged is charged.
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

/-- A product measure charges a measurable set `s` exactly when `μ` charges the set of points `x`
whose slice `Prod.mk x ⁻¹' s` is charged by `ν`. -/
lemma prod_apply_ne_zero_iff {μ : Measure α} {ν : Measure β} [SFinite ν] {s : Set (α × β)}
    (hs : MeasurableSet s) :
    μ.prod ν s ≠ 0 ↔ μ (Function.support fun x ↦ ν (Prod.mk x ⁻¹' s)) ≠ 0 := by
  rw [← pos_iff_ne_zero, ← pos_iff_ne_zero, prod_apply hs,
    lintegral_pos_iff_support (measurable_measure_prodMk_left hs)]

/-- A product measure charges a measurable set `s` exactly when `ν` charges the set of points `y`
whose slice `(·, y) ⁻¹' s` is charged by `μ`. -/
lemma prod_apply_ne_zero_iff_symm {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s ≠ 0 ↔ ν (Function.support fun y ↦ μ ((fun x ↦ (x, y)) ⁻¹' s)) ≠ 0 := by
  rw [← pos_iff_ne_zero, ← pos_iff_ne_zero, prod_apply_symm hs,
    lintegral_pos_iff_support (measurable_measure_prodMk_right hs)]

end MeasureTheory.Measure
