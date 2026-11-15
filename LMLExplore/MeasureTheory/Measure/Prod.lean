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
* `MeasureTheory.Measure.le_prod_apply_of_ae_le`,
  `MeasureTheory.Measure.le_prod_apply_of_ae_le_symm`: if almost every section of a measurable
  set has measure at least `c`, then the set has product measure at least `c` times the mass of
  the other factor. For probability measures, a high-probability event given each value of one
  coordinate is a high-probability event of the pair.
* `MeasureTheory.Measure.prod_apply_ne_zero_iff`,
  `MeasureTheory.Measure.prod_apply_ne_zero_iff_symm`: a product measure charges a measurable set
  exactly when the set of points whose slice of it is charged is charged.
-/

public section

open Set
open scoped ENNReal

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

/-- If almost every section `{y | (x, y) ∈ s}` of a measurable set `s` has `ν`-measure at least
`c`, then `s` has product measure at least `c * μ univ`. -/
lemma le_prod_apply_of_ae_le {μ : Measure α} {ν : Measure β} [SFinite ν] {s : Set (α × β)}
    (hs : MeasurableSet s) {c : ℝ≥0∞} (h : ∀ᵐ x ∂μ, c ≤ ν (Prod.mk x ⁻¹' s)) :
    c * μ univ ≤ μ.prod ν s := by
  rw [prod_apply hs, ← lintegral_const]
  exact lintegral_mono_ae h

/-- If almost every section `{x | (x, y) ∈ s}` of a measurable set `s` has `μ`-measure at least
`c`, then `s` has product measure at least `c * ν univ`. -/
lemma le_prod_apply_of_ae_le_symm {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set (α × β)} (hs : MeasurableSet s) {c : ℝ≥0∞}
    (h : ∀ᵐ y ∂ν, c ≤ μ ((fun x ↦ (x, y)) ⁻¹' s)) : c * ν univ ≤ μ.prod ν s := by
  rw [prod_apply_symm hs, ← lintegral_const]
  exact lintegral_mono_ae h

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
