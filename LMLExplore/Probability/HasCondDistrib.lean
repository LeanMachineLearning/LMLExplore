/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasCondDistrib
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Conditional distributions: joint masses and composition-products

If `κ` is the conditional distribution of `Y` given `X` under `P`, then the joint mass of a
rectangle is obtained by integrating the conditional mass: for measurable sets `s` and `t`,
`P(X ∈ s, Y ∈ t) = ∫_{X ∈ s} κ X t dP`, and more generally
`∫_{X ∈ s} g(Y) dP = ∫_{X ∈ s} (∫ g dκ(X)) dP` for measurable `g ≥ 0`. The second coordinate of
a composition-product `μ ⊗ₘ η.comap f` has conditional distribution `η` given `f` of the first
coordinate.

## Main statements

* `ProbabilityTheory.HasCondDistrib.measure_preimage_inter_eq_setLIntegral`:
  `P (X ⁻¹' s ∩ Y ⁻¹' t) = ∫⁻ ω in X ⁻¹' s, κ (X ω) t ∂P`.
* `ProbabilityTheory.HasCondDistrib.setLIntegral_comp_eq_setLIntegral_lintegral`:
  `∫⁻ ω in X ⁻¹' s, g (Y ω) ∂P = ∫⁻ ω in X ⁻¹' s, ∫⁻ y, g y ∂(κ (X ω)) ∂P`.
* `ProbabilityTheory.hasCondDistrib_snd_compProd_comap`: under `μ ⊗ₘ η.comap f`, the second
  coordinate has conditional distribution `η` given `f` of the first coordinate.

The last statement is adapted from the LMLPapers project (same author).
-/

public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

section JointMass

variable {Ω 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} [SFinite P] {X : Ω → 𝓧} {Y : Ω → 𝓨}
  {κ : Kernel 𝓧 𝓨} [IsSFiniteKernel κ]

/-- If `κ` is the conditional distribution of `Y` given `X`, then for measurable sets `s` and `t`,
`P(X ∈ s, Y ∈ t) = ∫_{X ∈ s} κ X t dP`. -/
lemma HasCondDistrib.measure_preimage_inter_eq_setLIntegral (h : HasCondDistrib Y X κ P)
    {s : Set 𝓧} (hs : MeasurableSet s) {t : Set 𝓨} (ht : MeasurableSet t) :
    P (X ⁻¹' s ∩ Y ⁻¹' t) = ∫⁻ ω in X ⁻¹' s, κ (X ω) t ∂P := by
  calc P (X ⁻¹' s ∩ Y ⁻¹' t)
      = P.map (fun ω ↦ (X ω, Y ω)) (s ×ˢ t) := by
        rw [Measure.map_apply_of_aemeasurable h.aemeasurable (hs.prod ht), Set.mk_preimage_prod]
    _ = (P.map X ⊗ₘ κ) (s ×ˢ t) := by rw [h.map_eq]
    _ = ∫⁻ x in s, κ x t ∂(P.map X) := Measure.compProd_apply_prod hs ht
    _ = ∫⁻ ω in X ⁻¹' s, κ (X ω) t ∂P := by
        rw [Measure.restrict_map_of_aemeasurable h.aemeasurable_fst hs,
          lintegral_map' (κ.measurable_coe ht).aemeasurable h.aemeasurable_fst.restrict]

/-- If `κ` is the conditional distribution of `Y` given `X`, then for a measurable set `s` and a
measurable function `g ≥ 0`, `∫_{X ∈ s} g(Y) dP = ∫_{X ∈ s} (∫ g dκ(X)) dP`. -/
lemma HasCondDistrib.setLIntegral_comp_eq_setLIntegral_lintegral (h : HasCondDistrib Y X κ P)
    {s : Set 𝓧} (hs : MeasurableSet s) {g : 𝓨 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω in X ⁻¹' s, g (Y ω) ∂P = ∫⁻ ω in X ⁻¹' s, ∫⁻ y, g y ∂(κ (X ω)) ∂P := by
  have hg' : Measurable fun p : 𝓧 × 𝓨 ↦ g p.2 := hg.comp measurable_snd
  calc ∫⁻ ω in X ⁻¹' s, g (Y ω) ∂P
      = ∫⁻ p in s ×ˢ Set.univ, g p.2 ∂(P.map (fun ω ↦ (X ω, Y ω))) := by
        rw [Measure.restrict_map_of_aemeasurable h.aemeasurable (hs.prod .univ),
          lintegral_map' hg'.aemeasurable h.aemeasurable.restrict,
          Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]
    _ = ∫⁻ p in s ×ˢ Set.univ, g p.2 ∂(P.map X ⊗ₘ κ) := by rw [h.map_eq]
    _ = ∫⁻ x in s, ∫⁻ y, g y ∂(κ x) ∂(P.map X) := by
        rw [Measure.setLIntegral_compProd hg' hs .univ]
        simp
    _ = ∫⁻ ω in X ⁻¹' s, ∫⁻ y, g y ∂(κ (X ω)) ∂P := by
        rw [Measure.restrict_map_of_aemeasurable h.aemeasurable_fst hs,
          lintegral_map' hg.lintegral_kernel.aemeasurable h.aemeasurable_fst.restrict]

end JointMass

section CompProd

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- Under `μ ⊗ₘ η.comap f`, the second coordinate has conditional distribution `η` given `f` of
the first coordinate, when `η` is a probability measure at every point of the range of `f`. -/
lemma hasCondDistrib_snd_compProd_comap (μ : Measure α) [SFinite μ]
    (η : Kernel β γ) [IsSFiniteKernel η] {f : α → β} (hf : Measurable f)
    (hη : ∀ a, IsProbabilityMeasure (η (f a))) :
    HasCondDistrib Prod.snd (fun p : α × γ ↦ f p.1) η (μ ⊗ₘ η.comap f hf) := by
  have : IsMarkovKernel (η.comap f hf) := ⟨fun a ↦ by rw [Kernel.comap_apply]; exact hη a⟩
  refine ⟨by fun_prop, (Measure.map_prodMap_compProd_comap μ η hf).trans ?_⟩
  congr 1
  conv_lhs => rw [← Measure.fst_compProd μ (η.comap f hf)]
  rw [Measure.fst, Measure.map_map hf measurable_fst]
  rfl

end CompProd

end ProbabilityTheory
