/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.HasCondDistrib
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd
public import LMLExplore.Probability.Kernel.Composition.IntegralCompProd
public import LMLExplore.Probability.Process.Filtration

/-!
# Conditional distributions: joint masses, integrals and composition-products

If `κ` is the conditional distribution of `Y` given `X` under `P`, then the joint mass of a
rectangle is obtained by integrating the conditional mass: for measurable sets `s` and `t`,
`P(X ∈ s, Y ∈ t) = ∫_{X ∈ s} κ X t dP`, and more generally
`∫_{X ∈ s} g(Y) dP = ∫_{X ∈ s} (∫ g dκ(X)) dP` and `∫ g(X, Y) dP = ∫ (∫ g(X, y) dκ(X)(y)) dP`
for measurable `g ≥ 0`; the last identity characterizes the conditional distribution, and its
Bochner form holds for every integrable `g`. The conditional expectation of `g(X, Y)` given `X` is
then `∫ g(X, y) dκ(X)(y)`, with no assumption on the space of `Y`: the kernel `κ` is given, rather
than obtained from the disintegration theorem as Mathlib's `condDistrib`. The second coordinate of
a composition-product `μ ⊗ₘ η.comap f` has conditional distribution `η` given `f` of the first
coordinate, and conditional distributions under each `κ a` glue into one under `μ ⊗ₘ κ`.

A conditional distribution given a sub-σ-algebra `m` of `Ω` is a conditional distribution given
the identity of `Ω` into `(Ω, m)`, with a kernel from `(Ω, m)`: this is how sequential statements
condition on the past `ℱ k` of a filtration. Conditioning on a random variable is conditioning on
the σ-algebra it generates, so that Mathlib's `condDistrib` provides conditional distributions
given the past of a sequence of observations.

## Main statements

* `ProbabilityTheory.HasCondDistrib.measure_preimage_inter_eq_setLIntegral`:
  `P (X ⁻¹' s ∩ Y ⁻¹' t) = ∫⁻ ω in X ⁻¹' s, κ (X ω) t ∂P`.
* `ProbabilityTheory.HasCondDistrib.setLIntegral_comp_eq_setLIntegral_lintegral`:
  `∫⁻ ω in X ⁻¹' s, g (Y ω) ∂P = ∫⁻ ω in X ⁻¹' s, ∫⁻ y, g y ∂(κ (X ω)) ∂P`.
* `ProbabilityTheory.HasCondDistrib.lintegral_comp_prodMk_eq_lintegral_lintegral`:
  `∫⁻ ω, g (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ y, g (X ω, y) ∂(κ (X ω)) ∂P`.
* `ProbabilityTheory.hasCondDistrib_iff_forall_lintegral_eq`: conversely, this identity for every
  measurable `g ≥ 0` characterizes the conditional distribution.
* `ProbabilityTheory.HasCondDistrib.integral_comp_prodMk_eq_integral_integral`: the Bochner form
  `∫ ω, g (X ω, Y ω) ∂P = ∫ ω, ∫ y, g (X ω, y) ∂(κ (X ω)) ∂P` for integrable `g`.
* `ProbabilityTheory.HasCondDistrib.integrable_comp_prodMk_iff`: `g (X, Y)` is integrable if and
  only if `g` is integrable for the joint law `P.map X ⊗ₘ κ`.
* `ProbabilityTheory.HasCondDistrib.integrable_integral_comp_prodMk`: if `g (X, Y)` is
  integrable, so is the conditional mean `∫ y, g (X, y) ∂(κ X)`.
* `ProbabilityTheory.HasCondDistrib.integrable_and_integral_comp_prodMk_eq_of_ae_integral_eq`:
  if the conditional mean `∫ y, g (X, y) ∂(κ X)` is `G (X)` almost surely and `g (X, Y)` is
  integrable, then so is `G (X)`, with the same mean.
* `ProbabilityTheory.HasCondDistrib.condExp_prod_ae_eq_integral`:
  `P[g (X, Y) | σ(X)] = ∫ y, g (X, y) ∂(κ X)` almost everywhere, for integrable `g`.
* `ProbabilityTheory.HasCondDistrib.restrict_preimage`: `κ` is still the conditional
  distribution of `Y` given `X` under the restriction of `P` to an event `X ⁻¹' s`.
* `ProbabilityTheory.HasCondDistrib.ae_mem`: if every conditional law is concentrated on a set,
  then `Y` lies in that set almost surely.
* `ProbabilityTheory.HasCondDistrib.prodMkLeft_of_comp`: if `Z` has conditional distribution
  `η ∘ₖ κ` given `X` and `f` reads off `Z` the point from which `η` draws it, then `Z` has
  conditional distribution `η (f Z)` given `X` and `f Z`.
* `ProbabilityTheory.hasCondDistrib_snd_compProd_comap`: under `μ ⊗ₘ η.comap f`, the second
  coordinate has conditional distribution `η` given `f` of the first coordinate.
* `ProbabilityTheory.hasCondDistrib_compProd_of_forall_sectR`: if `Y` has conditional
  distribution `η (a, ·)` given `X` under every `κ a`, then under `μ ⊗ₘ κ` the variable `Y` of the
  second coordinate has conditional distribution `η` given the first coordinate and `X`.
* `ProbabilityTheory.HasCondDistrib.of_comp_hasLaw`: a conditional distribution of `Y ∘ f` given
  `X ∘ f` under `P` is one of `Y` given `X` under the law of `f`, the converse of LML's
  `HasCondDistrib.comp_hasLaw`.
* `ProbabilityTheory.hasCondDistrib_id_of_measure_inter_preimage`: a kernel `η` from `(Ω, m)`
  with `P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, η ω t ∂P` on rectangles is a conditional distribution of `X`
  given the identity of `Ω` into `(Ω, m)`, that is, given the σ-algebra `m`.
* `ProbabilityTheory.hasCondDistrib_id_const_of_indep`: a random variable independent of `m` has
  its law as constant conditional distribution given `m`.
* `ProbabilityTheory.HasCondDistrib.id_of_le_comap`: a conditional distribution `η` given a random
  variable `R` gives the conditional distribution `η.comap R` given the σ-algebra of `R`.
* `ProbabilityTheory.hasCondDistrib_piLT_condDistrib`: on sequences in a standard Borel space,
  `condDistrib` of a coordinate given the previous ones is a conditional distribution given
  `Filtration.piLT`.
* `ProbabilityTheory.HasCondDistrib.condExp_id_ae_eq_integral`: given a σ-algebra `m`,
  `P[f (X) | m] = ∫ f dη` almost everywhere, for integrable `f (X)`.

`hasCondDistrib_snd_compProd_comap` is adapted from the LMLPapers project (same author). The
characterization, the Bochner integral, the conditional expectation,
`HasCondDistrib.restrict_preimage`, the gluing over `μ ⊗ₘ κ` and the transport by a law are
adapted from the Essakine2026Tight project
(`RemyDegenne/Essakine2026Tight`, Apache 2.0, files `HasCondDistribIntegral.lean`,
`HasCondDistribCondExp.lean` and `CondDistrib.lean` of `ForLMLExplore/Probability/`).
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

/-- If `κ` is the conditional distribution of `Y` given `X`, then for a measurable function
`g ≥ 0` of both, `∫ g(X, Y) dP = ∫ (∫ g(X, y) dκ(X)(y)) dP`. -/
lemma HasCondDistrib.lintegral_comp_prodMk_eq_lintegral_lintegral (h : HasCondDistrib Y X κ P)
    {g : 𝓧 × 𝓨 → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ y, g (X ω, y) ∂(κ (X ω)) ∂P := by
  calc ∫⁻ ω, g (X ω, Y ω) ∂P
      = ∫⁻ p, g p ∂(P.map (fun ω ↦ (X ω, Y ω))) :=
        (lintegral_map' hg.aemeasurable h.aemeasurable).symm
    _ = ∫⁻ p, g p ∂(P.map X ⊗ₘ κ) := by rw [h.map_eq]
    _ = ∫⁻ x, ∫⁻ y, g (x, y) ∂(κ x) ∂(P.map X) := Measure.lintegral_compProd hg
    _ = ∫⁻ ω, ∫⁻ y, g (X ω, y) ∂(κ (X ω)) ∂P :=
        lintegral_map' hg.lintegral_kernel_prod_right'.aemeasurable h.aemeasurable_fst

/-- A kernel `κ` is the conditional distribution of `Y` given `X` if and only if, for every
measurable function `g ≥ 0` of both, `∫ g(X, Y) dP = ∫ (∫ g(X, y) dκ(X)(y)) dP`. -/
lemma hasCondDistrib_iff_forall_lintegral_eq (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    HasCondDistrib Y X κ P ↔ ∀ g : 𝓧 × 𝓨 → ℝ≥0∞, Measurable g →
      ∫⁻ ω, g (X ω, Y ω) ∂P = ∫⁻ ω, ∫⁻ y, g (X ω, y) ∂(κ (X ω)) ∂P := by
  refine ⟨fun h g hg ↦ h.lintegral_comp_prodMk_eq_lintegral_lintegral hg,
    fun h ↦ ⟨hX.prodMk hY, Measure.ext_of_lintegral _ fun g hg ↦ ?_⟩⟩
  rw [lintegral_map' hg.aemeasurable (hX.prodMk hY), h g hg, Measure.lintegral_compProd hg,
    lintegral_map' hg.lintegral_kernel_prod_right'.aemeasurable hX]

/-- If `κ` is the conditional distribution of `Y` given `X`, then for a function `g` of both,
integrable for the joint law, `∫ g(X, Y) dP = ∫ (∫ g(X, y) dκ(X)(y)) dP`. -/
lemma HasCondDistrib.integral_comp_prodMk_eq_integral_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : HasCondDistrib Y X κ P) {g : 𝓧 × 𝓨 → E}
    (hg : Integrable g (P.map X ⊗ₘ κ)) :
    ∫ ω, g (X ω, Y ω) ∂P = ∫ ω, ∫ y, g (X ω, y) ∂(κ (X ω)) ∂P := by
  calc ∫ ω, g (X ω, Y ω) ∂P
      = ∫ p, g p ∂(P.map X ⊗ₘ κ) := h.integral_comp hg.aestronglyMeasurable
    _ = ∫ x, ∫ y, g (x, y) ∂(κ x) ∂(P.map X) := Measure.integral_compProd hg
    _ = ∫ ω, ∫ y, g (X ω, y) ∂(κ (X ω)) ∂P :=
        integral_map h.aemeasurable_fst hg.integral_measure_compProd.aestronglyMeasurable

omit [SFinite P] [IsSFiniteKernel κ] in
/-- If `κ` is the conditional distribution of `Y` given `X`, then a function `g` of both that is
a.e.-strongly measurable for the joint law `P.map X ⊗ₘ κ` is integrable for the joint law if and
only if `g (X, Y)` is integrable. -/
lemma HasCondDistrib.integrable_comp_prodMk_iff {E : Type*} [NormedAddCommGroup E]
    (h : HasCondDistrib Y X κ P) {g : 𝓧 × 𝓨 → E} (hg : AEStronglyMeasurable g (P.map X ⊗ₘ κ)) :
    Integrable (fun ω ↦ g (X ω, Y ω)) P ↔ Integrable g (P.map X ⊗ₘ κ) := by
  rw [← h.map_eq] at hg ⊢
  exact (integrable_map_measure hg h.aemeasurable).symm

/-- If `κ` is the conditional distribution of `Y` given `X` and `g (X, Y)` is integrable, for a
function `g` of both that is a.e.-strongly measurable for the joint law `P.map X ⊗ₘ κ`, then the
conditional mean `ω ↦ ∫ g (X ω, y) dκ(X ω)(y)` is integrable. -/
lemma HasCondDistrib.integrable_integral_comp_prodMk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (h : HasCondDistrib Y X κ P) {g : 𝓧 × 𝓨 → E}
    (hg : AEStronglyMeasurable g (P.map X ⊗ₘ κ)) (hint : Integrable (fun ω ↦ g (X ω, Y ω)) P) :
    Integrable (fun ω ↦ ∫ y, g (X ω, y) ∂(κ (X ω))) P :=
  ((h.integrable_comp_prodMk_iff hg).1 hint).integral_measure_compProd.comp_aemeasurable
    h.aemeasurable_fst

/-- If `κ` is the conditional distribution of `Y` given `X`, the conditional mean
`∫ y, g (X ω, y) ∂(κ (X ω))` equals `G (X ω)` for almost every `ω`, and `g (X, Y)` is integrable,
for a function `g` of both that is a.e.-strongly measurable for the joint law `P.map X ⊗ₘ κ`, then
`G (X)` is integrable, with the same mean as `g (X, Y)`. -/
lemma HasCondDistrib.integrable_and_integral_comp_prodMk_eq_of_ae_integral_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (h : HasCondDistrib Y X κ P) {g : 𝓧 × 𝓨 → E}
    (hg : AEStronglyMeasurable g (P.map X ⊗ₘ κ)) {G : 𝓧 → E}
    (hG : ∀ᵐ ω ∂P, ∫ y, g (X ω, y) ∂(κ (X ω)) = G (X ω))
    (hint : Integrable (fun ω ↦ g (X ω, Y ω)) P) :
    Integrable (fun ω ↦ G (X ω)) P ∧ ∫ ω, g (X ω, Y ω) ∂P = ∫ ω, G (X ω) ∂P := by
  refine ⟨(h.integrable_integral_comp_prodMk hg hint).congr hG, ?_⟩
  rw [h.integral_comp_prodMk_eq_integral_integral ((h.integrable_comp_prodMk_iff hg).1 hint)]
  exact integral_congr_ae hG

omit [IsSFiniteKernel κ] in
/-- If `κ` is the conditional distribution of `Y` given `X` under `P`, it is also the conditional
distribution of `Y` given `X` under the restriction of `P` to an event `X ⁻¹' s` determined by
`X`. -/
lemma HasCondDistrib.restrict_preimage (h : HasCondDistrib Y X κ P) {s : Set 𝓧}
    (hs : MeasurableSet s) :
    HasCondDistrib Y X κ (P.restrict (X ⁻¹' s)) := by
  refine ⟨h.aemeasurable.restrict, ?_⟩
  have h_pre : (fun ω ↦ (X ω, Y ω)) ⁻¹' (s ×ˢ Set.univ) = X ⁻¹' s := by
    rw [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]
  calc (P.restrict (X ⁻¹' s)).map (fun ω ↦ (X ω, Y ω))
      = (P.map (fun ω ↦ (X ω, Y ω))).restrict (s ×ˢ Set.univ) := by
        rw [Measure.restrict_map_of_aemeasurable h.aemeasurable (hs.prod .univ), h_pre]
    _ = (P.map X).restrict s ⊗ₘ κ := by
        rw [h.map_eq, Measure.compProd_restrict_left _ _ hs]
    _ = (P.restrict (X ⁻¹' s)).map X ⊗ₘ κ := by
        rw [Measure.restrict_map_of_aemeasurable h.aemeasurable_fst hs]

omit [SFinite P] [IsSFiniteKernel κ] in
/-- If `κ` is the conditional distribution of `Y` given `X` and every measure `κ x` is concentrated
on a measurable set `t`, then `Y` lies in `t` almost surely. -/
lemma HasCondDistrib.ae_mem (h : HasCondDistrib Y X κ P) {t : Set 𝓨} (ht : MeasurableSet t)
    (hκ : ∀ x, ∀ᵐ y ∂(κ x), y ∈ t) :
    ∀ᵐ ω ∂P, Y ω ∈ t := by
  have h_ae : ∀ᵐ q ∂(P.map X ⊗ₘ κ), q.2 ∈ t :=
    Measure.ae_compProd_of_ae_ae (ht.preimage measurable_snd) (.of_forall hκ)
  rw [← h.map_eq] at h_ae
  exact ae_of_ae_map h.aemeasurable h_ae

omit [SFinite P] [IsSFiniteKernel κ] in
/-- A conditional distribution under a nonzero measure is an s-finite kernel: for any other kernel
the joint law `P.map X ⊗ₘ κ` vanishes, and so does `P`. -/
lemma HasCondDistrib.isSFiniteKernel [NeZero P] (h : HasCondDistrib Y X κ P) :
    IsSFiniteKernel κ := by
  by_contra hκ
  refine NeZero.ne P ?_
  rw [← Measure.map_eq_zero_iff h.aemeasurable, h.map_eq,
    Measure.compProd_of_not_isSFiniteKernel _ _ hκ]

end JointMass

section Comp

variable {Ω α β γ : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {P : Measure Ω} [SFinite P] {X : Ω → α}
  {Z : Ω → γ}

/-- Let `Z` have conditional distribution `η ∘ₖ κ` given `X`: a point `b` is drawn from `κ X`,
then `Z` from `η b`. If `f` reads `b` off `Z`, in the sense that `η.map (fun z ↦ (f z, z))` is
`Kernel.id ×ₖ η` (the joint-law form of `f z = b` for `η b`-almost every `z`, which needs no
measurable singletons), then `Z` has conditional distribution `η (f Z)` given `X` and `f Z`. -/
lemma HasCondDistrib.prodMkLeft_of_comp {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel β γ}
    [IsMarkovKernel η] {f : γ → β} (hf : Measurable f)
    (hη : η.map (fun z ↦ (f z, z)) = Kernel.id ×ₖ η) (h : HasCondDistrib Z X (η ∘ₖ κ) P) :
    HasCondDistrib Z (fun ω ↦ (X ω, f (Z ω))) (Kernel.prodMkLeft α η) P := by
  have h2 := h.comp_left (f := fun z ↦ (f z, z)) (by fun_prop)
  rw [Kernel.map_comp, hη, ← Kernel.compProd_prodMkLeft_eq_comp] at h2
  exact h2.of_compProd

end Comp

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

variable {δ : Type*} {mδ : MeasurableSpace δ}

/-- If `Y` has conditional distribution `η.sectR a = η (a, ·)` given `X` under every `κ a`, then
under `μ ⊗ₘ κ` the variable `Y` of the second coordinate has conditional distribution `η` given
the first coordinate and `X` of the second. -/
lemma hasCondDistrib_compProd_of_forall_sectR {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsSFiniteKernel κ] {X : β → γ} {Y : β → δ} {η : Kernel (α × γ) δ} [IsSFiniteKernel η]
    (hX : Measurable X) (hY : Measurable Y) (h : ∀ a, HasCondDistrib Y X (η.sectR a) (κ a)) :
    HasCondDistrib (fun p ↦ Y p.2) (fun p ↦ (p.1, X p.2)) η (μ ⊗ₘ κ) := by
  refine (hasCondDistrib_iff_forall_lintegral_eq (by fun_prop) (by fun_prop)).mpr fun g hg ↦ ?_
  rw [Measure.lintegral_compProd (f := fun p ↦ g ((p.1, X p.2), Y p.2)) (by fun_prop),
    Measure.lintegral_compProd (f := fun p ↦ ∫⁻ y, g ((p.1, X p.2), y) ∂η (p.1, X p.2))
      (hg.lintegral_kernel_prod_right'.comp (by fun_prop))]
  refine lintegral_congr fun a ↦ ?_
  simpa using (h a).lintegral_comp_prodMk_eq_lintegral_lintegral
    (g := fun q ↦ g ((a, q.1), q.2)) (by fun_prop)

end CompProd

section Transport

variable {Ω Ω' 𝓧 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {P' : Measure Ω'}
  {f : Ω → Ω'} {X : Ω' → 𝓧} {Y : Ω' → 𝓨} {κ : Kernel 𝓧 𝓨}

/-- If `Y ∘ f` has conditional distribution `κ` given `X ∘ f` under `P` and `f` has law `P'`
under `P`, then `Y` has conditional distribution `κ` given `X` under `P'`. This is the converse
of LML's `HasCondDistrib.comp_hasLaw`. -/
lemma HasCondDistrib.of_comp_hasLaw (h : HasCondDistrib (Y ∘ f) (X ∘ f) κ P) (hf : HasLaw f P' P)
    (hX : AEMeasurable X P') (hY : AEMeasurable Y P') :
    HasCondDistrib Y X κ P' := by
  refine ⟨hX.prodMk hY, ?_⟩
  rw [← hf.map_eq, AEMeasurable.map_map_of_aemeasurable (hf.map_eq ▸ hX.prodMk hY) hf.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (hf.map_eq ▸ hX) hf.aemeasurable]
  exact h.map_eq

end Transport

section CondExp

variable {Ω 𝓧 𝓨 E : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨}
  [IsSFiniteKernel κ]

/-- If `κ` is the conditional distribution of `Y` given `X`, then for a function `g` of both,
integrable for the joint law, `𝔼[g(X, Y) | σ(X)] = ∫ g(X, y) dκ(X)(y)` almost everywhere.
Unlike Mathlib's `condExp_prod_ae_eq_integral_condDistrib'`, this needs no standard Borel
assumption on the space of `Y`; it generalizes LML's `HasCondDistrib.condExp_comp_ae_eq` to
functions of `(X, Y)`, on any measurable space. -/
lemma HasCondDistrib.condExp_prod_ae_eq_integral (h : HasCondDistrib Y X κ P) (hX : Measurable X)
    {g : 𝓧 × 𝓨 → E} (hg : Integrable g (P.map X ⊗ₘ κ)) :
    P[fun ω ↦ g (X ω, Y ω) | m𝓧.comap X] =ᵐ[P] fun ω ↦ ∫ y, g (X ω, y) ∂(κ (X ω)) := by
  have hg' := hg.integral_measure_compProd
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le (h.integrable_comp hg)
    (fun _ _ _ ↦ (hg'.comp_aemeasurable hX.aemeasurable).integrableOn) ?_
    (hg'.aestronglyMeasurable.comp_ae_measurable' hX.aemeasurable)).symm
  rintro _ ⟨t, ht, rfl⟩ _
  -- Both set integrals over `X ⁻¹' t` are integrals of `g` restricted to `t ×ˢ univ`.
  rw [← integral_indicator (hX ht), ← integral_indicator (hX ht)]
  convert (h.integral_comp_prodMk_eq_integral_integral (hg.indicator (ht.prod .univ))).symm
    using 1
  all_goals
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    by_cases hω : X ω ∈ t <;> simp [hω]

end CondExp

section SubSigmaAlgebra

/-! ### Conditional distributions given a σ-algebra

A conditional distribution of `X` given a sub-σ-algebra `m` of `Ω` is a conditional distribution
`HasCondDistrib X id κ P` given the identity of `Ω` into `(Ω, m)`, with `κ` a kernel from
`(Ω, m)`. -/

variable {Ω 𝓧 𝓨 : Type*} {m mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧}
  {m𝓨 : MeasurableSpace 𝓨} {P : Measure Ω} {X : Ω → 𝓧}

/-- **A conditional distribution given a σ-algebra from its values on rectangles.** If `η` is an
s-finite kernel from `(Ω, m)` and `P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, η ω t ∂P` for every
`m`-measurable `s` and measurable `t`, then `η` is a conditional distribution of `X` given `m`
under the finite measure `P`. -/
lemma hasCondDistrib_id_of_measure_inter_preimage [IsFiniteMeasure P] (hm : m ≤ mΩ)
    (hX : AEMeasurable X P) {η : Kernel[m] Ω 𝓧} [IsSFiniteKernel η]
    (h : ∀ s t, MeasurableSet[m] s → MeasurableSet t → P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, η ω t ∂P) :
    HasCondDistrib (m𝓧 := m) X id η P := by
  -- the σ-algebra on `Ω × 𝓧` is the one built from `m`, not from `mΩ`
  let : MeasurableSpace (Ω × 𝓧) := m.prod m𝓧
  have hΦ : AEMeasurable (fun ω ↦ (id ω, X ω)) P :=
    ⟨fun ω ↦ (ω, hX.mk X ω), (measurable_id'' hm).prodMk hX.measurable_mk,
      hX.ae_eq_mk.mono fun ω hω ↦ by simp only [id, hω]⟩
  refine ⟨hΦ, ?_⟩
  rw [← trim_eq_map hm]
  refine Measure.ext_prod fun {s t} hs ht ↦ ?_
  rw [Measure.map_apply_of_aemeasurable hΦ (hs.prod ht), Measure.compProd_apply_prod hs ht,
    Set.mk_preimage_prod, Set.preimage_id, h s t hs ht,
    setLIntegral_trim hm (η.measurable_coe ht) hs]

/-- **Independence gives a constant conditional distribution.** If `X` is independent of the
sub-σ-algebra `m` under a finite measure `P` and has law `ν`, then the constant kernel `ν` is a
conditional distribution of `X` given `m`. -/
lemma hasCondDistrib_id_const_of_indep [IsFiniteMeasure P] (hm : m ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X m𝓧) m P) {ν : Measure 𝓧} (hlaw : HasLaw X ν P) :
    HasCondDistrib (m𝓧 := m) X id (@Kernel.const Ω 𝓧 m _ ν) P := by
  have : IsFiniteMeasure ν := hlaw.map_eq ▸ inferInstance
  refine IndepFun.hasCondDistrib_const (mβ := m) ?_ ⟨id, measurable_id'' hm, .rfl⟩ hlaw
  rw [IndepFun_iff_Indep (mβ := m), MeasurableSpace.comap_id]
  exact hind.symm

/-- **Conditioning on a random variable is conditioning on the σ-algebra it generates.** If `η` is
a conditional distribution of `X` given `R`, then `η.comap R` is a conditional distribution of `X`
given every sub-σ-algebra `m` for which `R` is measurable and which `R` generates. -/
lemma HasCondDistrib.id_of_le_comap [IsFiniteMeasure P] {R : Ω → 𝓨} {η : Kernel 𝓨 𝓧}
    [IsSFiniteKernel η] (h : HasCondDistrib X R η P) (hm : m ≤ mΩ) (hR : Measurable[m] R)
    (hmR : m ≤ m𝓨.comap R) :
    HasCondDistrib (m𝓧 := m) X id (η.comap R hR) P :=
  hasCondDistrib_id_of_measure_inter_preimage hm h.aemeasurable_snd fun s t hs ht ↦ by
    obtain ⟨s', hs', rfl⟩ := hmR s hs
    exact h.measure_preimage_inter_eq_setLIntegral hs' ht

/-- **The conditional law of a coordinate given the strict past.** For a finite measure `P` on
sequences in a standard Borel space, Mathlib's `condDistrib` of the coordinate `ω k` given the
first `k` coordinates `initSeg k ω`, composed with `initSeg k`, is a conditional distribution of
`ω k` given time `k` of the filtration `Filtration.piLT` of the strict past. -/
lemma hasCondDistrib_piLT_condDistrib [StandardBorelSpace 𝓧] [Nonempty 𝓧]
    (P : Measure (ℕ → 𝓧)) [IsFiniteMeasure P] (k : ℕ) :
    HasCondDistrib (m𝓧 := Filtration.piLT k) (fun ω ↦ ω k) id
      ((condDistrib (fun ω ↦ ω k) (initSeg k) P).comap (initSeg k)
        (Filtration.measurable_piLT_initSeg le_rfl)) P :=
  (hasCondDistrib_of_condDistrib_ae_eq (measurable_initSeg k).aemeasurable
      (measurable_pi_apply k).aemeasurable .rfl).id_of_le_comap (Filtration.le _ k) _
    (Filtration.piLT_eq_comap_initSeg k).le

section Integral

variable {E : Type*} [NormedAddCommGroup E] {η : Kernel[m] Ω 𝓧} [IsSFiniteKernel η]
  {f : 𝓧 → E}

/-- **Integrability under a conditional distribution given a σ-algebra.** If the s-finite kernel
`η` from `(Ω, m)` is a conditional distribution of `X` given `m` and `f (X)` is integrable, then
`f` is `η ω`-integrable for almost every `ω`. -/
lemma HasCondDistrib.ae_integrable_id [SFinite P] (hm : m ≤ mΩ)
    (h : HasCondDistrib (m𝓧 := m) X id η P) (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω ↦ f (X ω)) P) :
    ∀ᵐ ω ∂P, Integrable f (η ω) := by
  have hg := (hf.comp_measurable (@measurable_snd Ω 𝓧 m m𝓧)).aestronglyMeasurable
    (μ := @Measure.map Ω Ω mΩ m id P ⊗ₘ η)
  exact ae_of_ae_map ⟨id, measurable_id'' hm, .rfl⟩
    ((Measure.integrable_compProd_iff hg).1 ((h.integrable_comp_prodMk_iff hg).1 hint)).1

/-- **Conditional expectations given a σ-algebra.** If the s-finite kernel `η` from `(Ω, m)` is a
conditional distribution of `X` given `m` under the finite measure `P` and `f (X)` is integrable,
then `P[f (X) | m] = ∫ f dη ω` almost everywhere. This is the case of the identity of `Ω` into
`(Ω, m)` and of a function of `X` alone of `HasCondDistrib.condExp_prod_ae_eq_integral`. -/
lemma HasCondDistrib.condExp_id_ae_eq_integral [NormedSpace ℝ E] [CompleteSpace E]
    [IsFiniteMeasure P] (hm : m ≤ mΩ) (h : HasCondDistrib (m𝓧 := m) X id η P)
    (hf : StronglyMeasurable f) (hint : Integrable (fun ω ↦ f (X ω)) P) :
    P[fun ω ↦ f (X ω) | m] =ᵐ[P] fun ω ↦ ∫ x, f x ∂(η ω) := by
  have hg := (hf.comp_measurable (@measurable_snd Ω 𝓧 m m𝓧)).aestronglyMeasurable
    (μ := @Measure.map Ω Ω mΩ m id P ⊗ₘ η)
  have := h.condExp_prod_ae_eq_integral (measurable_id'' hm)
    ((h.integrable_comp_prodMk_iff hg).1 hint)
  simpa only [MeasurableSpace.comap_id, id, Function.comp_apply] using this

end Integral

end SubSigmaAlgebra

end ProbabilityTheory
