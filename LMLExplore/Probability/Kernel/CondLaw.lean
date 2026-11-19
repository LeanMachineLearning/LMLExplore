/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Conditional laws given a σ-algebra

A family `κ : Ω → Measure 𝓧` is a *conditional law* of a random variable `X : Ω → 𝓧` given a
sub-σ-algebra `m` under `P` (`ProbabilityTheory.HasCondLaw`) when, for every function
`g : Ω → 𝓧 → ℝ≥0∞` measurable for `m` and the σ-algebra of `𝓧` jointly,
`∫⁻ ω, g ω (X ω) ∂P = ∫⁻ ω, ∫⁻ x, g ω x ∂(κ ω) ∂P`: integrating `X` against a function that may
also depend on the information in `m` amounts to integrating it out against `κ` with that
information frozen. This is the form in which sequential statements use the conditional law of
an observation given the past: no measurability of `κ` in `ω`, no regularity of `𝓧` and no
integrability are assumed. Mathlib's `HasCondDistrib` conditions on a random variable rather
than on a σ-algebra.

## Main statements

* `ProbabilityTheory.HasCondLaw.setLIntegral_comp`: the identity on every `m`-measurable set.
* `ProbabilityTheory.HasCondLaw.congr`: conditional laws are invariant under almost everywhere
  equality of the random variable.
* `ProbabilityTheory.HasCondLaw.setLIntegral_measure_univ`: the total masses integrate to `P` on
  `m`-measurable sets, `∫⁻ ω in s, κ ω univ ∂P = P s`.
* `ProbabilityTheory.HasCondLaw.measure_inter_preimage`: the identity on `m`-measurable
  rectangles, `P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, κ ω t ∂P`.
* `ProbabilityTheory.hasCondLaw_of_measure_inter_preimage`: conversely, an `m`-measurable s-finite
  kernel satisfying the identity on rectangles is a conditional law of `X` given `m`.
* `ProbabilityTheory.hasCondLaw_of_indep`: a random variable independent of `m`, of law `ν`, has
  the constant conditional law `ν` given `m`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  {X : Ω → 𝓧} {κ : Ω → Measure 𝓧}

/-- `κ` is a conditional law of `X` given the σ-algebra `m` under `P`: for every
`g : Ω → 𝓧 → ℝ≥0∞` measurable for `m` and the σ-algebra of `𝓧` jointly,
`∫⁻ ω, g ω (X ω) ∂P = ∫⁻ ω, ∫⁻ x, g ω x ∂(κ ω) ∂P`. -/
structure HasCondLaw (X : Ω → 𝓧) (κ : Ω → Measure 𝓧) (m : MeasurableSpace Ω)
    (P : @Measure Ω mΩ) : Prop where
  lintegral_comp : ∀ g : Ω → 𝓧 → ℝ≥0∞, Measurable[m.prod m𝓧] (Function.uncurry g) →
    ∫⁻ ω, g ω (X ω) ∂P = ∫⁻ ω, ∫⁻ x, g ω x ∂(κ ω) ∂P

/-- The identity defining a conditional law given `m`, on an `m`-measurable set `s`:
`∫⁻ ω in s, g ω (X ω) ∂P = ∫⁻ ω in s, ∫⁻ x, g ω x ∂(κ ω) ∂P`. -/
theorem HasCondLaw.setLIntegral_comp (h : HasCondLaw X κ m P) (hm : m ≤ mΩ)
    {g : Ω → 𝓧 → ℝ≥0∞} (hg : Measurable[m.prod m𝓧] (Function.uncurry g)) {s : Set Ω}
    (hs : MeasurableSet[m] s) :
    ∫⁻ ω in s, g ω (X ω) ∂P = ∫⁻ ω in s, ∫⁻ x, g ω x ∂(κ ω) ∂P := by
  classical
  have hg' : Measurable[m.prod m𝓧]
      (Function.uncurry fun ω x ↦ s.indicator (fun ω' ↦ g ω' x) ω) := by
    have : (Function.uncurry fun ω x ↦ s.indicator (fun ω' ↦ g ω' x) ω) =
        (s ×ˢ univ).indicator (Function.uncurry g) := by
      ext ⟨ω, x⟩
      by_cases hω : ω ∈ s <;> simp [hω]
    rw [this]
    exact hg.indicator (hs.prod MeasurableSet.univ)
  calc ∫⁻ ω in s, g ω (X ω) ∂P
      = ∫⁻ ω, s.indicator (fun ω' ↦ g ω' (X ω)) ω ∂P := by
        rw [← lintegral_indicator (hm s hs)]
        refine lintegral_congr fun ω ↦ ?_
        by_cases hω : ω ∈ s <;> simp [hω]
    _ = ∫⁻ ω, ∫⁻ x, s.indicator (fun ω' ↦ g ω' x) ω ∂(κ ω) ∂P := h.lintegral_comp _ hg'
    _ = ∫⁻ ω in s, ∫⁻ x, g ω x ∂(κ ω) ∂P := by
        rw [← lintegral_indicator (hm s hs)]
        refine lintegral_congr fun ω ↦ ?_
        by_cases hω : ω ∈ s <;> simp [hω]

/-- A conditional law of `X` given `m` is a conditional law of every random variable that agrees
with `X` almost everywhere. -/
theorem HasCondLaw.congr (h : HasCondLaw X κ m P) {Y : Ω → 𝓧} (hXY : X =ᵐ[P] Y) :
    HasCondLaw Y κ m P where
  lintegral_comp g hg := by
    rw [← h.lintegral_comp g hg]
    exact lintegral_congr_ae (hXY.mono fun ω hω ↦ by simp only [hω])

/-- **Total mass of a conditional law.** If `κ` is a conditional law of `X` given `m` under `P`,
then on every `m`-measurable set `s`, `∫⁻ ω in s, κ ω univ ∂P = P s`. No measurability of `X` is
needed. -/
theorem HasCondLaw.setLIntegral_measure_univ (h : HasCondLaw X κ m P) (hm : m ≤ mΩ) {s : Set Ω}
    (hs : MeasurableSet[m] s) :
    ∫⁻ ω in s, κ ω univ ∂P = P s := by
  simpa only [lintegral_one, Measure.restrict_apply_univ] using
    (h.setLIntegral_comp hm (g := fun _ _ ↦ 1) measurable_const hs).symm

/-- The identity defining a conditional law given `m`, on `m`-measurable rectangles:
`P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, κ ω t ∂P`. -/
theorem HasCondLaw.measure_inter_preimage (h : HasCondLaw X κ m P) (hm : m ≤ mΩ)
    (hX : AEMeasurable X P) {s : Set Ω} (hs : MeasurableSet[m] s) {t : Set 𝓧}
    (ht : MeasurableSet t) :
    P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, κ ω t ∂P := by
  have hg : Measurable[m.prod m𝓧]
      (Function.uncurry fun (_ : Ω) x ↦ t.indicator (1 : 𝓧 → ℝ≥0∞) x) :=
    (measurable_one.indicator ht).comp measurable_snd
  have h' := h.setLIntegral_comp hm hg hs
  simp_rw [lintegral_indicator_one ht] at h'
  rw [← h', inter_comm, ← Measure.restrict_apply' (hm s hs),
    ← lintegral_indicator_one₀ (hX.restrict.nullMeasurableSet_preimage ht)]
  simp only [← indicator_comp_right, Pi.one_comp]

/-- **A conditional law from its values on rectangles.** If `η` is an `m`-measurable s-finite
kernel and `P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, η ω t ∂P` for every `m`-measurable `s` and measurable
`t`, then `η` is a conditional law of `X` given `m` under the finite measure `P`. -/
theorem hasCondLaw_of_measure_inter_preimage [IsFiniteMeasure P] (hm : m ≤ mΩ)
    (hX : AEMeasurable X P) {η : Kernel[m] Ω 𝓧} [IsSFiniteKernel η]
    (h : ∀ s t, MeasurableSet[m] s → MeasurableSet t → P (s ∩ X ⁻¹' t) = ∫⁻ ω in s, η ω t ∂P) :
    HasCondLaw X η m P := by
  -- the product σ-algebra on `Ω × 𝓧` is the one built from `m`, not from `mΩ`
  let : MeasurableSpace (Ω × 𝓧) := m.prod m𝓧
  have hΦ : AEMeasurable (fun ω ↦ (ω, X ω)) P :=
    ⟨fun ω ↦ (ω, hX.mk X ω), (measurable_id'' hm).prodMk hX.measurable_mk,
      hX.ae_eq_mk.mono fun ω hω ↦ by simp only [hω]⟩
  -- the joint law of the information in `m` and of `X` is `P.trim hm ⊗ₘ η`
  have hmap : P.map (fun ω ↦ (ω, X ω)) = P.trim hm ⊗ₘ η := by
    refine Measure.ext_prod fun {s t} hs ht ↦ ?_
    rw [Measure.map_apply_of_aemeasurable hΦ (hs.prod ht), Measure.compProd_apply_prod hs ht,
      mk_preimage_prod, preimage_id', h s t hs ht,
      setLIntegral_trim hm (η.measurable_coe ht) hs]
  refine ⟨fun g hg ↦ ?_⟩
  calc ∫⁻ ω, g ω (X ω) ∂P
      = ∫⁻ p, Function.uncurry g p ∂(P.map fun ω ↦ (ω, X ω)) :=
        (lintegral_map' hg.aemeasurable hΦ).symm
    _ = ∫⁻ ω, ∫⁻ x, g ω x ∂(η ω) ∂(P.trim hm) := by
        rw [hmap, Measure.lintegral_compProd hg]
        simp only [Function.uncurry_apply_pair]
    _ = ∫⁻ ω, ∫⁻ x, g ω x ∂(η ω) ∂P :=
        lintegral_trim hm (hg.lintegral_kernel_prod_right' (κ := η))

/-- **A random variable independent of `m` has its law as conditional law given `m`.** If `X` is
independent of the sub-σ-algebra `m` under a finite measure `P` and has law `ν`, then the constant
family `ν` is a conditional law of `X` given `m`. -/
theorem hasCondLaw_of_indep [IsFiniteMeasure P] (hm : m ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X m𝓧) m P) {ν : Measure 𝓧} (hlaw : HasLaw X ν P) :
    HasCondLaw X (fun _ ↦ ν) m P := by
  have hν : IsFiniteMeasure ν := by
    rw [← hlaw.map_eq]
    infer_instance
  refine hasCondLaw_of_measure_inter_preimage (η := @Kernel.const _ _ m _ ν) hm hlaw.aemeasurable
    fun s t hs ht ↦ ?_
  calc P (s ∩ X ⁻¹' t)
      = P s * ν t := by
        rw [(Indep_iff _ _ _).1 hind.symm s (X ⁻¹' t) hs ⟨t, ht, rfl⟩, ← hlaw.map_eq,
          Measure.map_apply_of_aemeasurable hlaw.aemeasurable ht]
    _ = ∫⁻ _ in s, ν t ∂P := by rw [setLIntegral_const, mul_comm]

end ProbabilityTheory
