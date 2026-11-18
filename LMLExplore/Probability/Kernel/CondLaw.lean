/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

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

/-- **A random variable independent of `m` has its law as conditional law given `m`.** If `X` is
independent of the sub-σ-algebra `m` under a finite measure `P` and has law `ν`, then the constant
family `ν` is a conditional law of `X` given `m`. -/
theorem hasCondLaw_of_indep [IsFiniteMeasure P] (hm : m ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X m𝓧) m P) {ν : Measure 𝓧} (hlaw : HasLaw X ν P) :
    HasCondLaw X (fun _ ↦ ν) m P := by
  have hν : IsFiniteMeasure ν := by
    rw [← hlaw.map_eq]
    infer_instance
  -- `id` is measurable from `mΩ` to `m`; the σ-algebra on its codomain is `m`, not `mΩ`
  have hid : @AEMeasurable Ω Ω m mΩ id P := ⟨id, measurable_id'' hm, ae_eq_refl _⟩
  have hΦ : @AEMeasurable Ω (Ω × 𝓧) (m.prod m𝓧) mΩ (fun ω ↦ (ω, X ω)) P :=
    @AEMeasurable.prodMk Ω Ω 𝓧 mΩ m m𝓧 P id X hid hlaw.aemeasurable
  -- the joint law of the information in `m` and of `X` is the product of their laws
  have hmap : @Measure.map Ω (Ω × 𝓧) mΩ (m.prod m𝓧) (fun ω ↦ (ω, X ω)) P =
      @Measure.prod Ω 𝓧 m m𝓧 (P.trim hm) ν := by
    refine (@Measure.prod_eq Ω 𝓧 m m𝓧 (P.trim hm) _ ν _ _ fun s t hs ht ↦ ?_).symm
    rw [@Measure.map_apply_of_aemeasurable Ω (Ω × 𝓧) mΩ (m.prod m𝓧) _ _ hΦ _ (hs.prod ht),
      mk_preimage_prod, preimage_id', trim_measurableSet_eq hm hs, ← hlaw.map_eq,
      Measure.map_apply_of_aemeasurable hlaw.aemeasurable ht]
    exact (Indep_iff _ _ _).1 hind.symm s (X ⁻¹' t) hs ⟨t, ht, rfl⟩
  refine ⟨fun g hg ↦ ?_⟩
  calc ∫⁻ ω, g ω (X ω) ∂P
      = ∫⁻ p, Function.uncurry g p ∂(@Measure.map Ω (Ω × 𝓧) mΩ (m.prod m𝓧)
          (fun ω ↦ (ω, X ω)) P) :=
        (@lintegral_map' Ω (Ω × 𝓧) mΩ (m.prod m𝓧) P _ _ hg.aemeasurable hΦ).symm
    _ = ∫⁻ ω, ∫⁻ x, g ω x ∂ν ∂(P.trim hm) := by
        rw [hmap]
        exact @lintegral_prod Ω 𝓧 m m𝓧 (P.trim hm) ν _ _ hg.aemeasurable
    _ = ∫⁻ ω, ∫⁻ x, g ω x ∂ν ∂P :=
        lintegral_trim hm (@Measurable.lintegral_prod_right' Ω 𝓧 m m𝓧 ν _ _ hg)

end ProbabilityTheory
