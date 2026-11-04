/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Lower Lebesgue integrals against an upper bound of a conditional expectation

Let `f ≥ 0` be integrable with conditional expectation `μ[f | m] ≤ h` given a sub-σ-algebra `m`.
Integrating `f` against an `m`-measurable weight `g ≥ 0` is integrating `μ[f | m]` against `g`,
so `∫⁻ g * f ≤ ∫⁻ g * h`. The integrals are lower Lebesgue integrals: the weight `g` is valued in
`ℝ≥0∞` and need not be bounded, and `h` need not be measurable or integrable. This is the form in
which conditional expectations enter supermartingale bounds for products of a nonnegative
predictable factor and a nonnegative increment.

## Main statements

* `LMLExplore.lintegral_mul_ofReal_le_of_condExp_le`: for an `m`-measurable `g : Ω → ℝ≥0∞`,
  `∫⁻ g * ofReal f ≤ ∫⁻ g * ofReal h`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LMLExplore

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If `f ≥ 0` is integrable and its conditional expectation given `m` is at most `h`, then
`∫⁻ g * f ≤ ∫⁻ g * h` for every `m`-measurable `g : Ω → ℝ≥0∞`. -/
theorem lintegral_mul_ofReal_le_of_condExp_le (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {f h : Ω → ℝ} (hf : Integrable f μ) (hf_nonneg : 0 ≤ᵐ[μ] f) (hfh : μ[f | m] ≤ᵐ[μ] h)
    {g : Ω → ℝ≥0∞} (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (f ω) ∂μ ≤ ∫⁻ ω, g ω * ENNReal.ofReal (h ω) ∂μ := by
  have hF : AEMeasurable (fun ω ↦ ENNReal.ofReal (f ω)) μ := hf.1.aemeasurable.ennreal_ofReal
  refine @Measurable.ennreal_induction Ω m
    (fun g ↦ ∫⁻ ω, g ω * ENNReal.ofReal (f ω) ∂μ ≤ ∫⁻ ω, g ω * ENNReal.ofReal (h ω) ∂μ)
    (fun c s hs ↦ ?_) (fun g₁ g₂ _ hg₁ _ h₁ h₂ ↦ ?_) (fun g hg hmono ih ↦ ?_) g hg
  · -- indicators: `∫_s f = ∫_s μ[f | m] ≤ ∫_s h`
    have hind : ∀ F : Ω → ℝ≥0∞,
        ∫⁻ ω, s.indicator (fun _ ↦ c) ω * F ω ∂μ = ∫⁻ ω in s, c * F ω ∂μ := fun F ↦ by
      rw [← lintegral_indicator (hm s hs)]
      congr 1 with ω
      by_cases hω : ω ∈ s <;> simp [hω]
    rw [hind, hind, lintegral_const_mul'' c hF.restrict]
    refine le_trans ?_ (lintegral_const_mul_le c _)
    gcongr c * ?_
    calc ∫⁻ ω in s, ENNReal.ofReal (f ω) ∂μ = ENNReal.ofReal (∫ ω in s, f ω ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_restrict_of_ae hf_nonneg)).symm
      _ = ENNReal.ofReal (∫ ω in s, μ[f | m] ω ∂μ) := by rw [setIntegral_condExp hm hf hs]
      _ = ∫⁻ ω in s, ENNReal.ofReal (μ[f | m] ω) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal integrable_condExp.integrableOn
            (ae_restrict_of_ae (condExp_nonneg hf_nonneg))
      _ ≤ ∫⁻ ω in s, ENNReal.ofReal (h ω) ∂μ :=
          lintegral_mono_ae (ae_restrict_of_ae (hfh.mono fun ω hω ↦ ENNReal.ofReal_le_ofReal hω))
  · -- sums
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_left' (f := fun ω ↦ g₁ ω * ENNReal.ofReal (f ω))
      ((hg₁.mono hm le_rfl).aemeasurable.mul hF)]
    exact (add_le_add h₁ h₂).trans (le_lintegral_add _ _)
  · -- increasing suprema, by monotone convergence
    simp only [ENNReal.iSup_mul]
    rw [lintegral_iSup' (f := fun n ω ↦ g n ω * ENNReal.ofReal (f ω))
      (fun n ↦ ((hg n).mono hm le_rfl).aemeasurable.mul hF)
      (ae_of_all _ fun ω n k hnk ↦ by dsimp only; gcongr; exact hmono hnk ω)]
    exact iSup_le fun n ↦ (ih n).trans
      (lintegral_mono fun ω ↦ le_iSup (fun i ↦ g i ω * ENNReal.ofReal (h ω)) n)

end LMLExplore
