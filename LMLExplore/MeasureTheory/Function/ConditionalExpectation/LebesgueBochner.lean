/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Measure.WithDensity
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
  calc ∫⁻ ω, g ω * ENNReal.ofReal (f ω) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (μ[f | m] ω) ∂μ :=
        lintegral_mul_le_lintegral_mul_of_forall_setLIntegral_le
          (f := fun ω ↦ ENNReal.ofReal (f ω)) (g := fun ω ↦ ENNReal.ofReal (μ[f | m] ω)) hm
          hf.1.aemeasurable.ennreal_ofReal integrable_condExp.1.aemeasurable.ennreal_ofReal
          (fun s hs ↦ by
            -- `∫_s f = ∫_s μ[f | m]`, in `ℝ≥0∞`
            rw [← ofReal_integral_eq_lintegral_ofReal hf.integrableOn
                (ae_restrict_of_ae hf_nonneg),
              ← ofReal_integral_eq_lintegral_ofReal integrable_condExp.integrableOn
                (ae_restrict_of_ae (condExp_nonneg hf_nonneg)),
              setIntegral_condExp hm hf hs]) hg
    _ ≤ ∫⁻ ω, g ω * ENNReal.ofReal (h ω) ∂μ :=
        lintegral_mono_ae (hfh.mono fun ω hω ↦ by gcongr)

end LMLExplore
