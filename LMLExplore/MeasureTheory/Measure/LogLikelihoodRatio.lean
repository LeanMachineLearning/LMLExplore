/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import TauCeti.InformationTheory.KullbackLeibler.ChangeOfReference

/-!
# The mean of the absolute value of a log-likelihood ratio, and a change of reference

For a σ-finite `μ` and a finite `ν` with `μ ≪ ν` and `llr μ ν` integrable under `μ`, the mean
under `μ` of `|llr μ ν|` is at most the mean of `llr μ ν` plus twice the mass of `ν`: the
negative part of `llr μ ν` is the positive part of `log (dν/dμ)`, which is at most `dν/dμ`, of
mean at most the mass of `ν`. For probability measures, the mean of `|llr μ ν|` is at most
`(klDiv μ ν).toReal + 2`: a bound on the relative entropy controls the whole log-likelihood
ratio in `L¹`, not only its mean.

Against a measure `ν.withDensity f` with a density, the log-likelihood ratio of `μ` is that
against `ν` minus `log f`, `μ`-almost everywhere, by Tau Ceti's chain rule `TauCeti.llr_add_llr`.

## Main statements

* `MeasureTheory.integral_abs_llr_le`:
  `∫ x, |llr μ ν x| ∂μ ≤ ∫ x, llr μ ν x ∂μ + 2 * ν.real univ`.
* `MeasureTheory.llr_withDensity_ae_eq`: `llr μ (ν.withDensity f) = llr μ ν - log f`,
  `μ`-almost everywhere, when `μ ≪ ν.withDensity f`.

## Implementation notes

The bound is adapted from the helper `log_toReal_density_facts` of
`EValuesResearch/Results/NumeraireBarronAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, rewritten with Mathlib's log-likelihood ratio. The change of
reference `llr_withDensity_ae_eq` is extracted from the proof of
`ProbabilityTheory.klIntegral_withDensity_prod_rpow`, adapted from the same paper project at
commit `83205cb` (see `LMLExplore/EValues/BipolarRate/Saturation.lean` for its sources).
-/

public section

open Real
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- **The mean of the absolute value of a log-likelihood ratio.** For a σ-finite `μ` and a finite
`ν` with `μ ≪ ν` and `llr μ ν` integrable under `μ`, the mean of `|llr μ ν|` under `μ` is at most
the mean of `llr μ ν` plus twice the mass of `ν`: the negative part of `llr μ ν` is the positive
part of `log (dν/dμ)`, which is at most `dν/dμ`. -/
theorem integral_abs_llr_le [SigmaFinite μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫ x, |llr μ ν x| ∂μ ≤ ∫ x, llr μ ν x ∂μ + 2 * ν.real Set.univ := by
  have hpt : ∀ᵐ x ∂μ, |llr μ ν x| ≤ llr μ ν x + 2 * (ν.rnDeriv μ x).toReal := by
    filter_upwards [neg_llr hμν] with x hx
    have h0 : 0 ≤ (ν.rnDeriv μ x).toReal := ENNReal.toReal_nonneg
    have h1 : -llr μ ν x ≤ (ν.rnDeriv μ x).toReal := by
      rw [← Pi.neg_apply, hx]
      exact log_le_self h0
    rcases le_total 0 (llr μ ν x) with h | h
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_nonpos h]
      linarith
  have hint : Integrable (fun x ↦ (ν.rnDeriv μ x).toReal) μ := Measure.integrable_toReal_rnDeriv
  calc ∫ x, |llr μ ν x| ∂μ
  _ ≤ ∫ x, llr μ ν x + 2 * (ν.rnDeriv μ x).toReal ∂μ :=
    integral_mono_ae h_int.abs (h_int.add (hint.const_mul 2)) hpt
  _ = ∫ x, llr μ ν x ∂μ + 2 * ∫ x, (ν.rnDeriv μ x).toReal ∂μ := by
    rw [integral_add h_int (hint.const_mul 2), integral_const_mul]
  _ ≤ ∫ x, llr μ ν x ∂μ + 2 * ν.real Set.univ := by
    rw [Measure.integral_toReal_rnDeriv']
    have : 0 ≤ (ν.singularPart μ).real Set.univ := measureReal_nonneg
    linarith

/-- **The log-likelihood ratio against a measure with a density.** If `μ ≪ ν.withDensity f`,
then `llr μ (ν.withDensity f) = llr μ ν - log f`, `μ`-almost everywhere: by the chain rule
`TauCeti.llr_add_llr`, the log-likelihood ratio against `ν` is that against `ν.withDensity f`
plus `llr (ν.withDensity f) ν`, and the latter is `log f` (`Measure.rnDeriv_withDensity₀`). -/
theorem llr_withDensity_ae_eq [SigmaFinite μ] [SigmaFinite ν] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) [SigmaFinite (ν.withDensity f)] (hμf : μ ≪ ν.withDensity f) :
    llr μ (ν.withDensity f) =ᵐ[μ] fun x ↦ llr μ ν x - log (f x).toReal := by
  have hμν : μ ≪ ν := hμf.trans (withDensity_absolutelyContinuous _ _)
  filter_upwards [TauCeti.llr_add_llr hμf hμν,
    hμν.ae_le (Measure.rnDeriv_withDensity₀ ν hf)] with x h1 h2
  rw [← h1, Pi.add_apply, llr_def (ν.withDensity f)]
  beta_reduce
  rw [h2]
  ring

end MeasureTheory
