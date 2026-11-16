/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# The mean of the absolute value of a log-likelihood ratio

For a σ-finite `μ` and a finite `ν` with `μ ≪ ν` and `llr μ ν` integrable under `μ`, the mean
under `μ` of `|llr μ ν|` is at most the mean of `llr μ ν` plus twice the mass of `ν`: the
negative part of `llr μ ν` is the positive part of `log (dν/dμ)`, which is at most `dν/dμ`, of
mean at most the mass of `ν`. For probability measures, the mean of `|llr μ ν|` is at most
`(klDiv μ ν).toReal + 2`: a bound on the relative entropy controls the whole log-likelihood
ratio in `L¹`, not only its mean.

## Main statements

* `MeasureTheory.integral_abs_llr_le`:
  `∫ x, |llr μ ν x| ∂μ ≤ ∫ x, llr μ ν x ∂μ + 2 * ν.real univ`.

## Implementation notes

The bound is adapted from the helper `log_toReal_density_facts` of
`EValuesResearch/Results/NumeraireBarronAux.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research`, rewritten with Mathlib's log-likelihood ratio.
-/

public section

open Real

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

end MeasureTheory
