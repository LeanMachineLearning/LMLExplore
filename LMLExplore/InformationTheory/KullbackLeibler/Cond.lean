/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ConditionalProbability
public import Statlib.EValues.RIPr

/-!
# The relative entropy from a conditional law

The relative entropy from the law `μ[|A]`, the probability measure `μ` conditioned on the event
`A`, to `μ` is at most `log (1 / μ A)`. The proof uses Statlib's variational form of the relative
entropy, the maximal expected logarithm of an e-variable for the singleton null
(`maxUtility_singleton_eq_klDiv`), and Jensen's inequality: an e-variable for `μ` has integral at
most `1 / μ A` under `μ[|A]`.

## Main statements

* `InformationTheory.klDiv_cond_le`: `klDiv (μ[|A]) μ ≤ log (1 / μ A)`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The relative entropy from the law `μ` conditioned on `A` to `μ` is at most `log (1 / μ A)`. -/
lemma klDiv_cond_le {μ : Measure 𝓧} [IsProbabilityMeasure μ] {A : Set 𝓧} (hμA : μ A ≠ 0) :
    ((klDiv (μ[|A]) μ : ℝ≥0∞) : EReal) ≤ ENNReal.log (μ A)⁻¹ := by
  have := cond_isProbabilityMeasure hμA
  rw [← maxUtility_singleton_eq_klDiv]
  refine iSup₂_le fun X hX ↦ ?_
  calc ∫ᵉ x, (logUtility ∘ X) x ∂μ[|A]
  _ ≤ logUtility (∫⁻ x, X x ∂μ[|A]) :=
    Utility.eintegral_le_map logUtility hX.measurable.aemeasurable
  _ ≤ ENNReal.log (μ A)⁻¹ := by
    refine ENNReal.log_monotone ?_
    rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
    calc (μ A)⁻¹ * ∫⁻ x, X x ∂μ.restrict A
    _ ≤ (μ A)⁻¹ * 1 := by
      gcongr
      exact (setLIntegral_le_lintegral A X).trans
        ((hX.lintegral_le_measure_univ μ rfl).trans_eq measure_univ)
    _ = (μ A)⁻¹ := mul_one _

end InformationTheory
