/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.EValues.RIPr
import LMLExplore.EValues.Utility.Basic

/-!
# The relative entropy to a mixture with a singular law

For probability measures `μ` and `ν` with `ν` singular to `μ`, and `ε ≤ 1`, the relative entropy
from `μ` to the mixture `(1 - ε) ν + ε μ` is `log (1 / ε)`: the density of `μ` with respect to the
mixture is `1 / ε` on a set that carries `μ` and that `ν` does not charge. The proof uses
Statlib's variational form of the relative entropy, the maximal expected logarithm of an
e-variable for the singleton null (`maxUtility_singleton_eq_klDiv`): an e-variable for the mixture
has integral at most `1 / ε` under `μ`, and `1 / ε` times the indicator of that set is an
e-variable for the mixture.

## Main statements

* `InformationTheory.klDiv_mixture_of_mutuallySingular`:
  `klDiv μ ((1 - ε) • ν + ε • μ) = log (1 / ε)` for `ν ⟂ₘ μ`.
* `InformationTheory.iInf_klDiv_mixture_of_mutuallySingular`: the smallest relative entropy
  from `μ` to a nonempty set of such mixtures is `log (1 / ε)`.

## Implementation notes

The statement and its proof are adapted from the helper `klDiv_mixture_eq_log_inv` of
`EValuesResearch/Results/RateVersusKL.lean` (commit `dd4072f`) in the paper project
`RemyDegenne/evalues_research` (same author), with its separating set replaced by the
hypothesis `ν ⟂ₘ μ`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- The relative entropy from a probability measure `μ` to its mixture `(1 - ε) ν + ε μ` with a
probability measure `ν` singular to `μ` is `log (1 / ε)`, for `ε ≤ 1`. It is infinite for
`ε = 0`. -/
theorem klDiv_mixture_of_mutuallySingular {μ ν : Measure 𝓧} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hνμ : ν ⟂ₘ μ) {ε : ℝ≥0∞} (hε : ε ≤ 1) :
    ((klDiv μ ((1 - ε) • ν + ε • μ) : ℝ≥0∞) : EReal) = ENNReal.log ε⁻¹ := by
  set P := (1 - ε) • ν + ε • μ with hP_def
  have hP : IsProbabilityMeasure P := ⟨by simp [P, tsub_add_cancel_of_le hε]⟩
  set t := hνμ.nullSet
  have ht : MeasurableSet t := hνμ.measurableSet_nullSet
  rw [← maxUtility_singleton_eq_klDiv]
  refine le_antisymm (iSup₂_le fun X hX ↦ ?_) ?_
  · -- an e-variable for the mixture has integral at most `1 / ε` under `μ`
    rcases eq_or_ne ε 0 with rfl | hε0
    · simp
    have hle : ∫⁻ x, X x ∂μ ≤ ε⁻¹ := by
      rw [ENNReal.le_inv_iff_mul_le, mul_comm]
      calc ε * ∫⁻ x, X x ∂μ
      _ ≤ (1 - ε) * ∫⁻ x, X x ∂ν + ε * ∫⁻ x, X x ∂μ := le_add_self
      _ = ∫⁻ x, X x ∂P := by simp [P, lintegral_add_measure]
      _ ≤ 1 := hX.lintegral_le_one rfl
    calc ∫ᵉ x, (logUtility ∘ X) x ∂μ
    _ ≤ logUtility (∫⁻ x, X x ∂μ) :=
      Utility.eintegral_le_map logUtility hX.measurable.aemeasurable
    _ ≤ ENNReal.log ε⁻¹ := ENNReal.log_monotone hle
  · -- `1 / ε` times the indicator of the set `t` charged by `μ` alone is an e-variable
    have hX : IsEVar (t.indicator fun _ ↦ ε⁻¹) {P} := by
      refine ⟨measurable_const.indicator ht, fun P' hP' ↦ ?_⟩
      rw [Set.mem_singleton_iff.1 hP', lintegral_indicator_const ht]
      calc ε⁻¹ * P t
      _ = ε⁻¹ * (ε * μ t) := by simp [P, t, hνμ.measure_nullSet]
      _ ≤ ε⁻¹ * ε := by gcongr; exact mul_le_of_le_one_right' prob_le_one
      _ ≤ 1 := ENNReal.inv_mul_le_one ε
    exact (logUtility.eintegral_comp_indicator_const hνμ.measure_compl_nullSet ε⁻¹).symm.trans_le
      (hX.eintegral_le_maxUtility μ logUtility)

/-- The smallest relative entropy from a probability measure `μ` to a nonempty set of mixtures
`(1 - ε) ν + ε μ`, each with a probability measure `ν` singular to `μ`, is `log (1 / ε)`, for
`ε ≤ 1`: every member is at relative entropy `log (1 / ε)`
(`InformationTheory.klDiv_mixture_of_mutuallySingular`). -/
theorem iInf_klDiv_mixture_of_mutuallySingular {μ : Measure 𝓧} [IsProbabilityMeasure μ]
    {ε : ℝ≥0∞} {S : Set (Measure 𝓧)} (hS : S.Nonempty)
    (h : ∀ P ∈ S, ∃ ν : Measure 𝓧, IsProbabilityMeasure ν ∧ ν ⟂ₘ μ ∧ P = (1 - ε) • ν + ε • μ)
    (hε : ε ≤ 1) :
    ((⨅ P ∈ S, klDiv μ P : ℝ≥0∞) : EReal) = ENNReal.log ε⁻¹ := by
  have hkl (P : Measure 𝓧) (hP : P ∈ S) : ((klDiv μ P : ℝ≥0∞) : EReal) = ENNReal.log ε⁻¹ := by
    obtain ⟨ν, hν, hνμ, rfl⟩ := h P hP
    exact klDiv_mixture_of_mutuallySingular hνμ hε
  obtain ⟨P₀, hP₀⟩ := hS
  rw [← hkl P₀ hP₀]
  congr 1
  exact (biInf_congr fun P hP ↦ EReal.coe_ennreal_injective ((hkl P hP).trans
    (hkl P₀ hP₀).symm)).trans (biInf_const ⟨P₀, hP₀⟩)

end InformationTheory
