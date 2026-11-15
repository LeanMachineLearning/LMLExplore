/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Statlib.EValues.RIPr

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
      _ ≤ P .univ := hX.lintegral_le_measure_univ P rfl
      _ = 1 := measure_univ
    calc ∫ᵉ x, (logUtility ∘ X) x ∂μ
    _ ≤ logUtility (∫⁻ x, X x ∂μ) :=
      Utility.eintegral_le_map logUtility hX.measurable.aemeasurable
    _ ≤ ENNReal.log ε⁻¹ := ENNReal.log_monotone hle
  · -- `1 / ε` times the indicator of the set `t` charged by `μ` alone is an e-variable
    have hX : IsEVar (t.indicator fun _ ↦ ε⁻¹) {P} := by
      refine IsEVar.of_lintegral_le_one (by simpa using hP)
        (measurable_const.indicator ht) fun P' hP' ↦ ?_
      rw [Set.mem_singleton_iff.1 hP', lintegral_indicator_const ht]
      calc ε⁻¹ * P t
      _ = ε⁻¹ * (ε * μ t) := by simp [P, t, hνμ.measure_nullSet]
      _ ≤ ε⁻¹ * ε := by gcongr; exact mul_le_of_le_one_right' prob_le_one
      _ ≤ 1 := ENNReal.inv_mul_le_one ε
    refine le_trans (le_of_eq ?_) (hX.eintegral_le_maxUtility μ logUtility)
    have hae : ∀ᵐ x ∂μ, x ∈ t := by rw [ae_iff]; exact hνμ.measure_compl_nullSet
    rw [eintegral_congr_ae (g := fun _ ↦ ENNReal.log ε⁻¹), eintegral_const, measure_univ,
      EReal.coe_ennreal_one, mul_one]
    filter_upwards [hae] with x hx
    simp [logUtility_apply, hx]

end InformationTheory
