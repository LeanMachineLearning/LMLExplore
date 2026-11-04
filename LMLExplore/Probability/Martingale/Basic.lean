/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Probability.Martingale.Basic

/-!
# A supermartingale criterion for nonnegative processes

Mathlib's `MeasureTheory.supermartingale_of_setIntegral_succ_le` asks for the integrability of
every `f n`. For an almost surely nonnegative process, the comparison of the set integrals can be
made in `ℝ≥0∞`, where it needs no integrability, and integrability then propagates from `f 0`.

For an exponential of partial sums `exp (∑ k < n, Z k)`, the comparison reduces to a one-round
bound: the conditional expectation of `exp (Z n)` given `ℱ n` is at most `1`, which is expressed
without conditional expectations as `∫⁻ g * exp (Z n) ≤ ∫⁻ g` for every `ℱ n`-measurable `g ≥ 0`.

## Main statements

* `LMLExplore.supermartingale_of_setLIntegral_succ_le`: an adapted, a.s. nonnegative process with
  `f 0` integrable whose lower Lebesgue set integrals over `s ∈ ℱ n` do not increase from `n` to
  `n + 1` is a supermartingale.
* `LMLExplore.supermartingale_exp_sum_of_lintegral_mul_exp_le`: `n ↦ exp (∑ k < n, Z k)` is a
  supermartingale if each `Z n` is `ℱ (n + 1)`-measurable and
  `∫⁻ g * exp (Z n) ≤ ∫⁻ g` for every `ℱ n`-measurable `g ≥ 0`.

## References

* The proof is adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Martingale/IndepIncrements.lean`).
-/

public section

open MeasureTheory Finset Real
open scoped ENNReal

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- An adapted, almost surely nonnegative process `f` with `f 0` integrable, such that
`∫⁻ ω in s, f (n + 1) ω ∂μ ≤ ∫⁻ ω in s, f n ω ∂μ` for every `s ∈ ℱ n`, is a supermartingale. -/
theorem supermartingale_of_setLIntegral_succ_le [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hf : Adapted ℱ f) (hf_nonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    (hf0 : Integrable (f 0) μ)
    (hle : ∀ n, ∀ s, MeasurableSet[ℱ n] s →
      ∫⁻ ω in s, ENNReal.ofReal (f (n + 1) ω) ∂μ ≤ ∫⁻ ω in s, ENNReal.ofReal (f n ω) ∂μ) :
    Supermartingale f ℱ μ := by
  have hfm : ∀ n, Measurable (f n) := fun n ↦ (hf n).mono (ℱ.le n) le_rfl
  have hfin : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ < ∞ := by
    intro n
    induction n with
    | zero => exact (hasFiniteIntegral_iff_ofReal (hf_nonneg 0)).1 hf0.2
    | succ n ih =>
      refine lt_of_le_of_lt ?_ ih
      simpa using hle n Set.univ MeasurableSet.univ
  have hint : ∀ n, Integrable (f n) μ := fun n ↦
    ⟨(hfm n).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (hf_nonneg n)).2 (hfin n)⟩
  refine supermartingale_of_setIntegral_succ_le (fun n ↦ (hf n).stronglyMeasurable) hint ?_
  intro n s hs
  rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae (hf_nonneg (n + 1)))
      (hfm (n + 1)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae (hf_nonneg n))
      (hfm n).aestronglyMeasurable]
  exact ENNReal.toReal_mono ((setLIntegral_le_lintegral _ _).trans_lt (hfin n)).ne (hle n s hs)

/-- **Exponential supermartingale from a one-round bound.** If each `Z n` is
`ℱ (n + 1)`-measurable and `∫⁻ g * exp (Z n) ≤ ∫⁻ g` for every `ℱ n`-measurable `g : Ω → ℝ≥0∞`
(that is, the conditional expectation of `exp (Z n)` given `ℱ n` is at most `1`), then
`n ↦ exp (∑ k < n, Z k)` is a supermartingale. -/
theorem supermartingale_exp_sum_of_lintegral_mul_exp_le [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Z : ℕ → Ω → ℝ} (hZ : ∀ n, Measurable[ℱ (n + 1)] (Z n))
    (hle : ∀ n, ∀ g : Ω → ℝ≥0∞, Measurable[ℱ n] g →
      ∫⁻ ω, g ω * ENNReal.ofReal (exp (Z n ω)) ∂μ ≤ ∫⁻ ω, g ω ∂μ) :
    Supermartingale (fun n ω ↦ exp (∑ k ∈ range n, Z k ω)) ℱ μ := by
  have hS : ∀ n, Measurable[ℱ n] fun ω ↦ ∑ k ∈ range n, Z k ω := fun n ↦
    Finset.measurable_fun_sum _ fun k hk ↦ (hZ k).mono (ℱ.mono (mem_range.1 hk)) le_rfl
  refine supermartingale_of_setLIntegral_succ_le (fun n ↦ (hS n).exp)
    (fun n ↦ ae_of_all _ fun ω ↦ (exp_pos _).le) (by simp) fun n s hs ↦ ?_
  -- `𝟙_s exp (S (n + 1))` is `𝟙_s exp (S n)` times `exp (Z n)`
  rw [← lintegral_indicator (ℱ.le n _ hs), ← lintegral_indicator (ℱ.le n _ hs)]
  have h_succ : ∀ ω, s.indicator (fun ω ↦ ENNReal.ofReal (exp (∑ k ∈ range (n + 1), Z k ω))) ω =
      s.indicator (fun ω ↦ ENNReal.ofReal (exp (∑ k ∈ range n, Z k ω))) ω *
        ENNReal.ofReal (exp (Z n ω)) := fun ω ↦ by
    by_cases hωs : ω ∈ s
    · simp [hωs, sum_range_succ, exp_add, ENNReal.ofReal_mul (exp_pos _).le]
    · simp [hωs]
  simp_rw [h_succ]
  exact hle n _ ((hS n).exp.ennreal_ofReal.indicator hs)

end LMLExplore
