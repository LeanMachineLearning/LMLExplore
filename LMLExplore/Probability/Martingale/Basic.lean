/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# A supermartingale criterion for nonnegative processes

Mathlib's `MeasureTheory.supermartingale_of_setIntegral_succ_le` asks for the integrability of
every `f n`. For an almost surely nonnegative process, the comparison of the set integrals can be
made in `ℝ≥0∞`, where it needs no integrability, and integrability then propagates from `f 0`.

## Main statements

* `LMLExplore.supermartingale_of_setLIntegral_succ_le`: an adapted, a.s. nonnegative process with
  `f 0` integrable whose lower Lebesgue set integrals over `s ∈ ℱ n` do not increase from `n` to
  `n + 1` is a supermartingale.

## References

* The proof is adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Martingale/IndepIncrements.lean`).
-/

public section

open MeasureTheory
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

end LMLExplore
