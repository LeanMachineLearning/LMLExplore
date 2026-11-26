/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.KullbackLeibler.Basic
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# The relative entropy from a law that dominates a multiple of another

The relative entropy is convex in its first argument, and a bound in the other direction holds
up to the entropy of the weights: if a probability measure `ν` dominates `t • μ` for a
probability measure `μ` and `t ∈ [0, 1]`, so that `ν = t μ + (1 - t) μ'` for a probability
measure `μ'`, then for every finite measure `ξ`,
`t KL(μ ‖ ξ) ≤ KL(ν ‖ ξ) + h(t)`,
with `h` the binary entropy `Real.binEntropy`. A law close to `μ` in this sense is at relative
entropy at least about `KL(μ ‖ ξ)` from every `ξ`, uniformly in `ξ`. This is the step, in the Lean
library of [EVR26], of the proof that on a finite alphabet the bipolar rate equals the smallest
relative entropy to the null (Note 42, Theorem 6).

## Main statements

* `InformationTheory.mul_klDiv_le_klDiv_add_binEntropy`: for `t • μ ≤ ν`,
  `t KL(μ ‖ ξ) ≤ KL(ν ‖ ξ) + h(t)`.

## Implementation notes

The proof tests the Donsker–Varadhan form of `KL(ν ‖ ξ)` with mass correction
(`TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one`) at `g = log ((1 - t) + t exp f)`, for
each bounded measurable `f` of the variational form of `KL(μ ‖ ξ)`. The exponential terms are
proportional, and `t • μ ≤ ν` compares the linear terms, since `g` is bounded below by
`log (1 - t)`. The statement and its proof are adapted from the lemma
`ofReal_mul_klDiv_le_klDiv_add_binEntropy` of `EValuesResearch/Results/FiniteAlphabetRate.lean`
(commit `9eee1f2`) in the paper project `RemyDegenne/evalues_research`, with the weight written
`t` instead of `1 - δ` and its hypotheses `0 < 1 - t < 1` removed.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and the Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and refereed
  by AI agents: Note 42, *Four results that came out of the check of the book plan*, Section 1.
-/

public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- A bounded measurable function is integrable under a finite measure, and so is its
exponential. -/
private lemma integrable_and_integrable_exp {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ ∧ Integrable (fun x ↦ exp (f x)) μ :=
  ⟨.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC),
    .of_bound hf.exp.aestronglyMeasurable (exp C) (ae_of_all _ fun x ↦ by
      rw [norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.2 (le_of_abs_le (hC x)))⟩

/-- **The relative entropy from a law that dominates a multiple of another.** If the probability
measure `ν` is at least `t • μ`, with `μ` a probability measure, then
`t KL(μ ‖ ξ) ≤ KL(ν ‖ ξ) + h(t)` for every finite measure `ξ`, where `h` is the binary entropy.
The hypothesis forces `t ≤ 1`, and for `t = 1` it forces `ν = μ`. -/
theorem mul_klDiv_le_klDiv_add_binEntropy {μ ν ξ : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsFiniteMeasure ξ] {t : ℝ≥0} (h : t • μ ≤ ν) :
    t * klDiv μ ξ ≤ klDiv ν ξ + ENNReal.ofReal (binEntropy t) := by
  have ht1 : t ≤ 1 := by
    have h' := h Set.univ
    rwa [smul_apply, measure_univ, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one,
      ENNReal.coe_le_one_iff] at h'
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  rcases eq_or_ne t 1 with rfl | ht1'
  · rw [one_smul] at h
    rw [Measure.eq_of_le_of_isProbabilityMeasure h, ENNReal.coe_one, one_mul]
    exact le_self_add
  -- the weights `t` and `δ = 1 - t` are in `(0, 1)`
  have ht : (0 : ℝ) < t := lt_of_le_of_ne t.coe_nonneg (by exact_mod_cast ht0.symm)
  have ht' : (t : ℝ) < 1 := lt_of_le_of_ne (by exact_mod_cast ht1) (by exact_mod_cast ht1')
  set δ : ℝ := 1 - t with hδ
  have hδ0 : 0 < δ := by linarith
  rw [TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one (μ := μ) (ν := ξ), ENNReal.mul_iSup]
  refine iSup_le fun f ↦ ?_
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun hf ↦ iSup_le fun ⟨C, hC⟩ ↦ ?_
  -- the variational form of `KL(ν ‖ ξ)` at `g = log (δ + t exp f)`
  set g : α → ℝ := fun x ↦ log (δ + t * exp (f x)) with hg
  have hpos (x : α) : 0 < δ + t * exp (f x) := by positivity
  have hg_meas : Measurable g := by fun_prop
  have hg_ge (x : α) : log δ ≤ g x := log_le_log hδ0 (le_add_of_nonneg_right (by positivity))
  have hg_ge' (x : α) : log t + f x ≤ g x := by
    rw [← log_exp (f x), ← log_mul ht.ne' (exp_pos _).ne']
    exact log_le_log (by positivity) (le_add_of_nonneg_left hδ0.le)
  have hg_le (x : α) : g x ≤ C := by
    refine (log_le_log (hpos x) (?_ : _ ≤ exp |f x|)).trans ((log_exp _).le.trans (hC x))
    have h1 : (1 : ℝ) ≤ exp |f x| := one_le_exp (abs_nonneg _)
    have h2 : exp (f x) ≤ exp |f x| := exp_le_exp.2 (le_abs_self _)
    nlinarith [mul_le_mul_of_nonneg_left h2 ht.le, mul_le_mul_of_nonneg_left h1 hδ0.le]
  have hgC (x : α) : |g x| ≤ C - log δ := by
    have hlog : log δ ≤ 0 := log_nonpos hδ0.le (by linarith)
    have := (abs_nonneg (f x)).trans (hC x)
    rw [abs_le]
    constructor <;> linarith [hg_ge x, hg_le x]
  have hgν := (integrable_and_integrable_exp (μ := ν) hg_meas hgC).1
  have hgμ := (integrable_and_integrable_exp (μ := μ) hg_meas hgC).1
  have hfμ := (integrable_and_integrable_exp (μ := μ) hf hC).1
  have hDV := TauCeti.ofReal_integral_sub_integral_exp_sub_one_le_klDiv hgν
    (integrable_and_integrable_exp (μ := ξ) hg_meas hgC).2
  -- the exponential terms are proportional
  have h_exp : ∫ x, (exp (g x) - 1) ∂ξ = t * ∫ x, (exp (f x) - 1) ∂ξ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hg]
    rw [exp_log (hpos x), hδ]
    ring
  -- `t • μ ≤ ν` compares the linear terms, as `g - log δ` is nonnegative
  have h_lin : t * ∫ x, f x ∂μ - binEntropy t ≤ ∫ x, g x ∂ν := by
    have h1 : t * ∫ x, (g x - log δ) ∂μ ≤ ∫ x, (g x - log δ) ∂ν := by
      have h := integral_mono_measure h (ae_of_all _ fun x ↦ sub_nonneg.2 (hg_ge x))
        (hgν.sub (integrable_const _))
      rwa [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h
    have h2 : ∫ x, (log t - log δ + f x) ∂μ ≤ ∫ x, (g x - log δ) ∂μ :=
      integral_mono ((integrable_const _).add hfμ) (hgμ.sub (integrable_const _))
        fun x ↦ by linarith [hg_ge' x]
    rw [integral_add (integrable_const _) hfμ, integral_const, probReal_univ, one_smul,
      integral_sub hgμ (integrable_const _), integral_const, probReal_univ, one_smul] at h2
    rw [integral_sub hgν (integrable_const _), integral_const, probReal_univ, one_smul,
      integral_sub hgμ (integrable_const _), integral_const, probReal_univ, one_smul] at h1
    have h3 := mul_le_mul_of_nonneg_left h2 ht.le
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog, ← hδ]
    nlinarith
  calc (t : ℝ≥0∞) * ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ξ)
  _ = ENNReal.ofReal (t * (∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ξ)) := by
    rw [ENNReal.ofReal_mul t.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  _ ≤ ENNReal.ofReal ((∫ x, g x ∂ν - ∫ x, (exp (g x) - 1) ∂ξ) + binEntropy t) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [h_exp]
    linarith
  _ ≤ ENNReal.ofReal (∫ x, g x ∂ν - ∫ x, (exp (g x) - 1) ∂ξ) + ENNReal.ofReal (binEntropy t) :=
    ENNReal.ofReal_add_le
  _ ≤ klDiv ν ξ + ENNReal.ofReal (binEntropy t) := by gcongr

end InformationTheory
