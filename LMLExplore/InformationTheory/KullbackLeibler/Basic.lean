/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.InformationTheory.KullbackLeibler.Basic
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
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
  by AI agents: Note 42, *Four results that came out of the check of the book plan*, Theorem 6.
-/

public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α}

/-- For `t ∈ [0, 1)`, `log ((1 - t) + t exp y)` is at least `log (1 - t)`. -/
private lemma log_one_sub_le_log_one_sub_add_mul_exp {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1) (y : ℝ) :
    log (1 - t) ≤ log (1 - t + t * exp y) :=
  log_le_log (by linarith) (le_add_of_nonneg_right (by positivity))

/-- For `t ∈ (0, 1]`, `log ((1 - t) + t exp y)` is at least `log t + y`. -/
private lemma log_add_le_log_one_sub_add_mul_exp {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (y : ℝ) :
    log t + y ≤ log (1 - t + t * exp y) := by
  rw [← log_exp y, ← log_mul ht.ne' (exp_pos _).ne', log_exp]
  exact log_le_log (by positivity) (le_add_of_nonneg_left (by linarith))

/-- For `t ∈ (0, 1)` and `|y| ≤ C`, `|log ((1 - t) + t exp y)| ≤ C - log (1 - t)`. -/
private lemma abs_log_one_sub_add_mul_exp_le {t : ℝ} (ht : 0 < t) (ht' : t < 1) {y C : ℝ}
    (hy : |y| ≤ C) :
    |log (1 - t + t * exp y)| ≤ C - log (1 - t) := by
  have hle : log (1 - t + t * exp y) ≤ C := by
    refine (log_le_log (by positivity) (?_ : _ ≤ exp |y|)).trans ((log_exp _).le.trans hy)
    have h1 : (1 : ℝ) ≤ exp |y| := one_le_exp (abs_nonneg _)
    have h2 : exp y ≤ exp |y| := exp_le_exp.2 (le_abs_self _)
    nlinarith [mul_le_mul_of_nonneg_left h2 ht.le,
      mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 ht'.le)]
  have hlog : log (1 - t) ≤ 0 := log_nonpos (by linarith) (by linarith)
  have := (abs_nonneg y).trans hy
  rw [abs_le]
  constructor <;> linarith [log_one_sub_le_log_one_sub_add_mul_exp ht.le ht' y]

/-- If `t • μ ≤ ν` with `t > 0`, a function `g` at least `log (1 - t)` and at least
`log t + f` has `t ∫ f ∂μ - h(t) ≤ ∫ g ∂ν`, with `h` the binary entropy: `t • μ ≤ ν` compares the
integrals of the nonnegative function `g - log (1 - t)`. -/
private lemma mul_integral_sub_binEntropy_le_integral {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {t : ℝ≥0} (h : t • μ ≤ ν) (ht : 0 < (t : ℝ))
    {f g : α → ℝ} (hf : Integrable f μ) (hgμ : Integrable g μ) (hgν : Integrable g ν)
    (hg_ge : ∀ x, log (1 - t) ≤ g x) (hg_ge' : ∀ x, log t + f x ≤ g x) :
    t * ∫ x, f x ∂μ - binEntropy t ≤ ∫ x, g x ∂ν := by
  have h1 : t * ∫ x, (g x - log (1 - t)) ∂μ ≤ ∫ x, (g x - log (1 - t)) ∂ν := by
    have h := integral_mono_measure h (ae_of_all _ fun x ↦ sub_nonneg.2 (hg_ge x))
      (hgν.sub (integrable_const _))
    rwa [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul] at h
  have h2 : ∫ x, (log t - log (1 - t) + f x) ∂μ ≤ ∫ x, (g x - log (1 - t)) ∂μ :=
    integral_mono ((integrable_const _).add hf) (hgμ.sub (integrable_const _))
      fun x ↦ by linarith [hg_ge' x]
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
  simp [integral_add, integral_sub, hf, hgμ, hgν] at h1 h2
  nlinarith [mul_le_mul_of_nonneg_left h2 ht.le]

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
  -- the weight `t` is in `(0, 1)`
  have ht : (0 : ℝ) < t := lt_of_le_of_ne t.coe_nonneg (by exact_mod_cast ht0.symm)
  have ht' : (t : ℝ) < 1 := lt_of_le_of_ne (by exact_mod_cast ht1) (by exact_mod_cast ht1')
  rw [TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one (μ := μ) (ν := ξ), ENNReal.mul_iSup]
  refine iSup_le fun f ↦ ?_
  simp only [ENNReal.mul_iSup]
  refine iSup_le fun hf ↦ iSup_le fun ⟨C, hC⟩ ↦ ?_
  -- the variational form of `KL(ν ‖ ξ)` at `g = log ((1 - t) + t exp f)`
  set g : α → ℝ := fun x ↦ log (1 - t + t * exp (f x)) with hg
  have hg_meas : Measurable g := by fun_prop
  have hgC (x : α) : |g x| ≤ C - log (1 - t) := abs_log_one_sub_add_mul_exp_le ht ht' (hC x)
  have hgν := LMLExplore.integrable_of_abs_le hg_meas hgC ν
  have hDV := TauCeti.ofReal_integral_sub_integral_exp_sub_one_le_klDiv hgν
    (LMLExplore.integrable_exp_of_abs_le hg_meas hgC ξ)
  -- the exponential terms are proportional
  have h_exp : ∫ x, (exp (g x) - 1) ∂ξ = t * ∫ x, (exp (f x) - 1) ∂ξ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [hg]
    rw [exp_log (by positivity)]
    ring
  -- `t • μ ≤ ν` compares the linear terms
  have h_lin := mul_integral_sub_binEntropy_le_integral h ht
    (LMLExplore.integrable_of_abs_le hf hC μ)
    (LMLExplore.integrable_of_abs_le hg_meas hgC μ) hgν
    (fun x ↦ log_one_sub_le_log_one_sub_add_mul_exp ht.le ht' (f x))
    (fun x ↦ log_add_le_log_one_sub_add_mul_exp ht ht'.le (f x))
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
