/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.LinearBandit.Basic
public import LMLExplore.InformationTheory.KullbackLeibler.Gaussian
public import LMLExplore.SequentialLearning.BretagnolleHuber
public import LMLExplore.SequentialLearning.Environments.Stationary
public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition

/-!
# Divergence decomposition for linear bandits with Gaussian noise

In a linear bandit with a fixed action set and Gaussian noise of variance `σ²`, the reward of an
action with feature `x ∈ E` has law `𝒩(⟪θ, x⟫, σ²)` for an unknown parameter `θ`. Such an
environment is a stochastic bandit, so LML's divergence decomposition
`Learning.IsAlgEnvSeq.klDiv_map_history_bandit` applies to it: the relative entropy between the
laws of the histories of the first `n` rounds of an algorithm against the parameters `θ` and `θ'`
is the expected sum over the rounds of the relative entropies `⟪θ - θ', X_t⟫² / (2σ²)` between
the reward laws of the features `X_t` played [LS, Lemma 15.1]. Combined with the
Bretagnolle–Huber inequality, this is the information-theoretic step of the minimax lower bounds
for linear bandits [LS, Theorems 24.1 and 24.2].

## Main statements

* `Learning.IsAlgEnvSeq.klDiv_map_history_gaussianLinearEnv`: the divergence decomposition: the
  relative entropy between the laws of the histories of the first `n` rounds against the
  parameters `θ` and `θ'` is `∑_{t < n} E[⟪θ - θ', X_t⟫² / (2σ²)]`, for the features `X_t` of the
  actions played.
* `Learning.IsAlgEnvSeq.klDiv_map_history_gaussianLinearEnv_eq_ofReal`: the same decomposition
  in real form, when the squared differences of the mean rewards are integrable.
* `Learning.IsAlgEnvSeq.klDiv_map_history_gaussianLinearEnv_le`: it is at most `n δ / (2σ²)` when
  `⟪θ - θ', x⟫² ≤ δ` for every feature `x`.
* `Learning.IsAlgEnvSeq.mul_exp_neg_div_two_le_sum_gaussianLinearEnv`,
  `Learning.IsAlgEnvSeq.mul_exp_neg_sum_integral_div_two_le_sum_gaussianLinearEnv`: the
  Bretagnolle–Huber inequality, summed over the rounds, for two such parameters, with the uniform
  bound and with the expected divergence.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 15.1 and Chapter 24.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real LMLExplore LMLExplore.Bandits
open scoped ENNReal NNReal InnerProductSpace

namespace Learning.IsAlgEnvSeq

variable {𝓐 E : Type*} [MeasurableSpace 𝓐] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {φ : 𝓐 → E} {σ2 : ℝ≥0} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
  {O' : ℕ → Ω' → Unit} {A' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → ℝ} {alg : Algorithm Unit 𝓐 ℝ}
  {θ θ' : E} {hθ : Measurable fun p : Unit × 𝓐 ↦ ⟪θ, φ p.2⟫_ℝ}
  {hθ' : Measurable fun p : Unit × 𝓐 ↦ ⟪θ', φ p.2⟫_ℝ}

/-- **Divergence decomposition for linear bandits with Gaussian noise.** Run an algorithm against
the Gaussian linear environments with a fixed action set, features `φ`, variance `σ2 ≠ 0` and
parameters `θ` and `θ'`. The relative entropy between the laws of the histories of the first `n`
rounds is `∑_{t < n} E[⟪θ - θ', φ (A t)⟫² / (2σ²)]`, the expectation being under the run against
`θ`. -/
theorem klDiv_map_history_gaussianLinearEnv
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) (n : ℕ) :
    klDiv (P.map (history O A Y n)) (P'.map (history O' A' Y' n)) =
      ∑ t ∈ range n, ∫⁻ ω, ENNReal.ofReal (⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 / (2 * σ2)) ∂P := by
  rw [gaussianLinearEnv_def, Environment.stationary_dirac_unit_eq_bandit] at h h'
  rw [h.klDiv_map_history_bandit h']
  refine sum_congr rfl fun t _ ↦ lintegral_congr fun ω ↦ ?_
  rw [Kernel.comap_apply, Kernel.comap_apply, gaussianLinearKernel_apply,
    gaussianLinearKernel_apply, klDiv_gaussianReal_gaussianReal_same_var hσ2, inner_sub_left]

/-- **Divergence decomposition for linear bandits with Gaussian noise**, in real form. If the
squared differences `⟪θ - θ', φ (A t)⟫²` of the mean rewards of the actions played are integrable,
the relative entropy between the laws of the histories of the first `n` rounds against the
parameters `θ` and `θ'` is finite and equal to `∑_{t < n} E[⟪θ - θ', φ (A t)⟫²] / (2σ²)`, the
expectations being under the run against `θ`. -/
theorem klDiv_map_history_gaussianLinearEnv_eq_ofReal
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) (hint : ∀ t, Integrable (fun ω ↦ ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2) P) (n : ℕ) :
    klDiv (P.map (history O A Y n)) (P'.map (history O' A' Y' n)) =
      ENNReal.ofReal ((∑ t ∈ range n, ∫ ω, ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 ∂P) / (2 * σ2)) := by
  rw [h.klDiv_map_history_gaussianLinearEnv h' hσ2, Finset.sum_div,
    ENNReal.ofReal_sum_of_nonneg fun t _ ↦
      div_nonneg (integral_nonneg fun ω ↦ sq_nonneg _) (by positivity)]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [← integral_div, ofReal_integral_eq_lintegral_ofReal ((hint t).div_const _)
    (ae_of_all _ fun ω ↦ by positivity)]

/-- If `⟪θ - θ', x⟫² ≤ δ` for every feature `x`, the relative entropy between the laws of the
histories of the first `n` rounds of an algorithm against the Gaussian linear environments with
parameters `θ` and `θ'` and variance `σ2 ≠ 0` is at most `n δ / (2σ²)`. -/
theorem klDiv_map_history_gaussianLinearEnv_le
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : ∀ a, ⟪θ - θ', φ a⟫_ℝ ^ 2 ≤ δ) (n : ℕ) :
    klDiv (P.map (history O A Y n)) (P'.map (history O' A' Y' n)) ≤
      ENNReal.ofReal (n * δ / (2 * σ2)) := by
  rw [h.klDiv_map_history_gaussianLinearEnv h' hσ2]
  calc ∑ t ∈ range n, ∫⁻ ω, ENNReal.ofReal (⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 / (2 * σ2)) ∂P
      ≤ ∑ t ∈ range n, ENNReal.ofReal (δ / (2 * σ2)) := by
        refine sum_le_sum fun t _ ↦ ?_
        calc ∫⁻ ω, ENNReal.ofReal (⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 / (2 * σ2)) ∂P
            ≤ ∫⁻ _, ENNReal.ofReal (δ / (2 * σ2)) ∂P :=
              lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (by gcongr; exact hδ _)
          _ = ENNReal.ofReal (δ / (2 * σ2)) := by simp
    _ = ENNReal.ofReal (n * δ / (2 * σ2)) := by
        rw [sum_const, card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg n), mul_div_assoc]

/-- **Bretagnolle–Huber inequality for linear bandits with Gaussian noise.** If `⟪θ - θ', x⟫² ≤ δ`
for every feature `x`, then for a measurable set `S` of actions, the expected number of rounds
`t < n` with `A t ∈ S` in the run against `θ` plus the expected number of rounds `t < n` with
`A' t ∉ S` in the run against `θ'` is at least `n exp (-n δ / (2σ²)) / 2`. -/
theorem mul_exp_neg_div_two_le_sum_gaussianLinearEnv
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) {δ : ℝ} (hδ : ∀ a, ⟪θ - θ', φ a⟫_ℝ ^ 2 ≤ δ) (n : ℕ) {S : Set 𝓐}
    (hS : MeasurableSet S) :
    n * exp (-(n * δ / (2 * σ2))) / 2 ≤
      ∑ t ∈ range n, P.real (A t ⁻¹' S) + ∑ t ∈ range n, P'.real (A' t ⁻¹' Sᶜ) := by
  have hkl := h.klDiv_map_history_gaussianLinearEnv_le h' hσ2 hδ n
  have hbh := mul_exp_neg_klDiv_map_history_div_two_le_sum (h.measurable_history n)
    (h'.measurable_history n) hS (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl)
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure P
  have hδ0 : 0 ≤ δ := (sq_nonneg _).trans (hδ (A 0 ω))
  refine le_trans (le_of_eq_of_le (mul_div_assoc _ _ _) ?_) hbh
  gcongr
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hkl


/-- **Bretagnolle–Huber inequality for linear bandits with Gaussian noise**, with the expected
divergence. If the squared differences `⟪θ - θ', φ (A t)⟫²` of the mean rewards of the actions
played are integrable, then for a measurable set `S` of actions, the expected number of rounds
`t < n` with `A t ∈ S` in the run against `θ` plus the expected number of rounds `t < n` with
`A' t ∉ S` in the run against `θ'` is at least
`n exp (-∑_{t < n} E[⟪θ - θ', φ (A t)⟫²] / (2σ²)) / 2`, the expectations being under the run
against `θ`. -/
theorem mul_exp_neg_sum_integral_div_two_le_sum_gaussianLinearEnv
    (h : IsAlgEnvSeq O A Y alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ σ2 hθ) P)
    (h' : IsAlgEnvSeq O' A' Y' alg (gaussianLinearEnv (Measure.dirac ()) (fun _ ↦ φ) θ' σ2 hθ')
      P')
    (hσ2 : σ2 ≠ 0) (hint : ∀ t, Integrable (fun ω ↦ ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2) P) (n : ℕ)
    {S : Set 𝓐} (hS : MeasurableSet S) :
    n * exp (-((∑ t ∈ range n, ∫ ω, ⟪θ - θ', φ (A t ω)⟫_ℝ ^ 2 ∂P) / (2 * σ2))) / 2 ≤
      ∑ t ∈ range n, P.real (A t ⁻¹' S) + ∑ t ∈ range n, P'.real (A' t ⁻¹' Sᶜ) := by
  have hkl := h.klDiv_map_history_gaussianLinearEnv_eq_ofReal h' hσ2 hint n
  have hbh := mul_exp_neg_klDiv_map_history_div_two_le_sum (h.measurable_history n)
    (h'.measurable_history n) hS (by rw [hkl]; exact ENNReal.ofReal_ne_top)
  rw [hkl, ENNReal.toReal_ofReal (div_nonneg (sum_nonneg fun t _ ↦
    integral_nonneg fun ω ↦ sq_nonneg _) (by positivity))] at hbh
  exact le_of_eq_of_le (mul_div_assoc _ _ _) hbh

end Learning.IsAlgEnvSeq
