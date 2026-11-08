/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.HasCondDistrib
public import LMLExplore.Probability.Martingale.Basic
public import LMLExplore.Probability.Martingale.Mixture
public import LMLExplore.Probability.Martingale.Ville
public import LMLExplore.SequentialLearning.Algorithm

/-!
# Likelihood ratio supermartingales along a bandit run

Along a run of any algorithm against a stochastic bandit `ν`, let `z a y` be a function of the
arm and the observation whose exponential has `ν a`-expectation at most `1` for every arm: for
instance the log-likelihood ratio `log (dν' a / dν a)` of another bandit `ν'`. Then
`exp (∑ k < n, z (A k) (Y k))`, the likelihood ratio of the observations so far, is a
supermartingale for the filtration of the history and the next action. So are its mixtures
`∫ exp (∑ k < n, z l (A k) (Y k)) dπ(l)` over a parameter `l` drawn from a probability measure
`π`, the likelihood ratios of the Bayesian models with prior `π`, and Ville's inequality bounds the
probability that a mixture ever reaches `c` by `1 / c`. This replaces the change of measure of the
universal coding argument of [GK16, Appendix C.1] by a statement about the true measure only; with
the Krichevsky–Trofimov prior on Bernoulli means, it gives the deviation inequality of
`SequentialLearning/BernoulliDeviation.lean`.

## Main statements

* `LMLExplore.supermartingale_exp_sum_of_lintegral_exp_le_one`: the likelihood ratio
  `exp (∑ k < n, z (A k) (Y k))` is a supermartingale.
* `LMLExplore.measure_exists_le_integral_exp_sum_le`: Ville's inequality for its mixtures,
  `P(∃ n, c ≤ ∫ exp (∑ k < n, z l (A k) (Y k)) dπ(l)) ≤ 1 / c`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset Real

open scoped ENNReal

namespace LMLExplore

variable {𝓐 𝓨 Ω : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {alg : Algorithm Unit 𝓐 𝓨} {ν : Kernel 𝓐 𝓨}
  [IsMarkovKernel ν] {O : ℕ → Ω → Unit} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- **The likelihood ratio supermartingale of a bandit run.** Along a run against the stochastic
bandit `ν`, if `∫ exp (z a y) dν a(y) ≤ 1` for every arm `a`, then
`n ↦ exp (∑ k < n, z (A k) (Y k))` is a supermartingale for the filtration of the history and the
next action. -/
lemma supermartingale_exp_sum_of_lintegral_exp_le_one [IsFiniteMeasure P]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {z : 𝓐 → 𝓨 → ℝ}
    (hz : Measurable (Function.uncurry z))
    (hle : ∀ a, ∫⁻ y, ENNReal.ofReal (exp (z a y)) ∂ν a ≤ 1) :
    Supermartingale (fun n ω ↦ exp (∑ k ∈ range n, z (A k ω) (Y k ω))) h.filtrationAction P := by
  refine supermartingale_exp_sum_of_lintegral_mul_exp_le (fun n ↦ ?_) (fun n g hg ↦ ?_)
  · have hA : Measurable[h.filtrationAction (n + 1)] (A n) :=
      (h.adapted_action_filtrationAction n).mono (h.filtrationAction.mono (Nat.le_succ n)) le_rfl
    have hY : Measurable[h.filtrationAction (n + 1)] (Y n) :=
      h.measurable_feedback_filtrationAction_of_lt (Nat.lt_succ_self n)
    exact hz.comp (hA.prodMk hY)
  · rw [h.filtrationAction_eq_comap n] at hg
    obtain ⟨g', hg', rfl⟩ := hg.exists_eq_measurable_comp
    have hzm : Measurable fun p : ((Hist Unit 𝓐 𝓨 n × Unit) × 𝓐) × 𝓨 ↦
        g' p.1 * ENNReal.ofReal (exp (z p.1.2 p.2)) :=
      (hg'.comp measurable_fst).mul
        ((hz.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).exp.ennreal_ofReal)
    have key := (h.hasCondDistrib_feedback n).lintegral_comp_prodMk_eq_lintegral_lintegral hzm
    simp only [Function.comp_apply] at key ⊢
    rw [key]
    refine lintegral_mono fun ω ↦ ?_
    have hm : Measurable fun y ↦ ENNReal.ofReal (exp (z (A n ω) y)) :=
      (hz.comp (measurable_const.prodMk measurable_id)).exp.ennreal_ofReal
    rw [lintegral_const_mul _ hm]
    simpa [Environment.bandit_def, Environment.stationary_def] using
      mul_le_of_le_one_right' (hle (A n ω))

/-- **Ville's inequality for mixtures of likelihood ratios along a bandit run.** Along a run
against the stochastic bandit `ν`, let `z l a y` depend measurably on a parameter `l`, with
`∫ exp (z l a y) dν a(y) ≤ 1` for every `l` and every arm `a`, and let `ρ` be a probability measure
on the parameters. For every `c > 0`, the probability that the mixture
`∫ exp (∑ k < n, z l (A k) (Y k)) dρ(l)` ever reaches `c` is at most `1 / c`. -/
theorem measure_exists_le_integral_exp_sum_le [IsProbabilityMeasure P] {L : Type*}
    {mL : MeasurableSpace L} {ρ : Measure L} [IsProbabilityMeasure ρ]
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit ν) P) {z : L → 𝓐 → 𝓨 → ℝ}
    (hz : Measurable fun p : L × 𝓐 × 𝓨 ↦ z p.1 p.2.1 p.2.2)
    (hle : ∀ l a, ∫⁻ y, ENNReal.ofReal (exp (z l a y)) ∂ν a ≤ 1) {c : ℝ} (hc : 0 < c) :
    P {ω | ∃ n, c ≤ ∫ l, exp (∑ k ∈ range n, z l (A k ω) (Y k ω)) ∂ρ} ≤
      ENNReal.ofReal (1 / c) := by
  have hzl : ∀ l, Measurable (Function.uncurry (z l)) := fun l ↦
    hz.comp (measurable_const.prodMk measurable_id)
  have hmeas : ∀ n, Measurable[mL.prod (h.filtrationAction n)]
      (fun p : L × Ω ↦ exp (∑ k ∈ range n, z p.1 (A k p.2) (Y k p.2))) := by
    intro n
    refine Measurable.exp (Finset.measurable_sum _ fun k hk ↦ ?_)
    have hA : Measurable[h.filtrationAction n] (A k) :=
      (h.adapted_action_filtrationAction k).mono
        (h.filtrationAction.mono (mem_range.1 hk).le) le_rfl
    have hY : Measurable[h.filtrationAction n] (Y k) :=
      h.measurable_feedback_filtrationAction_of_lt (mem_range.1 hk)
    exact hz.comp (measurable_fst.prodMk ((hA.comp measurable_snd).prodMk
      (hY.comp measurable_snd)))
  have hsup : Supermartingale (fun n ω ↦ ∫ l, exp (∑ k ∈ range n, z l (A k ω) (Y k ω)) ∂ρ)
      h.filtrationAction P :=
    supermartingale_integral
      (fun l ↦ supermartingale_exp_sum_of_lintegral_exp_le_one h (hzl l) (hle l))
      (fun _ _ _ ↦ (exp_pos _).le) hmeas ⟨1, fun l ↦ by simp⟩
  have := hsup.measure_exists_le_le
    (fun n ↦ ae_of_all _ fun ω ↦ integral_nonneg fun l ↦ (exp_pos _).le) hc
  simpa using this

end LMLExplore
