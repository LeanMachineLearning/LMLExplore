/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian
public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LMLExplore.Analysis.Convex.Integral
public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.Analysis.SpecialFunctions.Log.InvMulLogSq
public import LMLExplore.Probability.Distributions.ExponentialFamily.Chernoff
public import LMLExplore.SequentialLearning.SumRewards
public import LMLExplore.Probability.Moments.KLChernoff
public import LMLExplore.Probability.Moments.SubGaussian.Sum
public import LMLExplore.SequentialLearning.SubGaussianDeviation
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Concentration lemmas for index policies

The analysis of an optimistic index policy bounds the number of times a suboptimal arm is pulled
by the number of sample sizes `s` at which the arm's index, computed from its first `s` rewards,
overestimates a threshold. This file bounds the expected value of that count for σ²-sub-Gaussian
rewards and the index `μ̂_s + √(2 σ² c / s)` of [LS, Algorithm 6], in LML's i.i.d. reward stream
model and in runs of any algorithm. For `ε > 0` and `c ≥ 0`, the expected number of sample sizes
`s` at which the index exceeds the mean plus `ε` is at most `1 + 2 σ² / ε² (c + √(π c) + 1)`: this
is [LS, Lemma 8.2], proved for independent σ²-sub-Gaussian variables as
`LMLExplore.sum_measureReal_mul_le_sum_add_sqrt_le`. The event of index `0` is the sure event,
matching the infinite index of an unpulled arm.

The same analysis needs that the index of an optimal arm rarely underestimates its mean. For the
exploration level `log f(t)` of [LS, Algorithm 6] at book round `t`, with `f(t) = 1 + t log² t`,
the probability of underestimation by `ε` at round `t` is at most
`(1 / f(t)) ∑_{s ≥ 1} exp (-s ε² / (2 σ²))`, by Hoeffding's inequality
(`LMLExplore.measureReal_sum_le_neg_mul_add_sqrt_le`) and a union bound over the number of pulls in
the reward stream model, and these sum to at most `5 σ² / ε²` over the rounds
(`Real.sum_range_inv_mul_sum_range_exp_neg_le`, [LS, Exercise 8.1]).

For rewards in `[0, 1]` and the KL-UCB index `U(μ̂_s, L / s)` of [LS, Algorithm 8], with `U` the
upper confidence level of the binary relative entropy `d`, the same two facts hold. For a level
`c > μ + ε`, where `μ` is the mean of the arm, the index after `s` pulls is above `c` only if
`μ̂_s ≥ μ + ε`, which Hoeffding's inequality makes rare, or `s d(μ + ε, c) ≤ L`, which bounds `s`:
this is [LS, Lemma 10.8], proved for independent `[0, 1]`-valued variables as
`LMLExplore.sum_measureReal_eq_zero_or_le_div_or_klBer_div_le_le`. The index of an optimal arm is
at most its mean minus `ε` at round `t` with probability at most
`(1 / f(t)) ∑_{s ≥ 1} exp (-2 s ε²)`, by the three-point inequality for `d` and the Chernoff bound
in relative-entropy form [LS, Lemma 10.7].

Both facts hold for an arm whose rewards are dominated by the member of mean `μ` of an exponential
family, with the index `U(μ̂, L / s)` of the upper confidence level of the family
(`MeasureTheory.Measure.expFamilyUpper`) and its divergence `d`: the expected number of rounds at
which the index of a pulled arm is at most `μ - ε` is at most `3 / (2 d(μ - ε, μ))`, and the
expected number of rounds at which the arm is played with `μ̂ ≥ c` or `dbar(μ̂, c) ≤ L / s` is at
most `1 + L / d(μ + ε, c) + 1 / d(μ + ε, μ)`. These are the generalizations of [LS, Lemmas 10.7
and 10.8] used in the regret analysis of KL-UCB for exponential families [GC11; CGMMS13].

## Main statements

* `iIndepFun_streamMeasure_sub_mean`, `hasSubgaussianMGF_streamMeasure_sub_mean`: in LML's i.i.d.
  reward stream model `streamMeasure ν`, the centered rewards `ω i a - μ_a` of an arm `a` are
  independent, and σ²-sub-Gaussian if the arm is.
* `sum_measureReal_streamMeasure_mul_le_sum_add_sqrt_le`: [LS, Lemma 8.2] for the rewards of one
  arm in LML's i.i.d. reward stream model `streamMeasure ν`, for σ²-sub-Gaussian arms.
* `measureReal_streamMeasure_div_add_sqrt_le_sub_le`: the converse deviation, for the index
  `μ̂_s + √(2 σ² L / s)` of the first `s ≥ 1` rewards of a σ²-sub-Gaussian arm in the stream
  model: it is at most the mean minus `ε` with probability at most `exp (-L) exp (-s ε² / (2 σ²))`.
  This controls the underestimation of an optimal arm in the proof of [LS, Theorem 8.1].
* `measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le`: in a run of any algorithm against
  `Environment.bandit ν`, the probability that at round `t` a pulled arm has index
  `μ̂_a + √(2 σ² L / T_a)` at most its mean minus `ε` is at most
  `exp (-L) ∑_{s < t} exp (-(s + 1) ε² / (2 σ²))`.
* `sum_measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le`: with the exploration level
  `log f(t + 1)` at Lean round `t`, the expected number of rounds of underestimation by `ε` is at
  most `5 σ² / ε²`.
* `sum_measureReal_action_eq_and_pullCount_eq_zero_or_lt_empMean_add_sqrt_le`: in a run of any
  algorithm, the expected number of rounds at which an arm is played before its first pull or with
  an index above its mean plus `δ > 0` is at most `1 + 2 σ² / δ² (c + √(π c) + 1)`, by
  [LS, Lemma 8.2] on the stream.
* `measureReal_streamMeasure_klUpper_le_sub_le`: in the reward stream model, the KL-UCB index
  `U(μ̂_s, L / s)` of the first `s ≥ 1` rewards of an arm with rewards in `[0, 1]` is at most its
  mean minus `ε > 0` with probability at most `exp (-L) exp (-2 ε² s)`.
* `measureReal_pullCount_ne_zero_and_klUpper_le_le`: in a run of any algorithm, the probability
  that at round `t` a pulled arm has KL-UCB index `U(μ̂_a, L / T_a)` at most its mean minus `ε` is
  at most `exp (-L) ∑_{s < t} exp (-2 ε² (s + 1))`.
* `sum_measureReal_pullCount_ne_zero_and_klUpper_le_le`: [LS, Lemma 10.7] in a run of any
  algorithm: with the exploration level `log f(t + 1)` at Lean round `t`, the expected number of
  rounds of underestimation by `ε` is at most `3 / (4 ε²)`.
* `measureReal_exists_klUpper_lt_le_tsum`, `measureReal_exists_lt_klLower_le_tsum`: in a run of
  any algorithm, for an exploration rate `β` of the number of pulls and the round, the probability
  that at some round `n` a pulled arm has its KL upper confidence level
  `U(μ̂_a, β(N_a, n) / N_a)` below its mean, or its KL lower confidence level
  `L(μ̂_a, β(N_a, n) / N_a)` above its mean, is at most `∑_n ∑_{u = 1}^n exp (-β(u, n))`. These are
  the confidence bounds of KL-LUCB [KK13].
* `measureReal_pullCount_ne_zero_and_klUpper_lt_le`,
  `measureReal_pullCount_ne_zero_and_lt_klLower_le`: [KK13, Lemma 4, (13)] in a run of any
  algorithm: for `x > 0`, the probability that at round `n` a pulled arm has `U(μ̂_a, x / N_a)`
  below its mean, or `L(μ̂_a, x / N_a)` above it, is at most `e (x log n + 1) exp (-x)`, from the
  self-normalized deviations of [GC11, Theorem 10] in the stream model, with no union bound over
  the number of pulls.
* `sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le`: in a run of any
  algorithm, the expected number of rounds at which an arm is played before its first pull, or with
  `c ≤ μ̂_a`, or with `d(μ̂_a, c) ≤ L / T_a`, is at most `1 + L / d(μ_a + ε, c) + 1 / (2 ε²)`.
* `measureReal_streamMeasure_expFamilyUpper_le_sub_le`: in the reward stream model, for rewards
  dominated by the member of mean `μ` of an exponential family, the index `U(μ̂_s, L / s)` of the
  first `s ≥ 1` rewards is at most `μ - ε` with probability at most
  `exp (-L) exp (-(s d(μ - ε, μ)))`.
* `measureReal_pullCount_ne_zero_and_expFamilyUpper_le_le`: in a run of any algorithm, the
  probability that at round `t` a pulled arm has index `U(μ̂_a, L / T_a)` at most `μ - ε` is at
  most `exp (-L) ∑_{s < t} exp (-(d(μ - ε, μ) (s + 1)))`.
* `sum_measureReal_pullCount_ne_zero_and_expFamilyUpper_le_le`: the generalization of
  [LS, Lemma 10.7]: with the exploration level `log f(t + 1)` at Lean round `t`, the expected
  number of rounds of underestimation by `ε` is at most `3 / (2 d(μ - ε, μ))`.
* `sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_expFamilyRate_le_le`: the
  generalization of [LS, Lemma 10.8]: the expected number of rounds at which the arm is played
  before its first pull, or with `c ≤ μ̂_a`, or with `dbar(μ̂_a, c) ≤ L / T_a`, is at most
  `1 + L / d(μ + ε, c) + 1 / d(μ + ε, μ)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemmas 8.2, 10.7 and 10.8, and Theorems 8.1 and 10.6.
* [KK13] E. Kaufmann and S. Kalyanakrishnan, *Information complexity in bandit subset selection*,
  COLT 2013, Section 3 and Appendix A (Lemma 4).
* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10.
* [CGMMS13] O. Cappé, A. Garivier, O.-A. Maillard, R. Munos and G. Stoltz, *Kullback–Leibler
  upper confidence bounds for optimal sequential allocation*, Ann. Statist. 41(3), 2013.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set Learning Bandits

open scoped NNReal

namespace LMLExplore.Bandits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {σ2 : ℝ≥0} {ε c : ℝ}

section Stream

variable {α : Type*} [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {a : α}

/-- In the i.i.d. reward stream model, the centered rewards `ω i a - μ_a` of arm `a` are
independent. -/
theorem iIndepFun_streamMeasure_sub_mean (ν : Kernel α ℝ) [IsMarkovKernel ν] (a : α) :
    iIndepFun (fun i (ω : ℕ → α → ℝ) ↦ ω i a - (ν a)[id]) (streamMeasure ν) := by
  set μa := (ν a)[id]
  exact (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ x ↦ x - μa) fun _ ↦ measurable_sub_const _

/-- In the i.i.d. reward stream model, the centered rewards `ω i a - μ_a` of a σ²-sub-Gaussian
arm `a` are σ²-sub-Gaussian. -/
theorem hasSubgaussianMGF_streamMeasure_sub_mean
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (i : ℕ) :
    HasSubgaussianMGF (fun (ω : ℕ → α → ℝ) ↦ ω i a - (ν a)[id]) σ2 (streamMeasure ν) :=
  hν.congr_identDistrib ((identDistrib_eval_eval_id_streamMeasure _ _ _).symm.sub_const _)

/-- **[LS, Lemma 8.2]** for the rewards of one arm in the i.i.d. reward stream model: if arm `a` is
σ²-sub-Gaussian with mean `μ_a`, then for `ε > 0` and `c ≥ 0`, the expected number of sample sizes
`s < n` at which the index `(X₀ + ⋯ + X_{s-1}) / s + √(2 σ² c / s)` of the first `s` rewards of
`a` is at least `μ_a + ε` is at most `1 + 2 σ² / ε² (c + √(π c) + 1)`. -/
theorem sum_measureReal_streamMeasure_mul_le_sum_add_sqrt_le
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hε : 0 < ε) (hc : 0 ≤ c) (n : ℕ) :
    ∑ s ∈ range n, (streamMeasure ν).real
        {ω | s * ((ν a)[id] + ε) ≤ ∑ i ∈ range s, ω i a + √(2 * σ2 * c * s)} ≤
      1 + 2 * σ2 / ε ^ 2 * (c + √(π * c) + 1) := by
  refine le_of_eq_of_le ?_ (sum_measureReal_mul_le_sum_add_sqrt_le
    (iIndepFun_streamMeasure_sub_mean ν a) (hasSubgaussianMGF_streamMeasure_sub_mean hν) hε hc n)
  refine sum_congr rfl fun s _ ↦ ?_
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  constructor <;> intro h <;> linarith

/-- **Underestimation of the index of [LS, Algorithm 6].** If arm `a` is σ²-sub-Gaussian with mean
`μ_a` and `σ² ≠ 0`, then for `L ≥ 0`, `ε ≥ 0` and `s ≠ 0`, the probability that the index
`(X₀ + ⋯ + X_{s-1}) / s + √(2 σ² L / s)` of the first `s` rewards of `a` in the i.i.d. reward
stream model is at most `μ_a - ε` is at most `exp (-L) exp (-s ε² / (2 σ²))`. -/
theorem measureReal_streamMeasure_div_add_sqrt_le_sub_le
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) {L : ℝ} (hL : 0 ≤ L)
    (hε : 0 ≤ ε) {s : ℕ} (hs : s ≠ 0) :
    (streamMeasure ν).real
        {ω | (∑ i ∈ range s, ω i a) / s + √(2 * σ2 * L / s) ≤ (ν a)[id] - ε} ≤
      exp (-L) * exp (-(ε ^ 2 / (2 * σ2) * s)) := by
  have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
  have h_sqrt := mul_sqrt_div_eq_sqrt_mul (2 * σ2 * L) hs'.le
  -- multiplied by `s`, the event says that the centered sum is at most `-(s ε + √(2 σ² L s))`
  refine le_trans (measureReal_mono fun ω (hω : _ ≤ _) ↦ ?_) (measureReal_sum_le_neg_mul_add_sqrt_le
    (iIndepFun_streamMeasure_sub_mean ν a) (hasSubgaussianMGF_streamMeasure_sub_mean hν) hσ2 hL hε
    hs)
  simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [div_add' _ _ _ hs'.ne', div_le_iff₀ hs'] at hω
  linarith

end Stream

section Runs

variable {α : Type*} [DecidableEq α] [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {ν : Kernel α ℝ} [IsMarkovKernel ν] {alg : Algorithm Unit α ℝ}
  [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- The index `x / s + √(c / s)` of a sum of rewards `x` over `s` pulls is measurable in
`(s, x)`. -/
private lemma measurable_div_add_sqrt_div (c : ℝ) :
    Measurable fun q : ℕ × ℝ ↦ q.2 / q.1 + √(c / q.1) := by
  fun_prop

/-- **Underestimation of an arm by its index, at one round.** In a run of any algorithm against
the stochastic bandit `Environment.bandit ν`, if arm `a` is σ²-sub-Gaussian with mean `μ_a` and
`σ² ≠ 0`, then for `L ≥ 0`, `ε ≥ 0` and every round `t`, the probability that `a` has been pulled
and its index `μ̂_a + √(2 σ² L / T_a)` is at most `μ_a - ε` is at most
`exp (-L) ∑_{s < t} exp (-(s + 1) ε² / (2 σ²))`. -/
theorem measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) {L : ℝ} (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (t : ℕ) :
    P.real {ω | pullCount A a t ω ≠ 0 ∧
        empMean A R a t ω + √(2 * σ2 * L / pullCount A a t ω) ≤ (ν a)[id] - ε} ≤
      exp (-L) * ∑ s ∈ range t, exp (-(ε ^ 2 / (2 * σ2) * (s + 1))) := by
  -- the event of round `t` is transferred to the reward stream with a union bound over the
  -- number of pulls
  refine (measureReal_pullCount_ne_zero_and_empMean_le_sum h a
    (fun s x ↦ x + √(2 * σ2 * L / s) ≤ (ν a)[id] - ε)
    (fun s hs ↦ measureReal_streamMeasure_div_add_sqrt_le_sub_le hν hσ2 hL hε hs) t).trans_eq ?_
  simp only [mul_sum, Nat.cast_add_one]

/-- **Underestimation of an arm by the index of [LS, Algorithm 6].** In a run of any algorithm
against the stochastic bandit `Environment.bandit ν`, if arm `a` is σ²-sub-Gaussian with mean `μ_a`
and `σ² ≠ 0`, then for `ε > 0` the expected number of rounds `t < n` at which `a` has been pulled
and its index `μ̂_a + √(2 σ² log f(t + 1) / T_a)` is at most `μ_a - ε` is at most `5 σ² / ε²`,
uniformly in `n`, where `f(t) = 1 + t log² t`. This bounds the contribution of an optimal arm in
the proof of [LS, Theorem 8.1]. -/
theorem sum_measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) (hε : 0 < ε)
    (n : ℕ) :
    ∑ t ∈ range n, P.real {ω | pullCount A a t ω ≠ 0 ∧
        empMean A R a t ω + √(2 * σ2 * log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A a t ω)
          ≤ (ν a)[id] - ε} ≤ 5 * σ2 / ε ^ 2 := by
  have hσ2' : (0 : ℝ) < σ2 := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ2)
  -- [LS, Exercise 8.1] for the sub-Gaussian rate `ε² / (2 σ²)`
  have h_sum := sum_range_inv_mul_sum_range_exp_neg_le
    (show 0 < ε ^ 2 / (2 * σ2) by positivity) n n
  rw [show 5 / 2 * (ε ^ 2 / (2 * σ2))⁻¹ = 5 * σ2 / ε ^ 2 by field_simp] at h_sum
  refine le_trans (sum_le_sum fun t ht ↦ ?_) h_sum
  -- at round `t < n`, the exploration level is `log f(t + 1)`, and `exp (-log f(t + 1))` is
  -- `1 / f(t + 1)`
  have hf : 0 < 1 + ((t : ℝ) + 1) * log (t + 1) ^ 2 := by positivity
  refine (measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le h a hν hσ2
    (log_nonneg (le_add_of_nonneg_right (by positivity))) hε.le t).trans ?_
  rw [exp_neg, exp_log hf]
  gcongr
  exact (mem_range.mp ht).le

/-- **Overestimation of an arm by its index.** In a run of any algorithm against the stochastic
bandit `Environment.bandit ν`, if arm `a` is σ²-sub-Gaussian with mean `μ_a`, then for `δ > 0` and
`c ≥ 0` the expected number of rounds `t < n` at which `a` is played while it has not been pulled
yet or its index `μ̂_a + √(2 σ² c / T_a)` exceeds `μ_a + δ` is at most
`1 + 2 σ² / δ² (c + √(π c) + 1)`, uniformly in `n`. This bounds the contribution of a suboptimal
arm in the proof of [LS, Theorem 8.1]. -/
theorem sum_measureReal_action_eq_and_pullCount_eq_zero_or_lt_empMean_add_sqrt_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {δ : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c)
    (n : ℕ) :
    ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
        (ν a)[id] + δ < empMean A R a t ω + √(2 * σ2 * c / pullCount A a t ω))} ≤
      1 + 2 * σ2 / δ ^ 2 * (c + √(π * c) + 1) := by
  set p : ℕ → ℝ → Prop := fun s x ↦ s = 0 ∨ (ν a)[id] + δ < x / s + √(2 * σ2 * c / s)
    with hp_def
  have hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2 :=
    (measurableSet_setOfPred.mp ((measurableSet_singleton 0).preimage measurable_fst)).or
      (measurableSet_setOfPred.mp (measurableSet_lt measurable_const
        (measurable_div_add_sqrt_div _)))
  -- the events are transferred to the reward stream, where [LS, Lemma 8.2] applies
  calc ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨
      (ν a)[id] + δ < empMean A R a t ω + √(2 * σ2 * c / pullCount A a t ω))}
  _ = ∑ t ∈ range n, P.real
      {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} := by
    simp only [hp_def, empMean]
  _ ≤ ∑ s ∈ range n, (streamMeasure ν).real {ω | p s (∑ i ∈ range s, ω i a)} :=
    sum_measureReal_action_eq_and_pullCount_sumRewards_le h a n hp
  _ ≤ ∑ s ∈ range n, (streamMeasure ν).real
      {ω | s * ((ν a)[id] + δ) ≤ ∑ i ∈ range s, ω i a + √(2 * σ2 * c * s)} := by
    refine sum_le_sum fun s _ ↦ measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
    simp only [hp_def, Set.mem_ofPred_eq] at hω ⊢
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    replace hω := hω.resolve_left hs0
    have hs : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs0)
    rw [div_add' _ _ _ hs.ne', lt_div_iff₀ hs] at hω
    have h_sqrt := mul_sqrt_div_eq_sqrt_mul (2 * σ2 * c) hs.le
    linarith
  _ ≤ 1 + 2 * σ2 / δ ^ 2 * (c + √(π * c) + 1) :=
    sum_measureReal_streamMeasure_mul_le_sum_add_sqrt_le hν hδ hc n

end Runs

/-! ### Rewards in `[0, 1]` and the KL-UCB index -/

section BoundedStream

variable {α : Type*} [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {a : α}

/-- In the i.i.d. reward stream model, the rewards of an arm whose law is concentrated on `[0, 1]`
lie in `[0, 1]` almost surely. -/
private lemma ae_mem_Icc_streamMeasure (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1) (i : ℕ) :
    ∀ᵐ ω ∂(streamMeasure ν), ω i a ∈ Set.Icc 0 1 :=
  (identDistrib_eval_eval_id_streamMeasure ν i a).symm.ae_snd measurableSet_Icc hν

/-- **Underestimation of the KL-UCB index in the stream model.** If the rewards of arm `a` lie in
`[0, 1]` almost surely and have mean `μ_a`, then for `ε > 0`, a real `L` and `s ≠ 0`, the
probability that the upper confidence level `U(μ̂_s, L / s)` of the empirical mean `μ̂_s` of the
first `s` rewards of `a` in the i.i.d. reward stream model is at most `μ_a - ε` is at most
`exp (-L) exp (-2 ε² s)`. -/
theorem measureReal_streamMeasure_klUpper_le_sub_le (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (hε : 0 < ε) (L : ℝ) {s : ℕ} (hs : s ≠ 0) :
    (streamMeasure ν).real {ω | klUpper ((∑ i ∈ range s, ω i a) / s) (ENNReal.ofReal (L / s)) ≤
        (ν a)[id] - ε} ≤ exp (-L) * exp (-(2 * ε ^ 2 * s)) := by
  have hμ : (ν a)[id] ∈ Set.Icc 0 1 := integral_id_mem_Icc_of_ae_mem_Icc hν
  have h := measureReal_klUpper_le_le (iIndepFun_eval_streamMeasure'' ν a) (s := range s)
    (nonempty_range_iff.2 hs)
    (fun i _ ↦ (by fun_prop : Measurable fun ω : ℕ → α → ℝ ↦ ω i a).aemeasurable)
    (fun i _ ↦ ae_mem_Icc_streamMeasure hν i)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.ge)
    (q := (ν a)[id] - ε) (by linarith [hμ.2]) (by linarith) L
  simpa only [card_range, sub_sub_cancel] using h

end BoundedStream

section BoundedRuns

variable {α : Type*} [DecidableEq α] [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {ν : Kernel α ℝ} [IsMarkovKernel ν] {alg : Algorithm Unit α ℝ}
  [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **Underestimation of an arm by the KL-UCB index, at one round.** In a run of any algorithm
against the stochastic bandit `Environment.bandit ν`, if the rewards of arm `a` lie in `[0, 1]`
almost surely and have mean `μ_a`, then for `ε > 0`, a real `L` and every round `t`, the probability
that `a` has been pulled and its upper confidence level `U(μ̂_a, L / T_a)` is at most `μ_a - ε` is
at most `exp (-L) ∑_{s < t} exp (-2 ε² (s + 1))`. -/
theorem measureReal_pullCount_ne_zero_and_klUpper_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (hε : 0 < ε) (L : ℝ) (t : ℕ) :
    P.real {ω | pullCount A a t ω ≠ 0 ∧
        klUpper (empMean A R a t ω) (ENNReal.ofReal (L / pullCount A a t ω)) ≤ (ν a)[id] - ε} ≤
      exp (-L) * ∑ s ∈ range t, exp (-(2 * ε ^ 2 * (s + 1))) := by
  -- the event of round `t` is transferred to the reward stream with a union bound over the
  -- number of pulls
  refine (measureReal_pullCount_ne_zero_and_empMean_le_sum h a
    (fun s x ↦ klUpper x (ENNReal.ofReal (L / s)) ≤ (ν a)[id] - ε)
    (fun s hs ↦ measureReal_streamMeasure_klUpper_le_sub_le hν hε L hs) t).trans_eq ?_
  simp only [mul_sum, Nat.cast_add_one]

/-- **Underestimation of an arm by the KL-UCB index** ([LS, Lemma 10.7] for rewards in
`[0, 1]`). In a run of any algorithm against the stochastic bandit `Environment.bandit ν`, if the
rewards of arm `a` lie in `[0, 1]` almost surely and have mean `μ_a`, then for `ε > 0` the expected
number of rounds `t < n` at which `a` has been pulled and its KL-UCB index
`U(μ̂_a, log f(t + 1) / T_a)` is at most `μ_a - ε` is at most `3 / (4 ε²)`, uniformly in `n`,
where `f(t) = 1 + t log² t`. This bounds the contribution of an optimal arm in the proof of
[LS, Theorem 10.6]. -/
theorem sum_measureReal_pullCount_ne_zero_and_klUpper_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (hε : 0 < ε) (n : ℕ) :
    ∑ t ∈ range n, P.real {ω | pullCount A a t ω ≠ 0 ∧
        klUpper (empMean A R a t ω)
          (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A a t ω)) ≤
            (ν a)[id] - ε} ≤ 3 / (4 * ε ^ 2) := by
  -- at round `t`, the exploration level is `log f(t + 1)`, and `exp (-log f(t + 1))` is
  -- `1 / f(t + 1)`
  calc ∑ t ∈ range n, P.real {ω | pullCount A a t ω ≠ 0 ∧
      klUpper (empMean A R a t ω)
        (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A a t ω)) ≤
          (ν a)[id] - ε}
  _ ≤ ∑ t ∈ range n, (1 + (t + 1) * log (t + 1) ^ 2)⁻¹ *
      ∑ s ∈ range t, exp (-(2 * ε ^ 2 * (s + 1))) := by
    refine sum_le_sum fun t _ ↦
      (measureReal_pullCount_ne_zero_and_klUpper_le_le h a hν hε _ t).trans_eq ?_
    rw [exp_neg, exp_log (by positivity)]
  _ ≤ 3 / 2 * (2 * ε ^ 2)⁻¹ := sum_range_inv_mul_sum_range_self_exp_neg_le (by positivity) n
  _ = 3 / (4 * ε ^ 2) := by
    field_simp
    ring

/-- **Overestimation of an arm by the KL-UCB index** ([LS, Lemma 10.8] for rewards in `[0, 1]`).
In a run of any algorithm against the stochastic bandit `Environment.bandit ν`, if the rewards of
arm `a` lie in `[0, 1]` almost surely and have mean `μ_a`, then for `ε > 0`, `c < 1` with
`μ_a + ε < c`, and `L ≥ 0`, the expected number of rounds `t < n` at which `a` is played while it
has not been pulled yet, or `c ≤ μ̂_a`, or `d(μ̂_a, c) ≤ L / T_a`, is at most
`1 + L / d(μ_a + ε, c) + 1 / (2 ε²)`, uniformly in `n`. This bounds the contribution of a
suboptimal arm in the proof of [LS, Theorem 10.6]. -/
theorem sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (hε : 0 < ε) (hc : (ν a)[id] + ε < c) (hc1 : c < 1) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
        klBer (empMean A R a t ω) c ≤ ENNReal.ofReal (L / pullCount A a t ω))} ≤
      1 + L / klBerReal ((ν a)[id] + ε) c + 1 / (2 * ε ^ 2) := by
  set p : ℕ → ℝ → Prop := fun s x ↦ s = 0 ∨ c ≤ x / s ∨
    klBer (x / s) c ≤ ENNReal.ofReal (L / s) with hp_def
  have hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2 :=
    (measurableSet_setOfPred.mp ((measurableSet_singleton 0).preimage measurable_fst)).or
      ((measurableSet_setOfPred.mp (measurableSet_le measurable_const (by fun_prop))).or
        (measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) (by fun_prop))))
  -- the events are transferred to the reward stream, where the bound for i.i.d. rewards applies
  calc ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
      klBer (empMean A R a t ω) c ≤ ENNReal.ofReal (L / pullCount A a t ω))}
  _ = ∑ t ∈ range n, P.real
      {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} := by
    simp only [hp_def, empMean]
  _ ≤ ∑ s ∈ range n, (streamMeasure ν).real {ω | p s (∑ i ∈ range s, ω i a)} :=
    sum_measureReal_action_eq_and_pullCount_sumRewards_le h a n hp
  _ ≤ 1 + L / klBerReal ((ν a)[id] + ε) c + 1 / (2 * ε ^ 2) :=
    sum_measureReal_eq_zero_or_le_div_or_klBer_div_le_le (iIndepFun_eval_streamMeasure'' ν a)
      (fun i ↦ (by fun_prop : Measurable fun ω : ℕ → α → ℝ ↦ ω i a).aemeasurable)
      (ae_mem_Icc_streamMeasure hν)
      (fun i ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.le)
      hε hc hc1 hL n

/-- **Time-uniform underestimation of an arm by its KL upper confidence level.** In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, if the rewards of arm `a` lie in
`[0, 1]` almost surely and have mean `μ_a`, and the exploration rate `β` is a function of the number
of pulls and the round, then the probability that at some round `n`, the arm `a` has been pulled
and its upper confidence level `U(μ̂_a(n), β(N_a(n), n) / N_a(n))` is less than `μ_a` is at most
`∑_n ∑_{u = 1}^n exp (-β(u, n))`. -/
theorem measureReal_exists_klUpper_lt_le_tsum
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    {β : ℕ → ℕ → ℝ} (hsum : Summable fun n ↦ ∑ u ∈ Finset.Icc 1 n, exp (-β u n)) :
    P.real {ω | ∃ n, pullCount A a n ω ≠ 0 ∧ klUpper (empMean A R a n ω)
        (ENNReal.ofReal (β (pullCount A a n ω) n / pullCount A a n ω)) < (ν a)[id]} ≤
      ∑' n, ∑ u ∈ Finset.Icc 1 n, exp (-β u n) := by
  refine le_trans ?_ (measureReal_exists_pullCount_sumRewards_le_tsum h a
    (fun n s x ↦ s ≠ 0 ∧ klUpper (x / s) (ENNReal.ofReal (β s n / s)) < (ν a)[id])
    (fun _ _ h0 ↦ h0.1 rfl) (fun n u ↦ ?_) hsum)
  · exact measureReal_mono fun ω ⟨n, hn⟩ ↦ ⟨n, by rwa [empMean] at hn⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simpa using (exp_pos _).le
  have h_cov := measureReal_klUpper_lt_le (iIndepFun_eval_streamMeasure'' ν a) (s := range u)
    (nonempty_range_iff.2 hu)
    (fun i _ ↦ (by fun_prop : Measurable fun ω : ℕ → α → ℝ ↦ ω i a).aemeasurable)
    (fun i _ ↦ ae_mem_Icc_streamMeasure hν i)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.ge) (β u n)
  rw [card_range] at h_cov
  exact le_trans (measureReal_mono fun ω hω ↦ hω.2) h_cov

/-- **Time-uniform overestimation of an arm by its KL lower confidence level.** In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, if the rewards of arm `a` lie in
`[0, 1]` almost surely and have mean `μ_a`, and the exploration rate `β` is a function of the number
of pulls and the round, then the probability that at some round `n`, the arm `a` has been pulled
and its lower confidence level `L(μ̂_a(n), β(N_a(n), n) / N_a(n))` is more than `μ_a` is at most
`∑_n ∑_{u = 1}^n exp (-β(u, n))`. -/
theorem measureReal_exists_lt_klLower_le_tsum
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    {β : ℕ → ℕ → ℝ} (hsum : Summable fun n ↦ ∑ u ∈ Finset.Icc 1 n, exp (-β u n)) :
    P.real {ω | ∃ n, pullCount A a n ω ≠ 0 ∧ (ν a)[id] < klLower (empMean A R a n ω)
        (ENNReal.ofReal (β (pullCount A a n ω) n / pullCount A a n ω))} ≤
      ∑' n, ∑ u ∈ Finset.Icc 1 n, exp (-β u n) := by
  refine le_trans ?_ (measureReal_exists_pullCount_sumRewards_le_tsum h a
    (fun n s x ↦ s ≠ 0 ∧ (ν a)[id] < klLower (x / s) (ENNReal.ofReal (β s n / s)))
    (fun _ _ h0 ↦ h0.1 rfl) (fun n u ↦ ?_) hsum)
  · exact measureReal_mono fun ω ⟨n, hn⟩ ↦ ⟨n, by rwa [empMean] at hn⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simpa using (exp_pos _).le
  have h_cov := measureReal_lt_klLower_le (iIndepFun_eval_streamMeasure'' ν a) (s := range u)
    (nonempty_range_iff.2 hu)
    (fun i _ ↦ (by fun_prop : Measurable fun ω : ℕ → α → ℝ ↦ ω i a).aemeasurable)
    (fun i _ ↦ ae_mem_Icc_streamMeasure hν i)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.le) (β u n)
  rw [card_range] at h_cov
  exact le_trans (measureReal_mono fun ω hω ↦ hω.2) h_cov

/-- **Deviations of an arm at one round, from bounds in the stream model.** In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, let `q s y` be a property of a
number of pulls `s` and an empirical mean `y` of arm `a`, and `x > 0`. If, in the i.i.d. reward
stream model, `q 1` holds for the first reward with probability at most `exp (-x)`, and for every
`n ≥ 2` the probability that `q s` holds for the empirical mean of the first `s` rewards for some
`s ∈ [1, n]` is at most `e ⌈x log n⌉ exp (-x)`, then at every round `n`, the probability that `a`
has been pulled and `q` holds for its number of pulls and its empirical mean is at most
`e (x log n + 1) exp (-x)`. -/
private lemma measureReal_pullCount_ne_zero_and_le_exp_one_mul_log_add_one_mul_exp
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (q : ℕ → ℝ → Prop) {x : ℝ}
    (hx : 0 < x)
    (h1 : (streamMeasure ν).real {ω | q 1 ((∑ i ∈ range 1, ω i a) / (1 : ℕ))} ≤ exp (-x))
    (h2 : ∀ n : ℕ, 1 < n → streamMeasure ν
      {ω | ∃ s : ℕ, 1 ≤ s ∧ s ≤ n ∧ q s ((∑ i ∈ range s, ω i a) / s)} ≤
        ENNReal.ofReal (exp 1 * ⌈x * log n⌉₊ * exp (-x)))
    (n : ℕ) :
    P.real {ω | pullCount A a n ω ≠ 0 ∧ q (pullCount A a n ω) (empMean A R a n ω)} ≤
      exp 1 * (x * log n + 1) * exp (-x) := by
  have h_log : 0 ≤ log n := log_natCast_nonneg n
  -- the event of round `n` is transferred to the reward stream, with `N_a(n) ≤ n` pulls
  have h_tr : P.real {ω | pullCount A a n ω ≠ 0 ∧ q (pullCount A a n ω) (empMean A R a n ω)} ≤
      (streamMeasure ν).real
        {ω | ∃ s < n + 1, s ≠ 0 ∧ q s ((∑ i ∈ range s, ω i a) / s)} := by
    have h_le := measure_exists_lt_pullCount_sumRewards_le h a (n + 1)
      fun s y ↦ s ≠ 0 ∧ q s (y / s)
    refine le_trans (measureReal_mono fun ω hω ↦ ?_) (ENNReal.toReal_mono (measure_ne_top _ _) h_le)
    simp only [Set.mem_ofPred_eq, empMean] at hω ⊢
    exact ⟨n, lt_add_one n, hω⟩
  refine h_tr.trans ?_
  rcases n with _ | _ | n
  · -- no arm has been pulled before the first round
    have h_empty : {ω : ℕ → α → ℝ | ∃ s < 0 + 1, s ≠ 0 ∧ q s ((∑ i ∈ range s, ω i a) / s)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω ⟨s, hs, hs0, _⟩ ↦ hs0 (by omega)
    rw [h_empty, measureReal_empty]
    positivity
  · -- after one round, the arm has been pulled once
    refine le_trans (measureReal_mono (s₂ := {ω | q 1 ((∑ i ∈ range 1, ω i a) / (1 : ℕ))})
      fun ω hω ↦ ?_) (h1.trans ?_)
    · obtain ⟨s, hs, hs0, hq⟩ := hω
      obtain rfl : s = 1 := by omega
      exact hq
    · simpa using le_mul_of_one_le_left (exp_pos (-x)).le (one_le_exp zero_le_one)
  · -- after `n + 2 ≥ 2` rounds, the self-normalized bound applies
    refine le_trans (measureReal_mono (s₂ := {ω | ∃ s : ℕ, 1 ≤ s ∧ s ≤ n + 2 ∧
      q s ((∑ i ∈ range s, ω i a) / s)}) fun ω hω ↦ ?_) ?_
    · obtain ⟨s, hs, hs0, hq⟩ := hω
      exact ⟨s, Nat.one_le_iff_ne_zero.2 hs0, Nat.lt_add_one_iff.1 hs, hq⟩
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ((h2 (n + 2) (by omega)).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_ceil := Nat.ceil_lt_add_one (mul_nonneg hx.le (log_natCast_nonneg (n + 2)))
    gcongr

/-- **Underestimation of an arm by its KL upper confidence level, at one round**
[KK13, Lemma 4, (13)], from the self-normalized deviations of [GC11, Theorem 10]. In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, if the rewards of arm `a` lie in
`[0, 1]` almost surely and have mean `μ_a`, then for `x > 0` and every round `n`, the probability
that `a` has been pulled and its upper confidence level `U(μ̂_a, x / N_a)` is less than `μ_a` is
at most `e (x log n + 1) exp (-x)`, whatever the number of pulls `N_a`. -/
theorem measureReal_pullCount_ne_zero_and_klUpper_lt_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    P.real {ω | pullCount A a n ω ≠ 0 ∧
        klUpper (empMean A R a n ω) (ENNReal.ofReal (x / pullCount A a n ω)) < (ν a)[id]} ≤
      exp 1 * (x * log n + 1) * exp (-x) := by
  refine measureReal_pullCount_ne_zero_and_le_exp_one_mul_log_add_one_mul_exp h a
    (fun s y ↦ klUpper y (ENNReal.ofReal (x / s)) < (ν a)[id]) hx ?_
    (fun n hn ↦ measure_exists_klUpper_lt_le (iIndepFun_eval_streamMeasure'' ν a)
      (fun i ↦ by fun_prop) (ae_mem_Icc_streamMeasure hν)
      (fun i ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.ge) hx hn) n
  have h_cov := measureReal_klUpper_lt_le (iIndepFun_eval_streamMeasure'' ν a) (s := range 1)
    (nonempty_range_iff.2 one_ne_zero)
    (fun i _ ↦ (by fun_prop : Measurable fun ω : ℕ → α → ℝ ↦ ω i a).aemeasurable)
    (fun i _ ↦ ae_mem_Icc_streamMeasure hν i)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.ge) x
  rwa [card_range] at h_cov

/-- **Overestimation of an arm by its KL lower confidence level, at one round**
[KK13, Lemma 4, (13)], from the self-normalized deviations of [GC11, Theorem 10]. In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, if the rewards of arm `a` lie in
`[0, 1]` almost surely and have mean `μ_a`, then for `x > 0` and every round `n`, the probability
that `a` has been pulled and its lower confidence level `L(μ̂_a, x / N_a)` is more than `μ_a` is
at most `e (x log n + 1) exp (-x)`, whatever the number of pulls `N_a`. -/
theorem measureReal_pullCount_ne_zero_and_lt_klLower_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    P.real {ω | pullCount A a n ω ≠ 0 ∧
        (ν a)[id] < klLower (empMean A R a n ω) (ENNReal.ofReal (x / pullCount A a n ω))} ≤
      exp 1 * (x * log n + 1) * exp (-x) := by
  refine measureReal_pullCount_ne_zero_and_le_exp_one_mul_log_add_one_mul_exp h a
    (fun s y ↦ (ν a)[id] < klLower y (ENNReal.ofReal (x / s))) hx ?_
    (fun n hn ↦ measure_exists_lt_klLower_le (iIndepFun_eval_streamMeasure'' ν a)
      (fun i ↦ by fun_prop) (ae_mem_Icc_streamMeasure hν)
      (fun i ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.le) hx hn) n
  have h_cov := measureReal_lt_klLower_le (iIndepFun_eval_streamMeasure'' ν a) (s := range 1)
    (nonempty_range_iff.2 one_ne_zero)
    (fun i _ ↦ (by fun_prop : Measurable fun ω : ℕ → α → ℝ ↦ ω i a).aemeasurable)
    (fun i _ ↦ ae_mem_Icc_streamMeasure hν i)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.le) x
  rwa [card_range] at h_cov

end BoundedRuns

/-! ### Arms dominated by an exponential family and the KL-UCB index -/

section ExpFamilyStream

variable {α 𝓧 : Type*} [MeasurableSpace α] {m𝓧 : MeasurableSpace 𝓧} {ν : Kernel α ℝ}
  [IsMarkovKernel ν] {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {a : α} {μ : ℝ}

/-- **Underestimation of the KL-UCB index of an exponential family in the stream model.** If the
rewards of arm `a` are dominated on `Set.Iic 0` by the member of mean `μ` of the exponential family
of `ρ` and `T`, then for `ε > 0` with `μ - ε` a mean of the family, a real `L` and `s ≠ 0`, the
probability that the upper confidence level `U(μ̂_s, L / s)` of the empirical mean `μ̂_s` of the
first `s` rewards of `a` in the i.i.d. reward stream model is at most `μ - ε` is at most
`exp (-L) exp (-(s d(μ - ε, μ)))`. -/
theorem measureReal_streamMeasure_expFamilyUpper_le_sub_le
    (hν : MGFDominatedOn id (ν a) T (ρ.expFamily T (ρ.natParam T μ)) (Set.Iic 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hε : 0 < ε) (hμε : μ - ε ∈ ρ.expFamilyMeans T) (L : ℝ)
    {s : ℕ} (hs : s ≠ 0) :
    (streamMeasure ν).real {ω | ρ.expFamilyUpper T ((∑ i ∈ range s, ω i a) / s)
        (ENNReal.ofReal (L / s)) ≤ ((μ - ε : ℝ) : EReal)} ≤
      exp (-L) * exp (-(s * ρ.expFamilyDiv T (μ - ε) μ)) := by
  have h := (iIndepFun_eval_streamMeasure'' ν a).measureReal_expFamilyUpper_le_le
    (s := range s) (nonempty_range_iff.2 hs)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedOn.trans hν) hμ hμε
    (by linarith) L
  simpa only [card_range] using h

end ExpFamilyStream

section ExpFamilyRuns

variable {α 𝓧 : Type*} [DecidableEq α] [MeasurableSpace α] [Countable α]
  [MeasurableSingletonClass α] {m𝓧 : MeasurableSpace 𝓧} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {alg : Algorithm Unit α ℝ} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {R : ℕ → Ω → ℝ} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {μ : ℝ}

/-- **Underestimation of an arm by the KL-UCB index of an exponential family, at one round.** In a
run of any algorithm against the stochastic bandit `Environment.bandit ν`, if the rewards of arm
`a` are dominated on `Set.Iic 0` by the member of mean `μ` of the exponential family of `ρ` and
`T`, then for `ε > 0` with `μ - ε` a mean of the family, a real `L` and every round `t`, the
probability that `a` has been pulled and its upper confidence level `U(μ̂_a, L / T_a)` is at most
`μ - ε` is at most `exp (-L) ∑_{s < t} exp (-(d(μ - ε, μ) (s + 1)))`. -/
theorem measureReal_pullCount_ne_zero_and_expFamilyUpper_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α)
    (hν : MGFDominatedOn id (ν a) T (ρ.expFamily T (ρ.natParam T μ)) (Set.Iic 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hε : 0 < ε) (hμε : μ - ε ∈ ρ.expFamilyMeans T) (L : ℝ)
    (t : ℕ) :
    P.real {ω | pullCount A a t ω ≠ 0 ∧ ρ.expFamilyUpper T (empMean A R a t ω)
        (ENNReal.ofReal (L / pullCount A a t ω)) ≤ ((μ - ε : ℝ) : EReal)} ≤
      exp (-L) * ∑ s ∈ range t, exp (-(ρ.expFamilyDiv T (μ - ε) μ * (s + 1))) := by
  -- the event of round `t` is transferred to the reward stream with a union bound over the
  -- number of pulls
  refine (measureReal_pullCount_ne_zero_and_empMean_le_sum h a
    (fun s x ↦ ρ.expFamilyUpper T x (ENNReal.ofReal (L / s)) ≤ ((μ - ε : ℝ) : EReal))
    (fun s hs ↦ measureReal_streamMeasure_expFamilyUpper_le_sub_le hν hμ hε hμε L hs) t).trans_eq ?_
  simp only [mul_sum, Nat.cast_add_one, mul_comm _ (ρ.expFamilyDiv T (μ - ε) μ)]

/-- **Underestimation of an arm by the KL-UCB index of an exponential family** (the
generalization of [LS, Lemma 10.7] to exponential families). In a run of any algorithm against
the stochastic bandit `Environment.bandit ν`, if the rewards of arm `a` are dominated on
`Set.Iic 0` by the member of mean `μ` of the exponential family of `ρ` and `T`, then for `ε > 0`
with `μ - ε` a mean of the family, the expected number of rounds `t < n` at which `a` has been
pulled and its KL-UCB index `U(μ̂_a, log f(t + 1) / T_a)` is at most `μ - ε` is at most
`3 / (2 d(μ - ε, μ))`, uniformly in `n`, where `f(t) = 1 + t log² t`. This bounds the contribution
of an optimal arm in the regret analysis of KL-UCB. -/
theorem sum_measureReal_pullCount_ne_zero_and_expFamilyUpper_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α)
    (hν : MGFDominatedOn id (ν a) T (ρ.expFamily T (ρ.natParam T μ)) (Set.Iic 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hε : 0 < ε) (hμε : μ - ε ∈ ρ.expFamilyMeans T) (n : ℕ) :
    ∑ t ∈ range n, P.real {ω | pullCount A a t ω ≠ 0 ∧ ρ.expFamilyUpper T (empMean A R a t ω)
        (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A a t ω)) ≤
          ((μ - ε : ℝ) : EReal)} ≤ 3 / (2 * ρ.expFamilyDiv T (μ - ε) μ) := by
  have hd : 0 < ρ.expFamilyDiv T (μ - ε) μ := Measure.expFamilyDiv_pos hμε hμ (by linarith)
  -- at round `t`, the exploration level is `log f(t + 1)`, and `exp (-log f(t + 1))` is
  -- `1 / f(t + 1)`
  calc ∑ t ∈ range n, P.real {ω | pullCount A a t ω ≠ 0 ∧ ρ.expFamilyUpper T (empMean A R a t ω)
        (ENNReal.ofReal (log (1 + (t + 1) * log (t + 1) ^ 2) / pullCount A a t ω)) ≤
          ((μ - ε : ℝ) : EReal)}
  _ ≤ ∑ t ∈ range n, (1 + (t + 1) * log (t + 1) ^ 2)⁻¹ *
      ∑ s ∈ range t, exp (-(ρ.expFamilyDiv T (μ - ε) μ * (s + 1))) := by
    refine sum_le_sum fun t _ ↦
      (measureReal_pullCount_ne_zero_and_expFamilyUpper_le_le h a hν hμ hε hμε _ t).trans_eq ?_
    rw [exp_neg, exp_log (by positivity)]
  _ ≤ 3 / 2 * (ρ.expFamilyDiv T (μ - ε) μ)⁻¹ := sum_range_inv_mul_sum_range_self_exp_neg_le hd n
  _ = 3 / (2 * ρ.expFamilyDiv T (μ - ε) μ) := by
    field_simp

/-- **Overestimation of an arm by the KL-UCB index of an exponential family** (the
generalization of [LS, Lemma 10.8] to exponential families). In a run of any algorithm against
the stochastic bandit `Environment.bandit ν`, if the rewards of arm `a` are dominated on
`Set.Ici 0` by the member of mean `μ` of the exponential family of `ρ` and `T`, then for `ε > 0`
and `c > μ + ε` with `μ + ε` and `c` means of the family, and `L ≥ 0`, the expected number of
rounds `t < n` at which `a` is played while it has not been pulled yet, or `c ≤ μ̂_a`, or
`dbar(μ̂_a, c) ≤ L / T_a`, is at most `1 + L / d(μ + ε, c) + 1 / d(μ + ε, μ)`, uniformly in `n`.
This bounds the contribution of a suboptimal arm in the regret analysis of KL-UCB. -/
theorem sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_expFamilyRate_le_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α)
    (hν : MGFDominatedOn id (ν a) T (ρ.expFamily T (ρ.natParam T μ)) (Set.Ici 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hε : 0 < ε) (hc : μ + ε < c)
    (hμε : μ + ε ∈ ρ.expFamilyMeans T) (hcM : c ∈ ρ.expFamilyMeans T) {L : ℝ} (hL : 0 ≤ L)
    (n : ℕ) :
    ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
        ρ.expFamilyRate T (empMean A R a t ω) c ≤ ENNReal.ofReal (L / pullCount A a t ω))} ≤
      1 + L / ρ.expFamilyDiv T (μ + ε) c + 1 / ρ.expFamilyDiv T (μ + ε) μ := by
  set p : ℕ → ℝ → Prop := fun s x ↦ s = 0 ∨ c ≤ x / s ∨
    ρ.expFamilyRate T (x / s) c ≤ ENNReal.ofReal (L / s) with hp_def
  have hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2 :=
    (measurableSet_setOfPred.mp ((measurableSet_singleton 0).preimage measurable_fst)).or
      ((measurableSet_setOfPred.mp (measurableSet_le measurable_const (by fun_prop))).or
        (measurableSet_setOfPred.mp (measurableSet_le
          ((Measure.lowerSemicontinuous_expFamilyRate_left c).measurable.comp (by fun_prop))
          (by fun_prop))))
  -- the events are transferred to the reward stream, where the bound for independent rewards
  -- applies
  calc ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
      ρ.expFamilyRate T (empMean A R a t ω) c ≤ ENNReal.ofReal (L / pullCount A a t ω))}
  _ = ∑ t ∈ range n, P.real
      {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} := by
    simp only [hp_def, empMean]
  _ ≤ ∑ s ∈ range n, (streamMeasure ν).real {ω | p s (∑ i ∈ range s, ω i a)} :=
    sum_measureReal_action_eq_and_pullCount_sumRewards_le h a n hp
  _ ≤ 1 + L / ρ.expFamilyDiv T (μ + ε) c + 1 / ρ.expFamilyDiv T (μ + ε) μ :=
    iIndepFun.sum_measureReal_eq_zero_or_le_div_or_expFamilyRate_div_le_le
      (iIndepFun_eval_streamMeasure'' ν a)
      (fun i ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedOn.trans hν)
      hμ hε hc hμε hcM hL n

end ExpFamilyRuns

end LMLExplore.Bandits
