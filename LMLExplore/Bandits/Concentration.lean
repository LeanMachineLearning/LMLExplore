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
public import LMLExplore.SequentialLearning.SumRewards
public import LMLExplore.Probability.Moments.KLChernoff
public import LMLExplore.Probability.Moments.SubGaussian.Sum
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
`μ̂_s ≥ μ + ε`, which Hoeffding's inequality makes rare, or `s d(μ + ε, c) ≤ L`, which bounds `s`
[LS, Lemma 10.8]. The index of an optimal arm is at most its mean minus `ε` at round `t` with
probability at most `(1 / f(t)) ∑_{s ≥ 1} exp (-2 s ε²)`, by the three-point inequality for `d`
and the Chernoff bound in relative-entropy form [LS, Lemma 10.7].

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
  `stationaryEnv ν`, the probability that at round `t` a pulled arm has index
  `μ̂_a + √(2 σ² L / T_a)` at most its mean minus `ε` is at most
  `exp (-L) ∑_{s < t} exp (-(s + 1) ε² / (2 σ²))`.
* `sum_measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le`: with the exploration level
  `log f(t + 1)` at Lean round `t`, the expected number of rounds of underestimation by `ε` is at
  most `5 σ² / ε²`.
* `sum_measureReal_action_eq_and_pullCount_eq_zero_or_lt_empMean_add_sqrt_le`: in a run of any
  algorithm, the expected number of rounds at which an arm is played before its first pull or with
  an index above its mean plus `δ > 0` is at most `1 + 2 σ² / δ² (c + √(π c) + 1)`, by
  [LS, Lemma 8.2] on the stream.
* `sum_measureReal_eq_zero_or_le_div_or_klBer_div_le_le`: [LS, Lemma 10.8] for independent
  `[0, 1]`-valued random variables with means at most `m`: for `m + ε < c < 1` and `L ≥ 0`, the
  expected number of sample sizes `s < n` at which `s = 0`, `c ≤ μ̂_s` or `d(μ̂_s, c) ≤ L / s` is
  at most `1 + L / d(m + ε, c) + 1 / (2 ε²)`.
* `measureReal_streamMeasure_klUpper_le_sub_le`: in the reward stream model, the KL-UCB index
  `U(μ̂_s, L / s)` of the first `s ≥ 1` rewards of an arm with rewards in `[0, 1]` is at most its
  mean minus `ε > 0` with probability at most `exp (-L) exp (-2 ε² s)`.
* `measureReal_pullCount_ne_zero_and_klUpper_le_le`: in a run of any algorithm, the probability
  that at round `t` a pulled arm has KL-UCB index `U(μ̂_a, L / T_a)` at most its mean minus `ε` is
  at most `exp (-L) ∑_{s < t} exp (-2 ε² (s + 1))`.
* `sum_measureReal_pullCount_ne_zero_and_klUpper_le_le`: [LS, Lemma 10.7] in a run of any
  algorithm: with the exploration level `log f(t + 1)` at Lean round `t`, the expected number of
  rounds of underestimation by `ε` is at most `3 / (4 ε²)`.
* `sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le`: in a run of any
  algorithm, the expected number of rounds at which an arm is played before its first pull, or with
  `c ≤ μ̂_a`, or with `d(μ̂_a, c) ≤ L / T_a`, is at most `1 + L / d(μ_a + ε, c) + 1 / (2 ε²)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemmas 8.2, 10.7 and 10.8, and Theorems 8.1 and 10.6.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set Learning Bandits

open scoped NNReal

namespace LMLExplore.Bandits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ} {σ2 : ℝ≥0}
  {ε c : ℝ}

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
the stochastic bandit `stationaryEnv ν`, if arm `a` is σ²-sub-Gaussian with mean `μ_a` and
`σ² ≠ 0`, then for `L ≥ 0`, `ε ≥ 0` and every round `t`, the probability that `a` has been pulled
and its index `μ̂_a + √(2 σ² L / T_a)` is at most `μ_a - ε` is at most
`exp (-L) ∑_{s < t} exp (-(s + 1) ε² / (2 σ²))`. -/
theorem measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0) {L : ℝ} (hL : 0 ≤ L)
    (hε : 0 ≤ ε) (t : ℕ) :
    P.real {ω | pullCount A a t ω ≠ 0 ∧
        empMean A R a t ω + √(2 * σ2 * L / pullCount A a t ω) ≤ (ν a)[id] - ε} ≤
      exp (-L) * ∑ s ∈ range t, exp (-(ε ^ 2 / (2 * σ2) * (s + 1))) := by
  set p : ℕ → ℝ → Prop := fun s x ↦ s ≠ 0 ∧ x / s + √(2 * σ2 * L / s) ≤ (ν a)[id] - ε with hp_def
  -- the event of round `t` is the event `p` for the number of pulls and the sum of rewards, which
  -- is transferred to the reward stream with a union bound over the number of pulls
  calc P.real {ω | pullCount A a t ω ≠ 0 ∧
      empMean A R a t ω + √(2 * σ2 * L / pullCount A a t ω) ≤ (ν a)[id] - ε}
  _ ≤ ∑ s ∈ range t, (streamMeasure ν).real {ω | p (s + 1) (∑ i ∈ range (s + 1), ω i a)} := by
    refine le_trans (measureReal_mono fun ω hω ↦ ?_)
      (measureReal_pullCount_sumRewards_le_sum h a p (fun _ h0 ↦ h0.1 rfl) t)
    simp only [Set.mem_ofPred_eq, empMean] at hω
    exact hω
  _ ≤ ∑ s ∈ range t, exp (-L) * exp (-(ε ^ 2 / (2 * σ2) * (s + 1))) := by
    refine sum_le_sum fun s _ ↦ ?_
    have h := measureReal_streamMeasure_div_add_sqrt_le_sub_le hν hσ2 hL hε (Nat.succ_ne_zero s)
    push_cast at h
    refine le_trans (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)) h
    simp only [hp_def, Set.mem_ofPred_eq, Nat.cast_add_one] at hω
    exact hω.2
  _ = exp (-L) * ∑ s ∈ range t, exp (-(ε ^ 2 / (2 * σ2) * (s + 1))) := (mul_sum _ _ _).symm

/-- **Underestimation of an arm by the index of [LS, Algorithm 6].** In a run of any algorithm
against the stochastic bandit `stationaryEnv ν`, if arm `a` is σ²-sub-Gaussian with mean `μ_a` and
`σ² ≠ 0`, then for `ε > 0` the expected number of rounds `t < n` at which `a` has been pulled and
its index `μ̂_a + √(2 σ² log f(t + 1) / T_a)` is at most `μ_a - ε` is at most `5 σ² / ε²`,
uniformly in `n`, where `f(t) = 1 + t log² t`. This bounds the contribution of an optimal arm in
the proof of [LS, Theorem 8.1]. -/
theorem sum_measureReal_pullCount_ne_zero_and_empMean_add_sqrt_le_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α)
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
bandit `stationaryEnv ν`, if arm `a` is σ²-sub-Gaussian with mean `μ_a`, then for `δ > 0` and
`c ≥ 0` the expected number of rounds `t < n` at which `a` is played while it has not been pulled
yet or its index `μ̂_a + √(2 σ² c / T_a)` exceeds `μ_a + δ` is at most
`1 + 2 σ² / δ² (c + √(π c) + 1)`, uniformly in `n`. This bounds the contribution of a suboptimal
arm in the proof of [LS, Theorem 8.1]. -/
theorem sum_measureReal_action_eq_and_pullCount_eq_zero_or_lt_empMean_add_sqrt_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α)
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

section Bounded

variable {m : ℝ}

/-- The number of `s < k` with `(s + 1) D ≤ L` is at most `L / D`, for `D > 0` and `L ≥ 0`. -/
private lemma sum_range_ite_add_one_mul_le_le {D L : ℝ} (hD : 0 < D) (hL : 0 ≤ L) (k : ℕ) :
    ∑ s ∈ range k, (if (s + 1) * D ≤ L then (1 : ℝ) else 0) ≤ L / D := by
  rw [sum_boole]
  refine le_trans ?_ (Nat.floor_le (div_nonneg hL hD.le))
  refine Nat.cast_le.2 ((card_le_card fun s hs ↦ ?_).trans (card_range _).le)
  rw [mem_filter] at hs
  rw [Finset.mem_range, Nat.lt_iff_add_one_le]
  refine Nat.le_floor ?_
  rw [le_div_iff₀ hD]
  exact_mod_cast hs.2

/-- **Overestimation of the KL-UCB index** ([LS, Lemma 10.8] for rewards in `[0, 1]`). Let
`X₀, X₁, …` be independent, in `[0, 1]`, with means at most `m`, let `ε > 0` and `c < 1` with
`m + ε < c`, and let `L ≥ 0`. Then the expected number of sample sizes `s < n` at which `s = 0`, or
the empirical mean `μ̂_s = (X₀ + ⋯ + X_{s-1}) / s` is at least `c`, or `d(μ̂_s, c) ≤ L / s`, is at
most `1 + L / d(m + ε, c) + 1 / (2 ε²)`, uniformly in `n`. For an arm of mean `m`, `c` below the
optimal mean and `L = log f(n)`, this bounds the number of sample sizes at which the KL-UCB index
of the arm exceeds `c`. -/
theorem sum_measureReal_eq_zero_or_le_div_or_klBer_div_le_le (h_indep : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P) (hX : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc 0 1)
    (hmean : ∀ i, P[X i] ≤ m) (hε : 0 < ε) (hc : m + ε < c) (hc1 : c < 1) {L : ℝ} (hL : 0 ≤ L)
    (n : ℕ) :
    ∑ s ∈ range n, P.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
        klBer ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)} ≤
      1 + L / klBerReal (m + ε) c + 1 / (2 * ε ^ 2) := by
  have := h_indep.isProbabilityMeasure
  have hm0 : 0 ≤ m := (integral_nonneg_of_ae ((hX 0).mono fun ω hω ↦ hω.1)).trans (hmean 0)
  have hme : m + ε ∈ Set.Icc 0 1 := ⟨by linarith, by linarith⟩
  have hc' : c ∈ Set.Ioo 0 1 := ⟨by linarith, hc1⟩
  set D := klBerReal (m + ε) c with hD_def
  have hD : 0 < D := by
    have := two_mul_sq_le_klBerReal hme (Set.Ioo_subset_Icc_self hc') (klBer_ne_top hc')
    nlinarith
  -- the term of `s` is at most `1` if `s D ≤ L`, and otherwise at most the Hoeffding bound
  -- `exp (-2 ε² s)`: if `μ̂_s < m + ε`, then `D ≤ d(μ̂_s, c)`, and `μ̂_s < c`
  have h_term (s : ℕ) : P.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
      klBer ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)} ≤
        if s * D ≤ L then 1 else exp (-(2 * ε ^ 2 * s)) := by
    split_ifs with hsD
    · exact measureReal_le_one
    have h_hoeffding := measureReal_card_mul_add_le_sum_le h_indep (s := range s)
      (fun i _ ↦ hXm i) (fun i _ ↦ hX i) (fun i _ ↦ hmean i) hε.le
    rw [card_range] at h_hoeffding
    refine le_trans (measureReal_mono fun ω hω ↦ ?_) h_hoeffding
    have hs : s ≠ 0 := by
      rintro rfl
      simp only [CharP.cast_eq_zero, zero_mul] at hsD
      exact hsD hL
    have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra! hlt
    have hx : (∑ i ∈ range s, X i ω) / s < m + ε := by rwa [div_lt_iff₀ hs', mul_comm]
    rcases hω with h0 | hcx | hkl
    · exact hs h0
    · linarith
    · refine hsD ?_
      have h1 : klBer (m + ε) c ≤ klBer ((∑ i ∈ range s, X i ω) / s) c :=
        antitoneOn_klBer_left c (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 hc.le) hx.le
      rw [klBer_eq_ofReal_klBerReal hme (Set.Ioo_subset_Icc_self hc') (klBer_ne_top hc')] at h1
      have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans hkl)
      rw [le_div_iff₀ hs'] at h2
      linarith
  calc ∑ s ∈ range n, P.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
      klBer ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)}
  _ ≤ ∑ s ∈ range n, (if s * D ≤ L then 1 else exp (-(2 * ε ^ 2 * s))) :=
    sum_le_sum fun s _ ↦ h_term s
  _ ≤ 1 + L / D + 1 / (2 * ε ^ 2) := by
    rcases n with _ | k
    · simp only [range_zero, sum_empty]
      positivity
    -- the term of `s = 0` is `1`; the others are at most `1_{(s + 1) D ≤ L} + exp (-2 ε² (s + 1))`
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, hL, ite_true, Nat.cast_add_one]
    calc ∑ s ∈ range k, (if (s + 1) * D ≤ L then 1 else exp (-(2 * ε ^ 2 * (s + 1)))) + 1
    _ ≤ ∑ s ∈ range k, ((if (s + 1) * D ≤ L then (1 : ℝ) else 0) +
        exp (-(2 * ε ^ 2 * (s + 1)))) + 1 := by
      gcongr with s
      split_ifs <;> simp [exp_nonneg]
    _ ≤ L / D + (2 * ε ^ 2)⁻¹ + 1 := by
      rw [sum_add_distrib]
      gcongr
      · exact sum_range_ite_add_one_mul_le_le hD hL k
      · exact sum_range_exp_neg_mul_le (by positivity) k
    _ = 1 + L / D + 1 / (2 * ε ^ 2) := by ring

end Bounded

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
against the stochastic bandit `stationaryEnv ν`, if the rewards of arm `a` lie in `[0, 1]` almost
surely and have mean `μ_a`, then for `ε > 0`, a real `L` and every round `t`, the probability that
`a` has been pulled and its upper confidence level `U(μ̂_a, L / T_a)` is at most `μ_a - ε` is at
most `exp (-L) ∑_{s < t} exp (-2 ε² (s + 1))`. -/
theorem measureReal_pullCount_ne_zero_and_klUpper_le_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (hε : 0 < ε) (L : ℝ) (t : ℕ) :
    P.real {ω | pullCount A a t ω ≠ 0 ∧
        klUpper (empMean A R a t ω) (ENNReal.ofReal (L / pullCount A a t ω)) ≤ (ν a)[id] - ε} ≤
      exp (-L) * ∑ s ∈ range t, exp (-(2 * ε ^ 2 * (s + 1))) := by
  set p : ℕ → ℝ → Prop :=
    fun s x ↦ s ≠ 0 ∧ klUpper (x / s) (ENNReal.ofReal (L / s)) ≤ (ν a)[id] - ε with hp_def
  -- the event of round `t` is transferred to the reward stream with a union bound over the
  -- number of pulls
  calc P.real {ω | pullCount A a t ω ≠ 0 ∧
      klUpper (empMean A R a t ω) (ENNReal.ofReal (L / pullCount A a t ω)) ≤ (ν a)[id] - ε}
  _ ≤ ∑ s ∈ range t, (streamMeasure ν).real {ω | p (s + 1) (∑ i ∈ range (s + 1), ω i a)} := by
    refine le_trans (measureReal_mono fun ω hω ↦ ?_)
      (measureReal_pullCount_sumRewards_le_sum h a p (fun _ h0 ↦ h0.1 rfl) t)
    simp only [Set.mem_ofPred_eq, empMean] at hω
    exact hω
  _ ≤ ∑ s ∈ range t, exp (-L) * exp (-(2 * ε ^ 2 * (s + 1))) := by
    refine sum_le_sum fun s _ ↦ ?_
    have h := measureReal_streamMeasure_klUpper_le_sub_le hν hε L (Nat.succ_ne_zero s)
    push_cast at h
    refine le_trans (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)) h
    simp only [hp_def, Set.mem_ofPred_eq, Nat.cast_add_one] at hω
    exact hω.2
  _ = exp (-L) * ∑ s ∈ range t, exp (-(2 * ε ^ 2 * (s + 1))) := (mul_sum _ _ _).symm

/-- **Underestimation of an arm by the KL-UCB index** ([LS, Lemma 10.7] for rewards in
`[0, 1]`). In a run of any algorithm against the stochastic bandit `stationaryEnv ν`, if the
rewards of arm `a` lie in `[0, 1]` almost surely and have mean `μ_a`, then for `ε > 0` the expected
number of rounds `t < n` at which `a` has been pulled and its KL-UCB index
`U(μ̂_a, log f(t + 1) / T_a)` is at most `μ_a - ε` is at most `3 / (4 ε²)`, uniformly in `n`,
where `f(t) = 1 + t log² t`. This bounds the contribution of an optimal arm in the proof of
[LS, Theorem 10.6]. -/
theorem sum_measureReal_pullCount_ne_zero_and_klUpper_le_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
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
  _ ≤ 3 / (4 * ε ^ 2) := by
    -- the term of round `0` vanishes, and `∑_{t ≥ 1} 1 / f(t + 1) ≤ 5 / 2 - 1 / f(1) = 3 / 2`
    rcases n with _ | k
    · simp only [range_zero, sum_empty]
      positivity
    rw [sum_range_succ']
    simp only [range_zero, sum_empty, mul_zero, add_zero]
    have h_sum := sum_range_inv_one_add_mul_log_sq_le (k + 1)
    rw [sum_range_succ'] at h_sum
    simp only [Nat.cast_zero, zero_add, log_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero, inv_one] at h_sum
    calc ∑ t ∈ range k, (1 + ((t + 1 : ℕ) + 1) * log ((t + 1 : ℕ) + 1) ^ 2)⁻¹ *
        ∑ s ∈ range (t + 1), exp (-(2 * ε ^ 2 * (s + 1)))
    _ ≤ ∑ t ∈ range k, (1 + ((t + 1 : ℕ) + 1) * log ((t + 1 : ℕ) + 1) ^ 2)⁻¹ *
        (2 * ε ^ 2)⁻¹ := by
      gcongr with t
      exact sum_range_exp_neg_mul_le (by positivity) _
    _ = (∑ t ∈ range k, (1 + ((t + 1 : ℕ) + 1) * log ((t + 1 : ℕ) + 1) ^ 2)⁻¹) *
        (2 * ε ^ 2)⁻¹ := (sum_mul _ _ _).symm
    _ ≤ 3 / 2 * (2 * ε ^ 2)⁻¹ := by
      gcongr
      push_cast at h_sum ⊢
      linarith
    _ = 3 / (4 * ε ^ 2) := by
      field_simp
      ring

/-- **Overestimation of an arm by the KL-UCB index** ([LS, Lemma 10.8] for rewards in `[0, 1]`).
In a run of any algorithm against the stochastic bandit `stationaryEnv ν`, if the rewards of arm
`a` lie in `[0, 1]` almost surely and have mean `μ_a`, then for `ε > 0`, `c < 1` with
`μ_a + ε < c`, and `L ≥ 0`, the expected number of rounds `t < n` at which `a` is played while it
has not been pulled yet, or `c ≤ μ̂_a`, or `c ≤ 1` and `d(μ̂_a, c) ≤ L / T_a`, is at most
`1 + L / d(μ_a + ε, c) + 1 / (2 ε²)`, uniformly in `n`. This bounds the contribution of a
suboptimal arm in the proof of [LS, Theorem 10.6]. -/
theorem sum_measureReal_action_eq_and_pullCount_eq_zero_or_le_empMean_or_klBer_le_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α) (hν : ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1)
    (hε : 0 < ε) (hc : (ν a)[id] + ε < c) (hc1 : c < 1) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
        c ≤ 1 ∧ klBer (empMean A R a t ω) c ≤ ENNReal.ofReal (L / pullCount A a t ω))} ≤
      1 + L / klBerReal ((ν a)[id] + ε) c + 1 / (2 * ε ^ 2) := by
  set p : ℕ → ℝ → Prop := fun s x ↦ s = 0 ∨ c ≤ x / s ∨
    c ≤ 1 ∧ klBer (x / s) c ≤ ENNReal.ofReal (L / s) with hp_def
  have hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2 :=
    (measurableSet_setOfPred.mp ((measurableSet_singleton 0).preimage measurable_fst)).or
      ((measurableSet_setOfPred.mp (measurableSet_le measurable_const (by fun_prop))).or
        (measurable_const.and
          (measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) (by fun_prop)))))
  -- the events are transferred to the reward stream, where the bound for i.i.d. rewards applies
  calc ∑ t ∈ range n, P.real {ω | A t ω = a ∧ (pullCount A a t ω = 0 ∨ c ≤ empMean A R a t ω ∨
      c ≤ 1 ∧ klBer (empMean A R a t ω) c ≤ ENNReal.ofReal (L / pullCount A a t ω))}
  _ = ∑ t ∈ range n, P.real
      {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} := by
    simp only [hp_def, empMean]
  _ ≤ ∑ s ∈ range n, (streamMeasure ν).real {ω | p s (∑ i ∈ range s, ω i a)} :=
    sum_measureReal_action_eq_and_pullCount_sumRewards_le h a n hp
  _ ≤ ∑ s ∈ range n, (streamMeasure ν).real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, ω i a) / s ∨
      klBer ((∑ i ∈ range s, ω i a) / s) c ≤ ENNReal.ofReal (L / s)} := by
    refine sum_le_sum fun s _ ↦ measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
    simp only [hp_def, Set.mem_ofPred_eq] at hω ⊢
    tauto
  _ ≤ 1 + L / klBerReal ((ν a)[id] + ε) c + 1 / (2 * ε ^ 2) :=
    sum_measureReal_eq_zero_or_le_div_or_klBer_div_le_le (iIndepFun_eval_streamMeasure'' ν a)
      (fun i ↦ (by fun_prop : Measurable fun ω : ℕ → α → ℝ ↦ ω i a).aemeasurable)
      (ae_mem_Icc_streamMeasure hν)
      (fun i ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).integral_eq.le)
      hε hc hc1 hL n

end BoundedRuns


end LMLExplore.Bandits
