/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Concentration
public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LMLExplore.Probability.Moments.ExponentialTail
public import LMLExplore.SequentialLearning.RateFunctionDeviation
public import LMLExplore.SequentialLearning.SumRewards

/-!
# Time-uniform deviations of the empirical means, for sub-Gaussian rewards

Let the rewards of each arm `a` of the stochastic environment `Environment.bandit ν` be
`σ²_a`-sub-Gaussian with mean `μ_a`. After `N_a` pulls with empirical mean `μ̂_a`, the
statistic `N_a (μ̂_a - μ_a)² / (2 σ²_a)` is the divergence `N_a d(μ̂_a, μ_a)` of Gaussian arms of
variance `σ²_a`, which the generalized likelihood ratio stopping rules of fixed-confidence
identification compare with a threshold. This file proves that, along a run of any algorithm,
the sum of these statistics over the `K` arms rarely exceeds `K log (2 t (t + 1)) + x` at any
round `t`: the probability of this event is at most `(x / K) ^ K exp (K - x)` for `x ≥ K`.

For one arm, in LML's i.i.d. reward stream model, Hoeffding's inequality (LML's
`Bandits.StreamMeasure.prob_sum_range_sub_ge_le_of_hasSubgaussianMGF` and
`Bandits.StreamMeasure.prob_sum_range_sub_le_le_of_hasSubgaussianMGF`) and a union bound over
the number `s` of rewards give
`P(∃ s, log (2 s (s + 1)) + y ≤ s (μ̂_s - μ)² / (2 σ²)) ≤ exp (-y)` [LS, Lemma 33.8]. The
rate function of a σ²-sub-Gaussian arm is at least `(x - μ)² / (2 σ²)`
(`ProbabilityTheory.HasSubgaussianMGF.ofReal_sq_div_le_rateFunction`), so the joint deviation
over all the arms, in the stream model and along the run, at all rounds simultaneously, follows
from the bounds for the rate functions of `SequentialLearning/RateFunctionDeviation.lean`
([LS, Proposition 33.9]). This is the deviation inequality of the proof of [LS, Lemma 33.7];
Lattimore and Szepesvári state it for Gaussian arms with unit variance and `log (t (t + 1))` in
place of `log (2 t (t + 1))`, which accounts for the two tails of a sub-Gaussian variable.

For a single arm and confidence intervals `μ̂_a ∓ β(N_a, n)` whose width depends on the number of
pulls `N_a` and on the round `n`, as in the stopping rule of LUCB [KTAS12], a union bound over the
rounds and the numbers of pulls, with Hoeffding's inequality for each number of pulls, bounds the
probability that the arm leaves its interval on one side at some round.

## Main definitions

* `LMLExplore.subgaussianRate σ2 y`: the time-uniform exploration rate
  `√(2 σ² (log (2 u (u + 1)) + y) / u)` after `u` pulls of a σ²-sub-Gaussian arm.

## Main statements

* `LMLExplore.subgaussianRate_lt`: the exploration rate is less than `ε` after
  `u ≥ 4 σ² ε⁻² (y + 2 log (16 σ² ε⁻²))` pulls.
* `LMLExplore.streamMeasure_le_sq_div_le`: for a σ²-sub-Gaussian arm and `s ≠ 0` rewards in the
  stream model, `P(z ≤ s (μ̂_s - μ)² / (2 σ²)) ≤ 2 exp (-z)`.
* `LMLExplore.streamMeasure_exists_log_add_le_sq_div_le`: [LS, Lemma 33.8] for a σ²-sub-Gaussian
  arm, in the stream model.
* `LMLExplore.streamMeasure_exists_card_mul_log_add_le_sum_sq_div_le`: the joint deviation over
  all the arms and all the vectors of numbers of rewards, in the stream model.
* `LMLExplore.measure_exists_card_mul_log_add_le_sum_pullCount_mul_sq_div_le`: along a run of any
  algorithm, `P(∃ t, K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) (μ̂_a(t) - μ_a)² / (2 σ²_a))` is at most
  `(x / K) ^ K exp (K - x)` for `x ≥ K`.
* `LMLExplore.measureReal_exists_pullCount_sumRewards_le_tsum`: a union bound over the rounds and
  the numbers of pulls of one arm, along a run of any algorithm.
* `LMLExplore.measureReal_exists_empMean_add_lt_le_tsum`,
  `LMLExplore.measureReal_exists_lt_empMean_sub_le_tsum`: along a run of any algorithm, the
  probability that a σ²-sub-Gaussian arm leaves the confidence interval `μ̂_a ∓ β(N_a, n)` on one
  side at some round `n` is at most `∑_n ∑_{u = 1}^n exp (-u β(u, n)² / (2 σ²))`, for any
  exploration rate `β ≥ 0` depending on the number of pulls `N_a` and the round `n`. These are the
  deviation bounds of the stopping rule of LUCB [KTAS12, Theorem 1].
* `LMLExplore.measureReal_exists_subgaussianRate_lt_abs_empMean_sub_le`: [LS, Lemma 33.8] along a
  run of any algorithm: a σ²-sub-Gaussian arm leaves the confidence interval
  `μ̂_a ∓ √(2 σ² (log (2 N_a (N_a + 1)) + y) / N_a)` (`subgaussianRate`) at some round with
  probability at most `exp (-y)`.
* `LMLExplore.measureReal_exists_exists_subgaussianRate_lt_abs_empMean_sub_le`: the same for all
  the `K` arms at once, with `y = log (K / δ)` and probability at most `δ`.

## References

* [KTAS12] S. Kalyanakrishnan, A. Tewari, P. Auer and P. Stone, *PAC subset selection in
  stochastic multi-armed bandits*, ICML 2012, Theorem 1.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemmas 33.7 and 33.8 and Proposition 33.9.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

open scoped ENNReal NNReal

namespace LMLExplore

variable {α : Type*} [MeasurableSpace α]

variable {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- The rewards of a σ²-sub-Gaussian arm are integrable. -/
private lemma _root_.ProbabilityTheory.HasSubgaussianMGF.integrable_id {a : α} {σ2 : ℝ≥0}
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) : Integrable id (ν a) :=
  (hν.integrable.add (integrable_const ((ν a)[id]))).congr
    (ae_of_all _ fun x ↦ by simp only [Pi.add_apply, sub_add_cancel, id])

/-- For a σ²-sub-Gaussian arm `a` with rate function `I_a`, the sub-Gaussian statistic
`N (m - μ_a)² / (2 σ²)` is at most the rate-function statistic `N I_a(m)`. -/
private lemma _root_.ProbabilityTheory.HasSubgaussianMGF.ofReal_mul_sq_div_le_mul_rateFunction
    {a : α} {σ2 : ℝ≥0} (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (N : ℕ)
    (m : ℝ) :
    ENNReal.ofReal (N * (m - (ν a)[id]) ^ 2 / (2 * σ2)) ≤ N * rateFunction id (ν a) m := by
  rw [mul_div_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  gcongr
  exact hν.ofReal_sq_div_le_rateFunction (X := id) m

/-- **Two-sided Hoeffding bound for the statistic of a sub-Gaussian arm.** In the reward stream
model, if the arm `a` is σ²-sub-Gaussian with mean `μ_a`, then for `s ≠ 0` rewards and `z ≥ 0`,
the probability that `z ≤ (∑ i < s, (X_i - μ_a))² / (2 σ² s)`, that is
`z ≤ s (μ̂_s - μ_a)² / (2 σ²)`, is at most `2 exp (-z)`. -/
theorem streamMeasure_le_sq_div_le {a : α} {σ2 : ℝ≥0}
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {s : ℕ} (hs : s ≠ 0) {z : ℝ}
    (hz : 0 ≤ z) :
    streamMeasure ν {ω | z ≤ (∑ i ∈ range s, (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 * s)} ≤
      ENNReal.ofReal (2 * exp (-z)) := by
  rcases hz.eq_or_lt with rfl | hz
  · simpa using prob_le_one.trans (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs' : (0 : ℝ) < s := Nat.cast_pos.2 (Nat.pos_of_ne_zero hs)
  set T : (ℕ → α → ℝ) → ℝ := fun ω ↦ ∑ i ∈ range s, (ω i a - (ν a)[id])
  rcases eq_or_ne σ2 0 with rfl | hσ2
  · -- for `σ² = 0`, the statistic `T² / 0` vanishes
    simp [hz.not_ge]
  -- the event is `|T| ≥ ε` for `ε = √(2 σ² s z)`, and each tail has probability `exp (-z)`
  set ε := √(2 * σ2 * s * z)
  have hε2 : -ε ^ 2 / (2 * s * σ2) = -z := by
    rw [sq_sqrt (by positivity)]
    field_simp
  have h_sub : {ω | z ≤ T ω ^ 2 / (2 * σ2 * s)} ⊆ {ω | ε ≤ T ω} ∪ {ω | T ω ≤ -ε} := by
    intro ω (hω : z ≤ _)
    rw [le_div_iff₀ (by positivity), mul_comm] at hω
    have h_abs : ε ≤ |T ω| := by
      rw [← sqrt_sq_eq_abs]
      exact sqrt_le_sqrt hω
    exact (le_abs'.1 h_abs).symm
  calc streamMeasure ν {ω | z ≤ T ω ^ 2 / (2 * σ2 * s)}
  _ ≤ streamMeasure ν {ω | ε ≤ T ω} + streamMeasure ν {ω | T ω ≤ -ε} :=
    (measure_mono h_sub).trans (measure_union_le _ _)
  _ ≤ ENNReal.ofReal (exp (-z)) + ENNReal.ofReal (exp (-z)) := by
    rw [← hε2]
    exact add_le_add
      (StreamMeasure.prob_sum_range_sub_ge_le_of_hasSubgaussianMGF hν (sqrt_nonneg _) s)
      (StreamMeasure.prob_sum_range_sub_le_le_of_hasSubgaussianMGF hν (sqrt_nonneg _) s)
  _ = ENNReal.ofReal (2 * exp (-z)) := by
    rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le, two_mul]

/-- **Time-uniform deviations of the empirical mean of a sub-Gaussian arm** [LS, Lemma 33.8]. In
the reward stream model, if the arm `a` is σ²-sub-Gaussian with mean `μ_a`, then for `y ≥ 0`, the
probability that `log (2 s (s + 1)) + y ≤ (∑ i < s, (X_i - μ_a))² / (2 σ² s)`, that is
`log (2 s (s + 1)) + y ≤ s (μ̂_s - μ_a)² / (2 σ²)`, for some number `s` of rewards is at most
`exp (-y)`. -/
theorem streamMeasure_exists_log_add_le_sq_div_le {a : α} {σ2 : ℝ≥0}
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {y : ℝ} (hy : 0 ≤ y) :
    streamMeasure ν {ω | ∃ s : ℕ, log (2 * s * (s + 1)) + y ≤
      (∑ i ∈ range s, (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 * s)} ≤ ENNReal.ofReal (exp (-y)) := by
  -- a union bound over the number of rewards, with no deviation for `0` rewards
  rw [Set.ofPred_exists]
  refine measure_iUnion_log_two_mul_mul_add_one_add_le (fun z hz ↦ ?_)
    (fun s z hs hz ↦ streamMeasure_le_sq_div_le hν hs hz) hy
  ext ω
  simp [hz.not_ge]

/-- **Joint time-uniform deviations of the empirical means of sub-Gaussian arms**, in the reward
stream model. If each arm `a` is `σ²_a`-sub-Gaussian with mean `μ_a`, then for `x ≥ K`, with `K`
the number of arms, the probability that
`K log (2 n (n + 1)) + x ≤ ∑ a, (∑ i < s a, (X_i a - μ_a))² / (2 σ²_a s a)` for some numbers of
rewards `s : α → ℕ`, with `n = ∑ a, s a`, is at most `(x / K) ^ K exp (K - x)`. -/
theorem streamMeasure_exists_card_mul_log_add_le_sum_sq_div_le [Fintype α] {σ2 : α → ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (σ2 a) (ν a)) {x : ℝ}
    (hx : Fintype.card α ≤ x) :
    streamMeasure ν {ω | ∃ s : α → ℕ,
      Fintype.card α * log (2 * ((∑ a, s a : ℕ) : ℝ) * (((∑ a, s a : ℕ) : ℝ) + 1)) + x ≤
        ∑ a, (∑ i ∈ range (s a), (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 a * s a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  -- the sub-Gaussian statistic of each arm is at most its rate-function statistic
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le
      (fun a ↦ (hν a).integrable_id) hx)
  obtain ⟨s, hs⟩ := hω
  refine ⟨s, ?_⟩
  refine (ENNReal.ofReal_le_ofReal hs).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ ↦ by positivity]
  refine sum_le_sum fun a _ ↦ ?_
  rcases eq_or_ne (s a) 0 with h0 | h0
  · simp [h0]
  have h_sum : (∑ i ∈ range (s a), (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 a * s a) =
      s a * ((∑ i ∈ range (s a), ω i a) / s a - (ν a)[id]) ^ 2 / (2 * σ2 a) := by
    have hs' : ((s a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 h0
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
  rw [h_sum]
  exact (hν a).ofReal_mul_sq_div_le_mul_rateFunction _ _

/-! ### Confidence bounds of one arm with an exploration rate -/

section ExplorationRate

variable [DecidableEq α] [Countable α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **Union bound over the rounds and the numbers of pulls.** In a run of any algorithm against
the stochastic bandit `Environment.bandit ν`, let `p n s x` be a property of a round `n`, a number
of pulls `s` and a sum of rewards `x` that fails for `s = 0`, and let `f n u` bound the probability
that `p n u` holds for the sum of the first `u` rewards of the arm `a` in the i.i.d. reward stream
model. Then the probability that `p n` holds at some round `n` for the number of pulls and the sum
of rewards of `a` is at most `∑_n ∑_{u = 1}^n f n u`. -/
theorem measureReal_exists_pullCount_sumRewards_le_tsum
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (p : ℕ → ℕ → ℝ → Prop)
    (hp0 : ∀ n x, ¬ p n 0 x) {f : ℕ → ℕ → ℝ}
    (hf : ∀ n u, (streamMeasure ν).real {ω | p n u (∑ i ∈ range u, ω i a)} ≤ f n u)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, f n u) :
    P.real {ω | ∃ n, p n (pullCount A a n ω) (sumRewards A R a n ω)} ≤
      ∑' n, ∑ u ∈ Icc 1 n, f n u := by
  have hg0 (n : ℕ) : 0 ≤ ∑ u ∈ Icc 1 n, f n u :=
    sum_nonneg fun u _ ↦ measureReal_nonneg.trans (hf n u)
  -- at round `n`, a union bound over the number `u ∈ [1, n]` of pulls of `a`
  have hn (n : ℕ) : P {ω | p n (pullCount A a n ω) (sumRewards A R a n ω)} ≤
      ENNReal.ofReal (∑ u ∈ Icc 1 n, f n u) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal
      ((measureReal_pullCount_sumRewards_le_sum h a (p n) (hp0 n) n).trans ?_)
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact sum_le_sum fun s _ ↦ add_comm s 1 ▸ hf n (s + 1)
  refine ENNReal.toReal_le_of_le_ofReal (tsum_nonneg hg0) ?_
  rw [ENNReal.ofReal_tsum_of_nonneg hg0 hsum, Set.ofPred_exists]
  exact (measure_iUnion_le _).trans (tsum_le_tsum hn)

/-- **Time-uniform underestimation of a sub-Gaussian arm, with an exploration rate.** In a run of
any algorithm against `Environment.bandit ν`, if the arm `a` is σ²-sub-Gaussian with mean `μ_a` and
the exploration rate `β ≥ 0` is a function of the number of pulls and the round, then the
probability that at some round `n`, the arm `a` has been pulled and its pull count `N_a(n)` and
empirical mean `μ̂_a(n)` satisfy `μ̂_a(n) + β(N_a(n), n) < μ_a` is at most
`∑_n ∑_{u = 1}^n exp (-u β(u, n)² / (2 σ²))`. -/
theorem measureReal_exists_empMean_add_lt_le_tsum
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) {σ2 : ℝ≥0}
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {β : ℕ → ℕ → ℝ}
    (hβ : ∀ u n, 0 ≤ β u n)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2)))) :
    P.real {ω | ∃ n, pullCount A a n ω ≠ 0 ∧
        empMean A R a n ω + β (pullCount A a n ω) n < (ν a)[id]} ≤
      ∑' n, ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))) := by
  refine le_trans ?_ (measureReal_exists_pullCount_sumRewards_le_tsum h a
    (fun n s x ↦ s ≠ 0 ∧ x / s + β s n < (ν a)[id]) (fun _ _ h0 ↦ h0.1 rfl) (fun n u ↦ ?_) hsum)
  · exact measureReal_mono fun ω ⟨n, hn⟩ ↦ ⟨n, by rwa [empMean] at hn⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : (0 : ℝ) < u := Nat.cast_pos.2 (Nat.pos_of_ne_zero hu)
  -- multiplied by `u`, the event says that the centered sum is less than `-u β(u, n)`
  refine le_trans (measureReal_mono fun ω hω ↦ ?_) (ENNReal.toReal_le_of_le_ofReal (exp_pos _).le
    ((Bandits.StreamMeasure.prob_sum_range_sub_le_le_of_hasSubgaussianMGF hν
      (mul_nonneg hu'.le (hβ u n)) u).trans_eq ?_))
  · obtain ⟨-, hω⟩ := hω
    rw [div_add' _ _ _ hu'.ne', div_lt_iff₀ hu'] at hω
    simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    linarith
  · congr 2
    field_simp

/-- **Time-uniform overestimation of a sub-Gaussian arm, with an exploration rate.** In a run of
any algorithm against `Environment.bandit ν`, if the arm `a` is σ²-sub-Gaussian with mean `μ_a` and
the exploration rate `β ≥ 0` is a function of the number of pulls and the round, then the
probability that at some round `n`, the arm `a` has been pulled and its pull count `N_a(n)` and
empirical mean `μ̂_a(n)` satisfy `μ_a < μ̂_a(n) - β(N_a(n), n)` is at most
`∑_n ∑_{u = 1}^n exp (-u β(u, n)² / (2 σ²))`. -/
theorem measureReal_exists_lt_empMean_sub_le_tsum
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) {σ2 : ℝ≥0}
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {β : ℕ → ℕ → ℝ}
    (hβ : ∀ u n, 0 ≤ β u n)
    (hsum : Summable fun n ↦ ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2)))) :
    P.real {ω | ∃ n, pullCount A a n ω ≠ 0 ∧
        (ν a)[id] < empMean A R a n ω - β (pullCount A a n ω) n} ≤
      ∑' n, ∑ u ∈ Icc 1 n, exp (-(u * β u n ^ 2 / (2 * σ2))) := by
  refine le_trans ?_ (measureReal_exists_pullCount_sumRewards_le_tsum h a
    (fun n s x ↦ s ≠ 0 ∧ (ν a)[id] < x / s - β s n) (fun _ _ h0 ↦ h0.1 rfl) (fun n u ↦ ?_) hsum)
  · exact measureReal_mono fun ω ⟨n, hn⟩ ↦ ⟨n, by rwa [empMean] at hn⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hu' : (0 : ℝ) < u := Nat.cast_pos.2 (Nat.pos_of_ne_zero hu)
  -- multiplied by `u`, the event says that the centered sum is more than `u β(u, n)`
  refine le_trans (measureReal_mono fun ω hω ↦ ?_) (ENNReal.toReal_le_of_le_ofReal (exp_pos _).le
    ((Bandits.StreamMeasure.prob_sum_range_sub_ge_le_of_hasSubgaussianMGF hν
      (mul_nonneg hu'.le (hβ u n)) u).trans_eq ?_))
  · obtain ⟨-, hω⟩ := hω
    rw [div_sub' hu'.ne', lt_div_iff₀ hu'] at hω
    simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    linarith
  · congr 2
    field_simp

/-- The time-uniform exploration rate `√(2 σ² (log (2 u (u + 1)) + y) / u)` after `u` pulls of a
σ²-sub-Gaussian arm [LS, Lemma 33.8]: the empirical mean of the arm stays within this rate of its
mean at all rounds with probability at least `1 - exp (-y)`
(`measureReal_exists_subgaussianRate_lt_abs_empMean_sub_le`). -/
noncomputable def subgaussianRate (σ2 : ℝ≥0) (y : ℝ) (u : ℕ) : ℝ :=
  √(2 * σ2 * (log (2 * u * (u + 1)) + y) / u)

lemma subgaussianRate_def (σ2 : ℝ≥0) (y : ℝ) (u : ℕ) :
    subgaussianRate σ2 y u = √(2 * σ2 * (log (2 * u * (u + 1)) + y) / u) := (rfl)

lemma subgaussianRate_nonneg (σ2 : ℝ≥0) (y : ℝ) (u : ℕ) : 0 ≤ subgaussianRate σ2 y u :=
  sqrt_nonneg _

open Filter Topology in
/-- The time-uniform exploration rate tends to `0` as the number of pulls tends to infinity. -/
lemma tendsto_subgaussianRate_atTop (σ2 : ℝ≥0) (y : ℝ) :
    Tendsto (subgaussianRate σ2 y) atTop (𝓝 0) := by
  have h_log : Tendsto (fun u : ℕ ↦ log (u : ℝ) / u) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      tendsto_natCast_atTop_atTop
  have h_log_succ : Tendsto (fun u : ℕ ↦ log ((u : ℝ) + 1) / u) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have h_sum := ((tendsto_const_div_atTop_nhds_zero_nat (log 2 + y)).add
    (h_log.add h_log_succ)).const_mul (2 * (σ2 : ℝ))
  rw [add_zero, add_zero, mul_zero] at h_sum
  have h_sqrt := (continuous_sqrt.tendsto 0).comp h_sum
  rw [sqrt_zero] at h_sqrt
  refine h_sqrt.congr' ((eventually_ne_atTop 0).mono fun u hu ↦ ?_)
  have hu' : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hu
  rw [Function.comp_apply, subgaussianRate_def, log_mul (by positivity) (by positivity),
    log_mul (by positivity) hu']
  congr 1
  field_simp
  ring

/-- **Number of pulls after which the exploration rate is below `ε`.** For `ε > 0`, the rate
`√(2 σ² (log (2 u (u + 1)) + y) / u)` is less than `ε` as soon as
`u ≥ 4 σ² ε⁻² (y + 2 log (16 σ² ε⁻²))`. -/
lemma subgaussianRate_lt {σ2 : ℝ≥0} {y ε : ℝ} {u : ℕ} (hε : 0 < ε)
    (hu : 4 * σ2 / ε ^ 2 * (y + 2 * log (16 * σ2 / ε ^ 2)) ≤ u) :
    subgaussianRate σ2 y u < ε := by
  rcases eq_or_ne u 0 with rfl | hu0
  · simpa [subgaussianRate_def] using hε
  rcases eq_or_ne σ2 0 with rfl | hσ0
  · simpa [subgaussianRate_def] using hε
  have hσ : (0 : ℝ) < σ2 := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ0)
  have hu1 : (1 : ℝ) ≤ u := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 hu0)
  have hε2 : 0 < ε ^ 2 := pow_pos hε 2
  -- `log (2 u (u + 1)) ≤ 2 log (2 u)`, as `u + 1 ≤ 2 u`.
  have hlog : log (2 * u * (u + 1)) ≤ 2 * log (2 * u) := by
    calc log (2 * u * (u + 1)) ≤ log ((2 * u) ^ 2) := log_le_log (by positivity) (by nlinarith)
      _ = 2 * log (2 * u) := by rw [log_pow, Nat.cast_ofNat]
  -- Inverting `x ↦ x - a log x` with `a = 8 σ² ε⁻²` at `x = 2 u`.
  have hkey := mul_log_add_lt (a := 8 * σ2 / ε ^ 2) (b := 4 * σ2 * y / ε ^ 2) (x := 2 * u)
    (by positivity) (by positivity) (by
      rw [show 2 * (8 * (σ2 : ℝ) / ε ^ 2) * log (2 * (8 * σ2 / ε ^ 2)) + 2 * (4 * σ2 * y / ε ^ 2)
        = 2 * (4 * σ2 / ε ^ 2 * (y + 2 * log (16 * σ2 / ε ^ 2))) by ring_nf]
      linarith)
  rw [show 8 * (σ2 : ℝ) / ε ^ 2 * log (2 * u) + 4 * σ2 * y / ε ^ 2 =
    (8 * σ2 * log (2 * u) + 4 * σ2 * y) / ε ^ 2 by ring, div_lt_iff₀ hε2] at hkey
  rw [subgaussianRate_def, sqrt_lt' hε, div_lt_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hlog hσ.le]

/-- **Time-uniform deviations of the empirical mean of a sub-Gaussian arm along a run**
([LS, Lemma 33.8] along a run). In a run of any algorithm against `Environment.bandit ν`, if the
arm `a` is σ²-sub-Gaussian with mean `μ_a` and `σ² ≠ 0`, then for `y ≥ 0`, the probability that at
some round `n` the arm `a` has been pulled and its pull count `N_a(n)` and empirical mean
`μ̂_a(n)` satisfy `√(2 σ² (log (2 N_a(n) (N_a(n) + 1)) + y) / N_a(n)) < |μ̂_a(n) - μ_a|`
(`subgaussianRate`) is at most `exp (-y)`. -/
theorem measureReal_exists_subgaussianRate_lt_abs_empMean_sub_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hν : HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {y : ℝ} (hy : 0 ≤ y) :
    P.real {ω | ∃ n, pullCount A a n ω ≠ 0 ∧
        subgaussianRate σ2 y (pullCount A a n ω) < |empMean A R a n ω - (ν a)[id]|} ≤
      exp (-y) := by
  simp only [subgaussianRate_def]
  have hσ : (0 : ℝ) < σ2 := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hσ2)
  -- the event of the stream model at `s ≠ 0` rewards with sum `x`
  set p : ℕ → ℝ → Prop := fun s x ↦ s ≠ 0 ∧
    √(2 * σ2 * (log (2 * s * (s + 1)) + y) / s) < |x / s - (ν a)[id]|
  have h_stream : streamMeasure ν {ω | ∃ s, p s (∑ i ∈ range s, ω i a)} ≤
      streamMeasure ν {ω | ∃ s : ℕ, log (2 * s * (s + 1)) + y ≤
        (∑ i ∈ range s, (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 * s)} := by
    refine measure_mono fun ω ⟨s, hs0, hs⟩ ↦ ⟨s, ?_⟩
    -- the deviation `D = μ̂_s - μ_a` satisfies `2 σ² (log (2 s (s + 1)) + y) < s D²`
    have hs' : (0 : ℝ) < s := Nat.cast_pos.2 (Nat.pos_of_ne_zero hs0)
    set x := ∑ i ∈ range s, ω i a
    rw [sqrt_lt' ((sqrt_nonneg _).trans_lt hs), sq_abs, div_lt_iff₀ hs'] at hs
    have h_sum : ∑ i ∈ range s, (ω i a - (ν a)[id]) = (x / s - (ν a)[id]) * s := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sub_mul,
        div_mul_cancel₀ _ hs'.ne', mul_comm]
    rw [h_sum, le_div_iff₀ (by positivity)]
    nlinarith
  refine ENNReal.toReal_le_of_le_ofReal (exp_pos _).le ?_
  calc P {ω | ∃ n, pullCount A a n ω ≠ 0 ∧
        √(2 * σ2 * (log (2 * pullCount A a n ω * (pullCount A a n ω + 1)) + y) /
          pullCount A a n ω) < |empMean A R a n ω - (ν a)[id]|}
  _ ≤ P {ω | ∃ n, p (pullCount A a n ω) (sumRewards A R a n ω)} :=
    measure_mono fun ω ⟨n, hn⟩ ↦ ⟨n, by rwa [empMean] at hn⟩
  _ ≤ streamMeasure ν {ω | ∃ s, p s (∑ i ∈ range s, ω i a)} :=
    measure_exists_pullCount_sumRewards_le h a p
  _ ≤ ENNReal.ofReal (exp (-y)) := h_stream.trans (streamMeasure_exists_log_add_le_sq_div_le hν hy)

end ExplorationRate

/-! ### Runs of an algorithm -/

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **Time-uniform deviations of the empirical means of sub-Gaussian arms along a run** (the
deviation inequality of [LS, Lemma 33.7]). In a run of any algorithm against `Environment.bandit ν`,
if each arm `a` is `σ²_a`-sub-Gaussian with mean `μ_a`, then for `x ≥ K`, with `K` the number of
arms, the probability that at some round `t`, the pull counts `N_a(t)` and the empirical means
`μ̂_a(t)` satisfy `K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) (μ̂_a(t) - μ_a)² / (2 σ²_a)`, is at most
`(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_card_mul_log_add_le_sum_pullCount_mul_sq_div_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {σ2 : α → ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (σ2 a) (ν a)) {x : ℝ}
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ t : ℕ, Fintype.card α * log (2 * t * (t + 1)) + x ≤
        ∑ a, pullCount A a t ω * (empMean A R a t ω - (ν a)[id]) ^ 2 / (2 * σ2 a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  -- the sub-Gaussian statistic of each arm is at most its rate-function statistic
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le h
      (fun a ↦ (hν a).integrable_id) hx)
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  refine (ENNReal.ofReal_le_ofReal ht).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ ↦ by positivity]
  exact sum_le_sum fun a _ ↦ (hν a).ofReal_mul_sq_div_le_mul_rateFunction _ _

/-- **Time-uniform deviations of the empirical means of all the sub-Gaussian arms along a run**
([LS, Lemma 33.8] and a union bound over the arms). In a run of any algorithm against
`Environment.bandit ν` with σ²-sub-Gaussian arms, `σ² ≠ 0` and `0 < δ ≤ K`, with `K` the number of
arms, the probability that at some round `n`, the empirical mean of some pulled arm `b` is not
within `subgaussianRate σ2 (log (K / δ)) (N_b(n))` of the mean of `b` is at most `δ`. -/
theorem measureReal_exists_exists_subgaussianRate_lt_abs_empMean_sub_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {σ2 : ℝ≥0} (hσ2 : σ2 ≠ 0)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) {δ : ℝ} (hδ : 0 < δ)
    (hδK : δ ≤ Fintype.card α) :
    P.real {ω | ∃ n b, pullCount A b n ω ≠ 0 ∧
      subgaussianRate σ2 (log (Fintype.card α / δ)) (pullCount A b n ω) <
        |empMean A R b n ω - (ν b)[id]|} ≤ δ := by
  have hy : 0 ≤ log (Fintype.card α / δ) := log_nonneg ((one_le_div hδ).2 hδK)
  calc P.real {ω | ∃ n b, pullCount A b n ω ≠ 0 ∧
      subgaussianRate σ2 (log (Fintype.card α / δ)) (pullCount A b n ω) <
        |empMean A R b n ω - (ν b)[id]|}
  _ ≤ P.real (⋃ b ∈ (univ : Finset α), {ω | ∃ n, pullCount A b n ω ≠ 0 ∧
      subgaussianRate σ2 (log (Fintype.card α / δ)) (pullCount A b n ω) <
        |empMean A R b n ω - (ν b)[id]|}) :=
    measureReal_mono (fun ω ⟨n, b, hb⟩ ↦ Set.mem_biUnion (mem_univ b) ⟨n, hb⟩)
      (measure_ne_top _ _)
  _ ≤ ∑ b, P.real {ω | ∃ n, pullCount A b n ω ≠ 0 ∧
      subgaussianRate σ2 (log (Fintype.card α / δ)) (pullCount A b n ω) <
        |empMean A R b n ω - (ν b)[id]|} :=
    measureReal_biUnion_finset_le _ _
  _ ≤ ∑ _b : α, exp (-log (Fintype.card α / δ)) :=
    sum_le_sum fun b _ ↦ measureReal_exists_subgaussianRate_lt_abs_empMean_sub_le h b hσ2 (hν b) hy
  _ = δ := by
    have hK : (0 : ℝ) < Fintype.card α := hδ.trans_le hδK
    rw [sum_const, card_univ, nsmul_eq_mul, exp_neg, exp_log (by positivity)]
    field_simp

end LMLExplore
