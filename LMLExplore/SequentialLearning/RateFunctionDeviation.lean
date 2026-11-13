/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LMLExplore.Probability.LargeDeviations.Chernoff
public import LMLExplore.Probability.Martingale.RateFunction
public import LMLExplore.Probability.Moments.ExponentialTail
public import LMLExplore.SequentialLearning.SumRewards

/-!
# Time-uniform deviations of the empirical means, measured by the rate function

Let the rewards of each arm `a` of the stochastic environment `Environment.bandit ν` be integrable,
with Cramér rate function `I_a = rateFunction id (ν a)`. After `N_a` pulls with empirical mean
`μ̂_a`, the statistic `N_a I_a(μ̂_a)` measures how far `μ̂_a` lies from the mean of `a`. This file
proves that, along a run of any algorithm, the sum of these statistics over a set `S` of `k` arms
rarely exceeds `k log (2 t (t + 1)) + x` at any round `t`: the probability of this event is at
most `(x / k) ^ k exp (k - x)` for `x ≥ k`. For all the `K` arms, `k = K`; for pairs of arms, as in
the pairwise stopping rules of best arm identification, the threshold is `2 log (2 t (t + 1)) + x`
whatever the number of arms.

For one arm, in LML's i.i.d. reward stream model, the two-sided Cramér–Chernoff bound
`P(z ≤ s I_a(μ̂_s)) ≤ 2 exp (-z)`
(`ProbabilityTheory.iIndepFun.measureReal_le_card_mul_rateFunction_le_two_mul_exp`) and a union
bound over the number `s` of rewards (`LMLExplore.measure_iUnion_log_two_mul_mul_add_one_add_le`)
give `P(∃ s, log (2 s (s + 1)) + y ≤ s I_a(μ̂_s)) ≤ exp (-y)` [LS, Lemma 33.8]. The arms are
independent in the stream model, so [LS, Proposition 33.9]
(`LMLExplore.measure_exists_card_mul_add_le_sum_le`) bounds the joint deviation over all the
vectors of numbers of rewards, and the joint transfer of `SequentialLearning/SumRewards.lean` turns
it into a bound along the run, at all rounds simultaneously. The statistics are `ℝ≥0∞`-valued:
`I_a(μ̂_s)` is infinite for instance at empirical means beyond the essential supremum of the
rewards, and by the same Chernoff bound this happens with probability zero.

The term `#S log (2 t (t + 1))` grows like `2 #S log t`. Peeling the number of rewards of each arm
over the dyadic slices `2 ^ k ≤ s < 2 ^ (k + 1)`, as in [GC11, Theorem 10], instead of a union
bound over each number, makes it grow like `η log₂ t` per arm, for any `η > 0`, at the price of a
factor `2`. On the slice `k`, the deviation `z ≤ s I_a(μ̂_s)` has probability at most
`2 exp (-z / 2)`
(`ProbabilityTheory.iIndepFun.measure_exists_le_and_lt_and_le_mul_rateFunction_le`), and with the
level `z = 2 (η k + κ_η + y)`, where `κ_η = log (2 / (1 - exp (-η)))`, these probabilities sum
to `exp (-y)`. The same joint bound and transfer to runs give
`P(∃ t, 2 (#S (η log₂ t + κ_η) + x) ≤ ∑ a ∈ S, N_a(t) I_a(μ̂_a(t))) ≤ (x / #S) ^ #S exp (#S - x)`
for `x ≥ #S`, with the integer logarithm `log₂ t = Nat.log 2 t`. This is the deviation inequality
behind the thresholds `log (C t ^ p / δ)` of [GK16, Proposition 12], for every exponent `p > 0`.
The peeled bounds are adapted from the formalization in the Garivier2016Optimal project
(Rémy Degenne, <https://github.com/RemyDegenne/Garivier2016Optimal>, file
`Garivier2016Optimal/ForLMLExplore/SequentialLearning/RateFunctionDeviation.lean`).

For rewards dominated by exponential families, the rate function of each arm is at least the
extended divergence of its family, and `SequentialLearning/ExpFamilyDeviation.lean` deduces the
same bound for the generalized likelihood ratio statistic of the empirical means. For
σ²-sub-Gaussian rewards, the rate function is at least `(x - μ_a)² / (2 σ²)`, with equality for
Gaussian rewards of variance `σ²`, and `SequentialLearning/SubGaussianDeviation.lean` deduces the
same bounds for that statistic.

## Main statements

* `LMLExplore.streamMeasure_le_mul_rateFunction_le`: for an integrable arm and `s` rewards in the
  stream model, `P(z ≤ s I_a(μ̂_s)) ≤ 2 exp (-z)`.
* `LMLExplore.streamMeasure_exists_log_add_le_mul_rateFunction_le`: [LS, Lemma 33.8] for the rate
  function, in the stream model.
* `LMLExplore.streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le`: the joint
  deviation over the arms of a set `S` and all the vectors of numbers of rewards, in the stream
  model.
* `LMLExplore.measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le`: along a run of
  any algorithm, `P(∃ t, #S log (2 t (t + 1)) + x ≤ ∑ a ∈ S, N_a(t) I_a(μ̂_a(t)))` is at most
  `(x / #S) ^ #S exp (#S - x)` for `x ≥ #S`; the `_univ` forms state the case of all the arms.
* `LMLExplore.streamMeasure_exists_two_mul_add_le_mul_rateFunction_le`: the peeled bound
  `P(∃ s, 2 (η log₂ s + κ_η + y) ≤ s I_a(μ̂_s)) ≤ exp (-y)` for one arm, in the stream model.
* `LMLExplore.streamMeasure_exists_two_mul_card_mul_add_le_sum_mul_rateFunction_le`: the peeled
  joint deviation over the arms of a set `S` and all the vectors of numbers of rewards, in the
  stream model.
* `LMLExplore.measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le`: along a
  run of any algorithm,
  `P(∃ t, 2 (#S (η log₂ t + κ_η) + x) ≤ ∑ a ∈ S, N_a(t) I_a(μ̂_a(t))) ≤ (x / #S) ^ #S exp (#S - x)`
  for `x ≥ #S`.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10, for the peeling.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemmas 33.7 and 33.8 and Proposition 33.9.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits Filter

open scoped ENNReal Topology

namespace LMLExplore

variable {α : Type*} [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-! ### The reward stream model -/

/-- **Two-sided Cramér–Chernoff bound for one arm in the stream model.** If the rewards of the arm
`a` are integrable, then for `s` rewards with empirical mean `μ̂_s = (∑ i < s, X_i) / s` and every
real `z`, the probability that `z ≤ s I_a(μ̂_s)` is at most `2 exp (-z)`, where `I_a` is the rate
function of the law `ν a` of the rewards. -/
theorem streamMeasure_le_mul_rateFunction_le {a : α} (hν : Integrable id (ν a)) (s : ℕ) (z : ℝ) :
    streamMeasure ν {ω | ENNReal.ofReal z ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ≤
      ENNReal.ofReal (2 * exp (-z)) := by
  have h := (iIndepFun_eval_streamMeasure'' ν a).measureReal_le_card_mul_rateFunction_le_two_mul_exp
    (s := range s) (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedOn) hν z
  rw [card_range] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- **Time-uniform deviations of the empirical mean of one arm, measured by the rate function**
[LS, Lemma 33.8]. In the reward stream model, if the rewards of the arm `a` are integrable, then
for `y ≥ 0`, the probability that `log (2 s (s + 1)) + y ≤ s I_a(μ̂_s)` for some number `s` of
rewards is at most `exp (-y)`. -/
theorem streamMeasure_exists_log_add_le_mul_rateFunction_le {a : α} (hν : Integrable id (ν a))
    {y : ℝ} (hy : 0 ≤ y) :
    streamMeasure ν {ω | ∃ s : ℕ, ENNReal.ofReal (log (2 * s * (s + 1)) + y) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ≤ ENNReal.ofReal (exp (-y)) := by
  -- a union bound over the number of rewards, with no deviation for `0` rewards
  rw [Set.ofPred_exists]
  refine measure_iUnion_log_two_mul_mul_add_one_add_le (fun z hz ↦ ?_)
    (fun s z _ _ ↦ streamMeasure_le_mul_rateFunction_le hν s z) hy
  ext ω
  simp [hz]

/-- **Peeled time-uniform deviations of the empirical mean of one arm, measured by the rate
function.** In the reward stream model, if the rewards of the arm `a` are integrable, with rate
function `I_a`, then for `η > 0` and `y ≥ 0`, the probability that
`2 (η log₂ s + log (2 / (1 - exp (-η))) + y) ≤ s I_a(μ̂_s)` for some number `s` of rewards, with
`log₂ s = Nat.log 2 s`, is at most `exp (-y)`. -/
theorem streamMeasure_exists_two_mul_add_le_mul_rateFunction_le [Countable α] {a : α}
    (hν : Integrable id (ν a)) {η : ℝ} (hη : 0 < η) {y : ℝ} (hy : 0 ≤ y) :
    streamMeasure ν {ω | ∃ s : ℕ, ENNReal.ofReal (2 * (η * Nat.log 2 s +
        log (2 / (1 - exp (-η))) + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ≤ ENNReal.ofReal (exp (-y)) := by
  set κ := log (2 / (1 - exp (-η))) with hκ
  have he : exp (-η) < 1 := (exp_lt_exp.2 (neg_lt_zero.2 hη)).trans_eq exp_zero
  have he1 : 0 < 1 - exp (-η) := by linarith
  have hκ0 : 0 < κ := log_pos (by rw [lt_div_iff₀ he1]; linarith [exp_pos (-η)])
  -- the dyadic slice of the numbers of rewards `2 ^ k ≤ s < 2 ^ (k + 1)`
  let E : ℕ → Set (ℕ → α → ℝ) := fun k ↦ {ω | ∃ s : ℕ, (2 : ℝ) ^ k ≤ s ∧ (s : ℝ) < 2 ^ k * 2 ∧
    ENNReal.ofReal (2 * (η * k + κ + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)}
  have hE (k : ℕ) : streamMeasure ν (E k) ≤ ENNReal.ofReal (2 * exp (-(η * k + κ + y))) := by
    have h_indep := iIndepFun_eval_streamMeasure'' ν a
    have h := h_indep.measure_exists_le_and_lt_and_le_mul_rateFunction_le (Y := id) (Q := ν a)
      (fun i ↦ by fun_prop) (fun i ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedOn)
      hν (a := 2 ^ k) (b := 2 ^ k * 2) (z := 2 * (η * k + κ + y)) (by positivity) (by positivity)
    refine h.trans_eq ?_
    congr 3
    field_simp
  -- a deviation with `s` rewards is a deviation on the slice of `s`
  have h_sub : {ω : ℕ → α → ℝ | ∃ s : ℕ, ENNReal.ofReal (2 * (η * Nat.log 2 s + κ + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ⊆ ⋃ k, E k := by
    rintro ω ⟨s, hs⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp only [Nat.log_zero_right, CharP.cast_eq_zero, mul_zero, zero_add, zero_mul,
        nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hs
      linarith
    refine Set.mem_iUnion.2 ⟨Nat.log 2 s, s, ?_, ?_, hs⟩
    · exact_mod_cast Nat.pow_log_le_self 2 hs0
    · have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) s
      rw [Nat.pow_succ] at h
      exact_mod_cast h
  -- the bounds of the slices sum to `exp (-y)`
  have h_sum : HasSum (fun k : ℕ ↦ 2 * exp (-(η * k + κ + y))) (exp (-y)) := by
    have h := (hasSum_exp_neg_add_mul hη 0).mul_left (2 * exp (-(κ + y)))
    convert h using 1
    · ext k
      rw [mul_assoc, ← exp_add]
      push_cast
      ring_nf
    · rw [hκ, neg_add, exp_add, exp_neg (log _), exp_log (by positivity)]
      simp only [CharP.cast_eq_zero, zero_mul, neg_zero, exp_zero]
      field_simp
  calc _ ≤ streamMeasure ν (⋃ k, E k) := measure_mono h_sub
  _ ≤ ∑' k, streamMeasure ν (E k) := measure_iUnion_le _
  _ ≤ ∑' k : ℕ, ENNReal.ofReal (2 * exp (-(η * k + κ + y))) := tsum_le_tsum hE
  _ = ENNReal.ofReal (exp (-y)) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ by positivity) h_sum.summable, h_sum.tsum_eq]

/-- In the reward stream model, if the rewards of the arm `a` are integrable, then almost surely
the statistic `s I_a(μ̂_s)` of the first `s` rewards is finite for every `s`. -/
private lemma streamMeasure_exists_mul_rateFunction_eq_top {a : α} (hν : Integrable id (ν a)) :
    streamMeasure ν {ω | ∃ s : ℕ,
      (s : ℝ≥0∞) * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s) = ∞} = 0 := by
  rw [Set.ofPred_exists]
  refine measure_iUnion_null fun s ↦ nonpos_iff_eq_zero.1 ?_
  have h_tendsto : Tendsto (fun z : ℝ ↦ ENNReal.ofReal (2 * exp (-z))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_exp_neg_atTop_nhds_zero.const_mul 2)
  refine ge_of_tendsto' h_tendsto fun z ↦ (measure_mono fun ω hω ↦ ?_).trans
    (streamMeasure_le_mul_rateFunction_le hν s z)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hω]
  exact le_top

/-- **Joint time-uniform deviations of the empirical means above a monotone threshold**, in the
reward stream model, for the arms of a finite set `S`. Let the rewards of each arm `a ∈ S` be
integrable, with rate function `I_a`, let `g` be monotone and `c > 0`, and suppose that for each
arm `a ∈ S` and `y ≥ 0`, the probability that `c (g s + y) ≤ s I_a(μ̂_s)` for some number `s` of
rewards is at most `exp (-y)`. Then for `x ≥ #S`, the probability that
`c (#S g n + x) ≤ ∑ a ∈ S, s a I_a((∑ i < s a, X_i a) / s a)` for some numbers of rewards
`s : α → ℕ`, with `n = ∑ a ∈ S, s a`, is at most `(x / #S) ^ #S exp (#S - x)`. -/
private lemma streamMeasure_exists_mul_card_mul_add_le_sum_mul_rateFunction_le_of (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) {g : ℕ → ℝ} (hg : Monotone g) {c : ℝ} (hc : 0 < c)
    (h_one : ∀ a ∈ S, ∀ y, 0 ≤ y → streamMeasure ν {ω | ∃ s : ℕ, ENNReal.ofReal (c * (g s + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ≤ ENNReal.ofReal (exp (-y)))
    {x : ℝ} (hx : #S ≤ x) :
    streamMeasure ν {ω | ∃ s : α → ℕ, ENNReal.ofReal (c * (#S * g (∑ a ∈ S, s a) + x)) ≤
        ∑ a ∈ S, s a * rateFunction id (ν a) ((∑ i ∈ range (s a), ω i a) / s a)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) := by
  -- the statistic `s I_a(μ̂_s)` of the first `s` rewards `f` of the arm `a`
  set F : α → (ℕ → ℝ) → ℕ → ℝ≥0∞ :=
    fun a f s ↦ s * rateFunction id (ν a) ((∑ i ∈ range s, f i) / s) with hF
  have hFm (a : α) (s : ℕ) : Measurable fun f : ℕ → ℝ ↦ F a f s :=
    measurable_const.mul ((lowerSemicontinuous_rateFunction _ _).measurable.comp (by fun_prop))
  -- the real statistics of the arms of `S`, divided by `c`, are functions of their independent
  -- reward sequences
  have h_indep : iIndepFun
      (fun (a : S) (ω : ℕ → α → ℝ) (s : ℕ) ↦ (F a (fun i ↦ ω i a) s).toReal / c)
      (streamMeasure ν) :=
    ((iIndepFun_arm_streamMeasure ν).comp (fun a f s ↦ (F a f s).toReal / c)
      fun a ↦ Measurable.of_eval fun s ↦ (hFm a s).ennreal_toReal.div_const c).precomp
      Subtype.val_injective
  have hS (a : S) (y : ℝ) (hy : 0 ≤ y) : streamMeasure ν
      {ω | ∃ s : ℕ, g s + y ≤ (F a (fun i ↦ ω i a) s).toReal / c} ≤
        ENNReal.ofReal (exp (-y)) := by
    refine le_trans (measure_mono fun ω hω ↦ ?_) (h_one a a.2 y hy)
    obtain ⟨s, hs⟩ := hω
    exact ⟨s, ENNReal.ofReal_le_of_le_toReal ((le_div_iff₀' hc).1 hs)⟩
  have h_real := measure_exists_card_mul_add_le_sum_le (P := streamMeasure ν)
    (S := fun (a : S) s ω ↦ (F a (fun i ↦ ω i a) s).toReal / c) (g := g) h_indep
    (fun a s ↦ ((hFm a s).comp (by fun_prop)).ennreal_toReal.div_const c) hg hS
    (x := x) (by rwa [Fintype.card_coe])
  rw [Fintype.card_coe] at h_real
  -- outside a null set the statistics are finite, and the event is that of the real statistics
  have h_top : streamMeasure ν {ω | ∃ a ∈ S, ∃ s : ℕ, F a (fun i ↦ ω i a) s = ∞} = 0 := by
    refine measure_mono_null (t := ⋃ a : S, {ω | ∃ s : ℕ, F a (fun i ↦ ω i a) s = ∞})
      (fun ω ⟨a, ha, hω⟩ ↦ Set.mem_iUnion.2 ⟨⟨a, ha⟩, hω⟩) ?_
    exact measure_iUnion_null fun a ↦ streamMeasure_exists_mul_rateFunction_eq_top (hν a a.2)
  refine le_trans (measure_mono fun ω hω ↦ ?_) ((measure_union_le _ _).trans
    ((add_le_add h_real h_top.le).trans_eq (add_zero _)))
  obtain ⟨s, hs⟩ := hω
  by_cases hω : ∃ a ∈ S, ∃ s : ℕ, F a (fun i ↦ ω i a) s = ∞
  · exact Or.inr hω
  push Not at hω
  refine Or.inl ⟨fun a ↦ s a, ?_⟩
  have h_sum : ∑ a ∈ S, F a (fun i ↦ ω i a) (s a) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun a ha ↦ hω a ha (s a)
  have h := (ENNReal.ofReal_le_iff_le_toReal h_sum).1 hs
  rw [ENNReal.toReal_sum fun a ha ↦ hω a ha (s a)] at h
  rw [Finset.sum_coe_sort S s,
    Finset.sum_coe_sort S fun a ↦ (F a (fun i ↦ ω i a) (s a)).toReal / c, ← Finset.sum_div]
  exact (le_div_iff₀' hc).2 h

/-- **Joint time-uniform deviations of the empirical means, measured by the rate functions**, in
the reward stream model, for the arms of a finite set `S`. If the rewards of each arm `a ∈ S` are
integrable, with rate function `I_a`, then for `x ≥ #S`, the probability that
`#S log (2 n (n + 1)) + x ≤ ∑ a ∈ S, s a I_a((∑ i < s a, X_i a) / s a)` for some numbers of
rewards `s : α → ℕ`, with `n = ∑ a ∈ S, s a`, is at most `(x / #S) ^ #S exp (#S - x)`. -/
theorem streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) {x : ℝ} (hx : #S ≤ x) :
    streamMeasure ν {ω | ∃ s : α → ℕ, ENNReal.ofReal (#S *
        log (2 * ((∑ a ∈ S, s a : ℕ) : ℝ) * (((∑ a ∈ S, s a : ℕ) : ℝ) + 1)) + x) ≤
        ∑ a ∈ S, s a * rateFunction id (ν a) ((∑ i ∈ range (s a), ω i a) / s a)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) := by
  simpa only [one_mul] using streamMeasure_exists_mul_card_mul_add_le_sum_mul_rateFunction_le_of S
    hν monotone_log_two_mul_mul_add_one one_pos (fun a ha y hy ↦ by
      simpa only [one_mul] using streamMeasure_exists_log_add_le_mul_rateFunction_le (hν a ha) hy)
    hx

/-- **Peeled joint time-uniform deviations of the empirical means, measured by the rate
functions**, in the reward stream model, for the arms of a finite set `S`. If the rewards of each
arm `a ∈ S` are integrable, with rate function `I_a`, then for `η > 0` and `x ≥ #S`, the
probability that
`2 (#S (η log₂ n + log (2 / (1 - exp (-η)))) + x) ≤ ∑ a ∈ S, s a I_a((∑ i < s a, X_i a) / s a)`
for some numbers of rewards `s : α → ℕ`, with `n = ∑ a ∈ S, s a` and `log₂ n = Nat.log 2 n`, is
at most `(x / #S) ^ #S exp (#S - x)`. -/
theorem streamMeasure_exists_two_mul_card_mul_add_le_sum_mul_rateFunction_le [Countable α]
    (S : Finset α) (hν : ∀ a ∈ S, Integrable id (ν a)) {η : ℝ} (hη : 0 < η) {x : ℝ}
    (hx : #S ≤ x) :
    streamMeasure ν {ω | ∃ s : α → ℕ, ENNReal.ofReal (2 * (#S *
        (η * Nat.log 2 (∑ a ∈ S, s a) + log (2 / (1 - exp (-η)))) + x)) ≤
        ∑ a ∈ S, s a * rateFunction id (ν a) ((∑ i ∈ range (s a), ω i a) / s a)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) :=
  streamMeasure_exists_mul_card_mul_add_le_sum_mul_rateFunction_le_of S hν
    (g := fun n ↦ η * Nat.log 2 n + log (2 / (1 - exp (-η)))) (fun _ _ h ↦ by dsimp only; gcongr)
    two_pos (fun a ha _ hy ↦
      streamMeasure_exists_two_mul_add_le_mul_rateFunction_le (hν a ha) hη hy) hx

/-- **Joint time-uniform deviations of the empirical means, measured by the rate functions**, in
the reward stream model, for all the `K` arms: the case `S = univ` of
`streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le`. If the rewards of each arm
`a` are integrable, with rate function `I_a`, then for `x ≥ K`, the probability that
`K log (2 n (n + 1)) + x ≤ ∑ a, s a I_a((∑ i < s a, X_i a) / s a)` for some numbers of rewards
`s : α → ℕ`, with `n = ∑ a, s a`, is at most `(x / K) ^ K exp (K - x)`. -/
theorem streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le_univ [Fintype α]
    (hν : ∀ a, Integrable id (ν a)) {x : ℝ} (hx : Fintype.card α ≤ x) :
    streamMeasure ν {ω | ∃ s : α → ℕ, ENNReal.ofReal (Fintype.card α *
        log (2 * ((∑ a, s a : ℕ) : ℝ) * (((∑ a, s a : ℕ) : ℝ) + 1)) + x) ≤
        ∑ a, s a * rateFunction id (ν a) ((∑ i ∈ range (s a), ω i a) / s a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  have h := streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le univ
    (fun a _ ↦ hν a) (x := x) (by rwa [card_univ])
  rwa [card_univ] at h

/-! ### Runs of an algorithm -/

variable [DecidableEq α] [Countable α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {x : ℝ}

/-- **Time-uniform deviations of the empirical means along a run above a monotone threshold**,
for the arms of a set `S`. In a run of any algorithm against `Environment.bandit ν`, let the
rewards of each arm `a ∈ S` be integrable, with rate function `I_a`, let `g` be monotone and
`c > 0`, and suppose that for each arm `a ∈ S` and `y ≥ 0`, the probability that
`c (g s + y) ≤ s I_a(μ̂_s)` for some number `s` of rewards is at most `exp (-y)` in the reward
stream model. Then for `x ≥ #S`, the probability that at some round `t`,
`c (#S g t + x) ≤ ∑ a ∈ S, N_a(t) I_a(μ̂_a(t))`, is at most `(x / #S) ^ #S exp (#S - x)`. -/
private lemma measure_exists_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le_of
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) {g : ℕ → ℝ} (hg : Monotone g) {c : ℝ} (hc : 0 < c)
    (h_one : ∀ a ∈ S, ∀ y, 0 ≤ y → streamMeasure ν {ω | ∃ s : ℕ, ENNReal.ofReal (c * (g s + y)) ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ≤ ENNReal.ofReal (exp (-y)))
    (hx : #S ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (c * (#S * g t + x)) ≤
        ∑ a ∈ S, pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    ((measure_exists_pullCount_sumRewards_pi_le h fun s y ↦
      ENNReal.ofReal (c * (#S * g (∑ a ∈ S, s a) + x)) ≤
        ∑ a ∈ S, s a * rateFunction id (ν a) (y a / s a)).trans
      (streamMeasure_exists_mul_card_mul_add_le_sum_mul_rateFunction_le_of S hν hg hc h_one hx))
  obtain ⟨t, ht⟩ := hω
  -- the arms of `S` have been pulled at most `t` times in total after `t` rounds
  have h_g := hg (sum_pullCount_le (A := A) S t ω)
  refine ⟨t, le_trans (ENNReal.ofReal_le_ofReal ?_) (by simpa only [empMean] using ht)⟩
  have hc0 := hc.le
  gcongr

/-- **Time-uniform deviations of the empirical means along a run, measured by the rate
functions** (the deviation inequality of [LS, Lemma 33.7], for any integrable rewards), for the
arms of a set `S`. In a run of any algorithm against `Environment.bandit ν`, if the rewards of each
arm `a ∈ S` are integrable, with rate function `I_a`, then for `x ≥ #S`, the probability that at
some round `t`, the pull counts `N_a(t)` and the empirical means `μ̂_a(t)` satisfy
`#S log (2 t (t + 1)) + x ≤ ∑ a ∈ S, N_a(t) I_a(μ̂_a(t))`, is at most
`(x / #S) ^ #S exp (#S - x)`. For `S = univ`, `#S` is the number `K` of arms; for the pairs of
arms, the threshold grows as `2 log (2 t (t + 1))` whatever the number of arms. -/
theorem measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) (hx : #S ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (#S * log (2 * t * (t + 1)) + x) ≤
        ∑ a ∈ S, pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) := by
  simpa only [one_mul] using measure_exists_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le_of
    h S hν monotone_log_two_mul_mul_add_one one_pos (fun a ha y hy ↦ by
      simpa only [one_mul] using streamMeasure_exists_log_add_le_mul_rateFunction_le (hν a ha) hy)
    hx

/-- **Peeled time-uniform deviations of the empirical means along a run, measured by the rate
functions**, for the arms of a set `S`. In a run of any algorithm against `Environment.bandit ν`,
if the rewards of each arm `a ∈ S` are integrable, with rate function `I_a`, then for `η > 0` and
`x ≥ #S`, the probability that at some round `t`, the pull counts `N_a(t)` and the empirical means
`μ̂_a(t)` satisfy
`2 (#S (η log₂ t + log (2 / (1 - exp (-η)))) + x) ≤ ∑ a ∈ S, N_a(t) I_a(μ̂_a(t))`, with
`log₂ t = Nat.log 2 t`, is at most `(x / #S) ^ #S exp (#S - x)`. -/
theorem measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) {η : ℝ} (hη : 0 < η) (hx : #S ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (2 * (#S *
        (η * Nat.log 2 t + log (2 / (1 - exp (-η)))) + x)) ≤
        ∑ a ∈ S, pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) :=
  measure_exists_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le_of h S hν
    (g := fun n ↦ η * Nat.log 2 n + log (2 / (1 - exp (-η)))) (fun _ _ h ↦ by dsimp only; gcongr)
    two_pos (fun a ha _ hy ↦
      streamMeasure_exists_two_mul_add_le_mul_rateFunction_le (hν a ha) hη hy) hx

/-- **Time-uniform deviations of the empirical means along a run, measured by the rate
functions** (the deviation inequality of [LS, Lemma 33.7], for any integrable rewards), for all the
`K` arms: the case `S = univ` of
`measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le`. In a run of any algorithm
against `Environment.bandit ν`, if the rewards of each arm `a` are integrable, with rate function
`I_a`, then for `x ≥ K`, the probability that at some round `t`,
`K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) I_a(μ̂_a(t))`, is at most `(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le_univ [Fintype α]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hν : ∀ a, Integrable id (ν a))
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (Fintype.card α * log (2 * t * (t + 1)) + x) ≤
        ∑ a, pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  have h_dev := measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le h univ
    (fun a _ ↦ hν a) (x := x) (by rwa [card_univ])
  rwa [card_univ] at h_dev

end LMLExplore
