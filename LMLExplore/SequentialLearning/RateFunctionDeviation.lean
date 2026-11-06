/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.SumRewards
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
public import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction
public import LMLExplore.Probability.LargeDeviations.Chernoff
public import LMLExplore.Probability.Moments.ExponentialTail
public import LMLExplore.SequentialLearning.SumRewards

/-!
# Time-uniform deviations of the empirical means, measured by the rate function

Let the rewards of each arm `a` of the stochastic environment `Environment.bandit ν` be integrable,
with Cramér rate function `I_a = rateFunction id (ν a)`. After `N_a` pulls with empirical mean
`μ̂_a`, the statistic `N_a I_a(μ̂_a)` measures how far `μ̂_a` lies from the mean of `a`. This file
proves that, along a run of any algorithm, the sum of these statistics over the `K` arms rarely
exceeds `K log (2 t (t + 1)) + x` at any round `t`: the probability of this event is at most
`(x / K) ^ K exp (K - x)` for `x ≥ K`.

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

If the rewards of the arm `a` are dominated, in moment generating function, by the member of mean
`μ_a` of an exponential family `(ρ_a, T_a)`, the rate function of the arm is at least the extended
divergence `dbar_a(·, μ_a)` of the family (`MeasureTheory.Measure.expFamilyRate`), so the same
bound holds for the generalized likelihood ratio statistic `∑ a, N_a dbar_a(μ̂_a, μ_a)` of the
empirical means, including at empirical means on the boundary of the means of the families, such
as the empirical means `0` and `1` of Bernoulli rewards. This is the deviation inequality behind the
`δ`-correctness of generalized likelihood ratio stopping rules for exponential families
[GK16, Proposition 12; LS, Lemma 33.7]. For σ²-sub-Gaussian rewards, the rate function is at
least `(x - μ_a)² / (2 σ²)`, with equality for Gaussian rewards of variance `σ²`, and
`SequentialLearning/SubGaussianDeviation.lean` deduces the same bounds for that statistic.

## Main statements

* `LMLExplore.streamMeasure_le_mul_rateFunction_le`: for an integrable arm and `s` rewards in the
  stream model, `P(z ≤ s I_a(μ̂_s)) ≤ 2 exp (-z)`.
* `LMLExplore.streamMeasure_exists_log_add_le_mul_rateFunction_le`: [LS, Lemma 33.8] for the rate
  function, in the stream model.
* `LMLExplore.streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le`: the joint
  deviation over all the arms and all the vectors of numbers of rewards, in the stream model.
* `LMLExplore.measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le`: along a run of
  any algorithm, `P(∃ t, K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) I_a(μ̂_a(t)))` is at most
  `(x / K) ^ K exp (K - x)` for `x ≥ K`.
* `LMLExplore.measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le`: the same for
  `∑ a, N_a(t) dbar_a(μ̂_a(t), μ_a)`, for rewards dominated by members of exponential families.

## References

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

/-- **Joint time-uniform deviations of the empirical means, measured by the rate functions**, in
the reward stream model. If the rewards of each arm `a` are integrable, with rate function `I_a`,
then for `x ≥ K`, with `K` the number of arms, the probability that
`K log (2 n (n + 1)) + x ≤ ∑ a, s a I_a((∑ i < s a, X_i a) / s a)` for some numbers of rewards
`s : α → ℕ`, with `n = ∑ a, s a`, is at most `(x / K) ^ K exp (K - x)`. -/
theorem streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le [Fintype α]
    (hν : ∀ a, Integrable id (ν a)) {x : ℝ} (hx : Fintype.card α ≤ x) :
    streamMeasure ν {ω | ∃ s : α → ℕ, ENNReal.ofReal (Fintype.card α *
        log (2 * ((∑ a, s a : ℕ) : ℝ) * (((∑ a, s a : ℕ) : ℝ) + 1)) + x) ≤
        ∑ a, s a * rateFunction id (ν a) ((∑ i ∈ range (s a), ω i a) / s a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  -- the statistic `s I_a(μ̂_s)` of the first `s` rewards `f` of the arm `a`
  set F : α → (ℕ → ℝ) → ℕ → ℝ≥0∞ :=
    fun a f s ↦ s * rateFunction id (ν a) ((∑ i ∈ range s, f i) / s) with hF
  have hFm (a : α) (s : ℕ) : Measurable fun f : ℕ → ℝ ↦ F a f s :=
    measurable_const.mul ((lowerSemicontinuous_rateFunction _ _).measurable.comp (by fun_prop))
  -- the real statistics of the arms are functions of their independent reward sequences
  have h_indep : iIndepFun (fun a (ω : ℕ → α → ℝ) (s : ℕ) ↦ (F a (fun i ↦ ω i a) s).toReal)
      (streamMeasure ν) :=
    (iIndepFun_arm_streamMeasure ν).comp (fun a f s ↦ (F a f s).toReal)
      fun a ↦ Measurable.of_eval fun s ↦ (hFm a s).ennreal_toReal
  have hS (a : α) (y : ℝ) (hy : 0 ≤ y) : streamMeasure ν
      {ω | ∃ s : ℕ, log (2 * s * (s + 1)) + y ≤ (F a (fun i ↦ ω i a) s).toReal} ≤
        ENNReal.ofReal (exp (-y)) := by
    refine le_trans (measure_mono fun ω hω ↦ ?_)
      (streamMeasure_exists_log_add_le_mul_rateFunction_le (hν a) hy)
    obtain ⟨s, hs⟩ := hω
    exact ⟨s, ENNReal.ofReal_le_of_le_toReal hs⟩
  have h_real := measure_exists_card_mul_add_le_sum_le (P := streamMeasure ν)
    (S := fun a s ω ↦ (F a (fun i ↦ ω i a) s).toReal) (g := fun n : ℕ ↦ log (2 * n * (n + 1)))
    h_indep (fun a s ↦ ((hFm a s).comp (by fun_prop)).ennreal_toReal)
    monotone_log_two_mul_mul_add_one hS hx
  -- outside a null set the statistics are finite, and the event is that of the real statistics
  have h_top : streamMeasure ν {ω | ∃ a, ∃ s : ℕ, F a (fun i ↦ ω i a) s = ∞} = 0 := by
    rw [Set.ofPred_exists]
    exact measure_iUnion_null fun a ↦ streamMeasure_exists_mul_rateFunction_eq_top (hν a)
  refine le_trans (measure_mono fun ω hω ↦ ?_) ((measure_union_le _ _).trans
    ((add_le_add h_real h_top.le).trans_eq (add_zero _)))
  obtain ⟨s, hs⟩ := hω
  by_cases hω : ∃ a, ∃ s : ℕ, F a (fun i ↦ ω i a) s = ∞
  · exact Or.inr hω
  push Not at hω
  refine Or.inl ⟨s, ?_⟩
  have h_sum : ∑ a, F a (fun i ↦ ω i a) (s a) ≠ ∞ := ENNReal.sum_ne_top.2 fun a _ ↦ hω a (s a)
  rw [← ENNReal.toReal_sum fun a _ ↦ hω a (s a)]
  exact (ENNReal.ofReal_le_iff_le_toReal h_sum).1 hs

/-! ### Runs of an algorithm -/

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {x : ℝ}

/-- **Time-uniform deviations of the empirical means along a run, measured by the rate
functions** (the deviation inequality of [LS, Lemma 33.7], for any integrable rewards). In a run of
any algorithm against `Environment.bandit ν`, if the rewards of each arm `a` are integrable, with
rate function `I_a`, then for `x ≥ K`, with `K` the number of arms, the probability that at some
round `t`, the pull counts `N_a(t)` and the empirical means `μ̂_a(t)` satisfy
`K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) I_a(μ̂_a(t))`, is at most `(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hν : ∀ a, Integrable id (ν a))
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (Fintype.card α * log (2 * t * (t + 1)) + x) ≤
        ∑ a, pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    ((measure_exists_pullCount_sumRewards_pi_le h fun s y ↦
      ENNReal.ofReal (Fintype.card α *
        log (2 * ((∑ a, s a : ℕ) : ℝ) * (((∑ a, s a : ℕ) : ℝ) + 1)) + x) ≤
        ∑ a, s a * rateFunction id (ν a) (y a / s a)).trans
      (streamMeasure_exists_card_mul_log_add_le_sum_mul_rateFunction_le hν hx))
  obtain ⟨t, ht⟩ := hω
  exact ⟨t, by simpa only [sum_pullCount, empMean] using ht⟩

/-- **Time-uniform deviations of the empirical means along a run, for rewards dominated by
exponential families** ([GK16, Proposition 12], [LS, Lemma 33.7]). In a run of any algorithm
against `Environment.bandit ν`, let the rewards of each arm `a` be dominated on `Set.univ`, in
moment generating function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`,
with extended divergence `dbar_a` (`MeasureTheory.Measure.expFamilyRate`). Then for `x ≥ K`, with
`K` the number of arms, the probability that at some round `t`, the pull counts `N_a(t)` and the
empirical means `μ̂_a(t)` satisfy `K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) dbar_a(μ̂_a(t), μ a)`, is
at most `(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ}
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (Fintype.card α * log (2 * t * (t + 1)) + x) ≤
        ∑ a, pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  -- the rewards are integrable, and the rate function of each arm is at least `dbar_a(·, μ a)`
  have h_int (a : α) : Integrable id (ν a) := (hν a).integrable (by
    simpa only [Set.univ_inter] using Measure.zero_mem_interior_integrableExpSet_expFamily
      (Measure.natParam_mem_interior_integrableExpSet (hμ a)))
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le h h_int hx)
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ht.trans (sum_le_sum fun a _ ↦ ?_)⟩
  rw [Measure.expFamilyRate_def]
  gcongr
  exact ((hν a).mono (Set.subset_univ _)).rateFunction_le _

end LMLExplore
