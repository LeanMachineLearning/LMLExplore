/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.SubLogInv
public import LMLExplore.SequentialLearning.RateFunctionDeviation
import LMLExplore.Analysis.PSeries

/-!
# Self-normalized deviations of the empirical means along a run, up to a horizon

Let the rewards of each arm `a` of the stochastic environment `Environment.bandit ν` be integrable,
with Cramér rate function `I_a = rateFunction id (ν a)`. After `N_a(t)` pulls with empirical mean
`μ̂_a(t)`, the statistic `N_a(t) I_a(μ̂_a(t))` measures how far `μ̂_a(t)` lies from the mean of `a`.
This file bounds the probability that this statistic exceeds a level `x > 0` at some round
`t ≤ n`, along a run of any algorithm, by `2 e (x log n + 1) exp (-x)`. The bound grows only
logarithmically with the horizon `n`, and needs no union bound over the numbers of pulls: in LML's
i.i.d. reward stream model, the self-normalized deviation inequality of Garivier and Cappé
[GC11, Theorem 10] (`ProbabilityTheory.iIndepFun.measure_exists_gt_and_le_mul_rateFunction_le` and
its lower-tail form) bounds each side of the mean by `e ⌈x log n⌉ exp (-x)` for all the numbers of
rewards `s ≤ n` at once, and the transfer of `SequentialLearning/SumRewards.lean` turns the bound
in the stream into a bound along the run, since an arm has at most `n` pulls before round `n`.
This is [DKM19, Lemma 5], there for arms in a canonical one-parameter exponential family.

The level `x_n = h⁻¹((1 + c) log n)`, with `h(u) = u - log u` and `h⁻¹ = Real.subLogInv`, makes
the bound summable over the horizons: from `x_n - log x_n ≥ (1 + c) log n` and `x_n ≥ 1`,
`(x_n log n + 1) exp (-x_n) ≤ (log n + 1) / n ^ (1 + c)`. For a finite set `S` of `k` arms, the
probability that some arm of `S` has `x_n ≤ N_a(t) I_a(μ̂_a(t))` at some round `t ≤ n` is
therefore at most `2 e k (log n + 1) / n ^ (1 + c)`, and these probabilities sum over `n` to at
most `2 e k (2 + 1 / c + 1 / c²)`. These are the concentration events `E_n` of the analysis of the
pure exploration algorithms of [DKM19] (Appendix B.2, Lemma 6): the sum of the probabilities of
their complements is the second term of the non-asymptotic sample-complexity bound
`𝔼[τ] ≤ T₀ + ∑_n P(E_nᶜ)` of the generalized likelihood ratio stopping rule
(`LMLExplore.Identification.IdentTask.expectedStoppingTime_glrt_le_add_tsum`). [DKM19, Lemma 6]
states the constant `2 e k / c²`, from a comparison of the sum with an integral and without the
`+ 1` of the ceiling of [GC11, Theorem 10]; the constant here comes from the explicit bounds
`∑ log n / n ^ p ≤ 1 + 1 / (p - 1) ^ 2` and `∑ 1 / n ^ p ≤ 1 + 1 / (p - 1)` of
`LMLExplore/Analysis/PSeries.lean`.

For rewards dominated by exponential families, the rate function of each arm is at least the
extended divergence `dbar_a(·, μ_a)` of its family, so the same bounds hold for the generalized
likelihood ratio statistic `N_a(t) dbar_a(μ̂_a(t), μ_a)`, which is the form of [DKM19]; these
forms are in `SequentialLearning/ExpFamilyDeviation.lean`.

## Main statements

* `LMLExplore.streamMeasure_exists_le_mul_rateFunction_le`: in the reward stream model, the
  probability that `x ≤ s I_a(μ̂_s)` for some number `s ≤ n` of rewards is at most
  `2 e (x log n + 1) exp (-x)`.
* `LMLExplore.measure_exists_le_pullCount_mul_rateFunction_le` [DKM19, Lemma 5]: along a run of
  any algorithm, the probability that `x ≤ N_a(t) I_a(μ̂_a(t))` at some round `t ≤ n` is at most
  `2 e (x log n + 1) exp (-x)`.
* `LMLExplore.measure_exists_mem_exists_le_pullCount_mul_rateFunction_le`: the same for some arm
  of a set `S`, with the factor `#S`.
* `LMLExplore.measure_exists_mem_exists_subLogInv_le_pullCount_mul_rateFunction_le`
  [DKM19, Lemma 6]: at the level `h⁻¹((1 + c) log n)`, the bound
  `2 e #S (log n / n ^ (1 + c) + 1 / n ^ (1 + c))`.
* `LMLExplore.tsum_measure_exists_mem_exists_subLogInv_le_pullCount_mul_rateFunction_le`
  [DKM19, Lemma 6]: these probabilities sum to at most `2 e #S (2 + 1 / c + 1 / c²)`.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Appendix B (Lemmas 5 and 6), arXiv:1906.10431.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

namespace LMLExplore

variable {α : Type*} [MeasurableSpace α] [Countable α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {x : ℝ}

/-! ### The reward stream model -/

/-- **Self-normalized deviations of one arm up to a horizon, in the stream model**
[GC11, Theorem 10]. If the rewards of the arm `a` are integrable, with rate function `I_a`, then
for `x > 0` and every horizon `n`, the probability that `x ≤ s I_a(μ̂_s)` for some number `s ≤ n`
of rewards, where `μ̂_s = (∑ i < s, X_i) / s`, is at most `2 e (x log n + 1) exp (-x)`. -/
theorem streamMeasure_exists_le_mul_rateFunction_le {a : α} (hν : Integrable id (ν a))
    (hx : 0 < x) (n : ℕ) :
    streamMeasure ν {ω | ∃ s ≤ n, ENNReal.ofReal x ≤
      s * rateFunction id (ν a) ((∑ i ∈ range s, ω i a) / s)} ≤
      ENNReal.ofReal (2 * exp 1 * (x * log n + 1) * exp (-x)) := by
  -- no deviation is possible with no reward
  have h_zero : ¬ ENNReal.ofReal x ≤ ((0 : ℕ) : ENNReal) * rateFunction id (ν a) 0 := by
    simpa using hx
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- with at most one reward, the Cramér–Chernoff bound for one reward applies
    refine (measure_mono fun ω hω ↦ ?_).trans
      ((streamMeasure_le_mul_rateFunction_le hν 1 x).trans (ENNReal.ofReal_le_ofReal ?_))
    · obtain ⟨s, hs, hle⟩ := hω
      obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
      · exact absurd (by simpa using hle) h_zero
      · exact hle
    · have h_log : log n = 0 := by interval_cases n <;> simp
      rw [h_log, mul_zero, zero_add, mul_one]
      gcongr
      exact le_mul_of_one_le_right zero_le_two (one_le_exp zero_le_one)
  -- for `n ≥ 2`, each side of the mean has the bound of [GC11, Theorem 10]
  have h_indep := iIndepFun_eval_streamMeasure'' ν a
  have hZ (i : ℕ) := (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedOn (Λ := Set.univ)
  have h_up := h_indep.measure_exists_gt_and_le_mul_rateFunction_le (fun i ↦ by fun_prop)
    (fun i ↦ (hZ i).mono (Set.subset_univ _)) hν hx hn
  have h_low := h_indep.measure_exists_lt_and_le_mul_rateFunction_le (fun i ↦ by fun_prop)
    (fun i ↦ (hZ i).mono (Set.subset_univ _)) hν hx hn
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    ((measure_union_le _ _).trans ((add_le_add h_up h_low).trans ?_))
  · obtain ⟨s, hs, hle⟩ := hω
    have hs1 : 1 ≤ s := by
      by_contra! h0
      obtain rfl : s = 0 := by omega
      exact h_zero (by simpa using hle)
    -- the rate function vanishes at the mean
    rcases lt_trichotomy (ν a)[id] ((∑ i ∈ range s, ω i a) / s) with h | h | h
    · exact Or.inl ⟨s, hs1, hs, h, hle⟩
    · rw [← h, rateFunction_integral hν, mul_zero] at hle
      exact absurd (by simpa using hle) h_zero
    · exact Or.inr ⟨s, hs1, hs, h, hle⟩
  · have h_ceil := Nat.ceil_lt_add_one (mul_nonneg hx.le (log_natCast_nonneg n))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ exp 1 * exp (-x) := by positivity
    nlinarith

/-! ### Runs of an algorithm -/

variable [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **Self-normalized deviations of one arm along a run, up to a horizon** [DKM19, Lemma 5]. In a
run of any algorithm against `Environment.bandit ν`, if the rewards of the arm `a` are integrable,
with rate function `I_a`, then for `x > 0` and every horizon `n`, the probability that
`x ≤ N_a(t) I_a(μ̂_a(t))` at some round `t ≤ n` is at most `2 e (x log n + 1) exp (-x)`. -/
theorem measure_exists_le_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (hν : Integrable id (ν a))
    (hx : 0 < x) (n : ℕ) :
    P {ω | ∃ t ≤ n, ENNReal.ofReal x ≤
        pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal (2 * exp 1 * (x * log n + 1) * exp (-x)) := by
  -- the arm has at most `n` pulls before round `n + 1`, so the event transfers to the stream
  refine le_trans (measure_mono fun ω hω ↦ ?_) ((measure_exists_lt_pullCount_sumRewards_le h a
    (n + 1) fun s y ↦ ENNReal.ofReal x ≤ s * rateFunction id (ν a) (y / s)).trans
    (le_trans (measure_mono fun ω hω ↦ ?_) (streamMeasure_exists_le_mul_rateFunction_le hν hx n)))
  · obtain ⟨t, ht, hle⟩ := hω
    exact ⟨t, Nat.lt_succ_of_le ht, by simpa only [empMean] using hle⟩
  · obtain ⟨s, hs, hle⟩ := hω
    exact ⟨s, Nat.lt_succ_iff.1 hs, hle⟩

/-- **Self-normalized deviations of the arms of a set along a run, up to a horizon.** In a run of
any algorithm against `Environment.bandit ν`, if the rewards of each arm `a ∈ S` are integrable,
with rate function `I_a`, then for `x > 0` and every horizon `n`, the probability that some arm
`a ∈ S` has `x ≤ N_a(t) I_a(μ̂_a(t))` at some round `t ≤ n` is at most
`2 e #S (x log n + 1) exp (-x)`. -/
theorem measure_exists_mem_exists_le_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) (hx : 0 < x) (n : ℕ) :
    P {ω | ∃ a ∈ S, ∃ t ≤ n, ENNReal.ofReal x ≤
        pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal (2 * exp 1 * #S * (x * log n + 1) * exp (-x)) := by
  have h_eq : {ω | ∃ a ∈ S, ∃ t ≤ n, ENNReal.ofReal x ≤
      pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} = ⋃ a ∈ S, {ω | ∃ t ≤ n,
        ENNReal.ofReal x ≤ pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} := by
    ext ω
    simp
  -- a union bound over the arms of `S`
  rw [h_eq]
  refine (measure_biUnion_finset_le S _).trans ?_
  refine (sum_le_sum fun a ha ↦
    measure_exists_le_pullCount_mul_rateFunction_le h a (hν a ha) hx n).trans_eq ?_
  rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

/-- At the level `x = h⁻¹((1 + c) log n)`, with `h(u) = u - log u`, the factor
`(x log n + 1) exp (-x)` of the self-normalized deviation bounds is at most
`log n / n ^ (1 + c) + 1 / n ^ (1 + c)`. -/
private lemma mul_log_add_one_mul_exp_neg_subLogInv_le {c : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    (subLogInv ((1 + c) * log n) * log n + 1) * exp (-subLogInv ((1 + c) * log n)) ≤
      log n / (n : ℝ) ^ (1 + c) + 1 / (n : ℝ) ^ (1 + c) := by
  set y := subLogInv ((1 + c) * log n)
  have hy1 : 1 ≤ y := one_le_subLogInv _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `y exp (-y) ≤ exp (-(1 + c) log n) = 1 / n ^ (1 + c)`
  have h_mul : y * exp (-y) ≤ 1 / (n : ℝ) ^ (1 + c) := by
    refine (subLogInv_mul_exp_neg_subLogInv_le _).trans_eq ?_
    rw [rpow_def_of_pos hn0, one_div, ← exp_neg, mul_comm (log _)]
  have h_exp : exp (-y) ≤ y * exp (-y) := le_mul_of_one_le_left (exp_pos _).le hy1
  have h_log := log_natCast_nonneg n
  calc (y * log n + 1) * exp (-y) = log n * (y * exp (-y)) + exp (-y) := by ring
  _ ≤ log n * (1 / (n : ℝ) ^ (1 + c)) + 1 / (n : ℝ) ^ (1 + c) := by gcongr; linarith
  _ = log n / (n : ℝ) ^ (1 + c) + 1 / (n : ℝ) ^ (1 + c) := by rw [mul_one_div]

/-- **The concentration events of [DKM19, Lemma 6], at one horizon.** In a run of any algorithm
against `Environment.bandit ν`, if the rewards of each arm `a ∈ S` are integrable, with rate
function `I_a`, then for every real `c` and every horizon `n`, the probability that some arm
`a ∈ S` has `h⁻¹((1 + c) log n) ≤ N_a(t) I_a(μ̂_a(t))` at some round `t ≤ n`, with
`h(u) = u - log u`, is at most `2 e #S (log n / n ^ (1 + c) + 1 / n ^ (1 + c))`. For `c > 0` these
bounds are summable over `n`. -/
theorem measure_exists_mem_exists_subLogInv_le_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) (c : ℝ) (n : ℕ) :
    P {ω | ∃ a ∈ S, ∃ t ≤ n, ENNReal.ofReal (subLogInv ((1 + c) * log n)) ≤
        pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal (2 * exp 1 * #S * (log n / (n : ℝ) ^ (1 + c) + 1 / (n : ℝ) ^ (1 + c))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no arm has been pulled before the first round
    refine (measure_mono_null (fun ω hω ↦ (?_ : ω ∈ (∅ : Set Ω))) measure_empty).trans_le
      zero_le
    obtain ⟨a, _, t, ht, hle⟩ := hω
    obtain rfl : t = 0 := by omega
    simp only [pullCount_zero, CharP.cast_eq_zero, zero_mul, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at hle
    exact absurd hle (not_le.2 (subLogInv_pos _))
  refine (measure_exists_mem_exists_le_pullCount_mul_rateFunction_le h S hν
    (subLogInv_pos _) n).trans (ENNReal.ofReal_le_ofReal ?_)
  have h_le := mul_log_add_one_mul_exp_neg_subLogInv_le (c := c) hn
  calc 2 * exp 1 * #S * (subLogInv ((1 + c) * log n) * log n + 1) *
        exp (-subLogInv ((1 + c) * log n))
  _ = 2 * exp 1 * #S * ((subLogInv ((1 + c) * log n) * log n + 1) *
        exp (-subLogInv ((1 + c) * log n))) := by ring
  _ ≤ 2 * exp 1 * #S * (log n / (n : ℝ) ^ (1 + c) + 1 / (n : ℝ) ^ (1 + c)) := by gcongr

/-- For `c > 0`, the bounds `2 e k (log n / n ^ (1 + c) + 1 / n ^ (1 + c))` of the concentration
events of [DKM19, Lemma 6] sum over `n` to at most `2 e k (2 + 1 / c + 1 / c²)`. -/
private lemma tsum_ofReal_mul_log_div_rpow_add_one_div_rpow_le {c k : ℝ} (hc : 0 < c)
    (hk : 0 ≤ k) :
    ∑' n : ℕ, ENNReal.ofReal (2 * exp 1 * k * (log n / (n : ℝ) ^ (1 + c) + 1 / (n : ℝ) ^ (1 + c)))
      ≤ ENNReal.ofReal (2 * exp 1 * k * (2 + 1 / c + 1 / c ^ 2)) := by
  have hp : 1 < 1 + c := by linarith
  have h_log := summable_log_div_nat_rpow hp
  have h_one := summable_one_div_nat_rpow.2 hp
  have h0 : 0 ≤ 2 * exp 1 * k := by positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) ((h_log.add h_one).mul_left _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [tsum_mul_left, h_log.tsum_add h_one]
  have h1 := tsum_log_div_nat_rpow_le hp
  have h2 := tsum_one_div_nat_rpow_le hp
  rw [add_sub_cancel_left] at h1 h2
  calc 2 * exp 1 * k * (∑' n : ℕ, log n / (n : ℝ) ^ (1 + c) + ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + c))
  _ ≤ 2 * exp 1 * k * ((1 + 1 / c ^ 2) + (1 + 1 / c)) := by gcongr
  _ = 2 * exp 1 * k * (2 + 1 / c + 1 / c ^ 2) := by ring

/-- **The concentration events of [DKM19, Lemma 6] are summable.** In a run of any algorithm
against `Environment.bandit ν`, if the rewards of each arm `a ∈ S` are integrable, with rate
function `I_a`, then for `c > 0`, the probabilities, over the horizons `n`, that some arm `a ∈ S`
has `h⁻¹((1 + c) log n) ≤ N_a(t) I_a(μ̂_a(t))` at some round `t ≤ n`, with `h(u) = u - log u`,
sum to at most `2 e #S (2 + 1 / c + 1 / c²)`. -/
theorem tsum_measure_exists_mem_exists_subLogInv_le_pullCount_mul_rateFunction_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (S : Finset α)
    (hν : ∀ a ∈ S, Integrable id (ν a)) {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, P {ω | ∃ a ∈ S, ∃ t ≤ n, ENNReal.ofReal (subLogInv ((1 + c) * log n)) ≤
        pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤
      ENNReal.ofReal (2 * exp 1 * #S * (2 + 1 / c + 1 / c ^ 2)) :=
  (tsum_le_tsum fun n ↦
    measure_exists_mem_exists_subLogInv_le_pullCount_mul_rateFunction_le h S hν c n).trans
    (tsum_ofReal_mul_log_div_rpow_add_one_div_rpow_le hc (Nat.cast_nonneg _))

end LMLExplore
