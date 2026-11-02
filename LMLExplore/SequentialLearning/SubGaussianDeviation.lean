/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Bandits.Concentration
public import LMLExplore.Probability.Moments.ExponentialTail

/-!
# Time-uniform deviations of the empirical means of all the arms, for sub-Gaussian rewards

Let the rewards of each arm `a` of the stochastic environment `stationaryEnv ν` be
`σ²_a`-sub-Gaussian with mean `μ_a`. After `N_a` pulls with empirical mean `μ̂_a`, the
statistic `N_a (μ̂_a - μ_a)² / (2 σ²_a)` is the divergence `N_a d(μ̂_a, μ_a)` of Gaussian arms of
variance `σ²_a`, which the generalized likelihood ratio stopping rules of fixed-confidence
identification compare with a threshold. This file proves that, along a run of any algorithm,
the sum of these statistics over the `K` arms rarely exceeds `K log (2 t (t + 1)) + x` at any
round `t`: the probability of this event is at most `(x / K) ^ K exp (K - x)` for `x ≥ K`.

For one arm, in LML's i.i.d. reward stream model, Hoeffding's inequality and a union bound over
the number `s` of rewards give
`P(∃ s, log (2 s (s + 1)) + y ≤ s (μ̂_s - μ)² / (2 σ²)) ≤ exp (-y)` [LS, Lemma 33.8]. The arms
are independent in the stream model, so [LS, Proposition 33.9]
(`LMLExplore.measure_exists_card_mul_add_le_sum_le`) bounds the joint deviation over all the
vectors of numbers of rewards, and the joint transfer of `SequentialLearning/SumRewards.lean` turns
it into a bound along the run, at all rounds simultaneously. This is the deviation inequality of
the proof of [LS, Lemma 33.7]; Lattimore and Szepesvári state it for Gaussian arms with unit
variance and `log (t (t + 1))` in place of `log (2 t (t + 1))`, which accounts for the two tails
of a sub-Gaussian variable.

## Main statements

* `LMLExplore.iIndepFun_arm_streamMeasure`: in the stream model, the reward sequences of the arms
  are independent.
* `LMLExplore.streamMeasure_le_sq_div_le`: for a σ²-sub-Gaussian arm and `s ≠ 0` rewards in the
  stream model, `P(z ≤ s (μ̂_s - μ)² / (2 σ²)) ≤ 2 exp (-z)`.
* `LMLExplore.streamMeasure_exists_log_add_le_sq_div_le`: [LS, Lemma 33.8] for a σ²-sub-Gaussian
  arm, in the stream model.
* `LMLExplore.streamMeasure_exists_card_mul_log_add_le_sum_sq_div_le`: the joint deviation over
  all the arms and all the vectors of numbers of rewards, in the stream model.
* `LMLExplore.measure_exists_card_mul_log_add_le_sum_pullCount_mul_sq_div_le`: along a run of any
  algorithm, `P(∃ t, K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) (μ̂_a(t) - μ_a)² / (2 σ²_a))` is at most
  `(x / K) ^ K exp (K - x)` for `x ≥ K`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemmas 33.7 and 33.8 and Proposition 33.9.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

open scoped ENNReal NNReal

namespace LMLExplore

variable {α : Type*} [MeasurableSpace α]

/-! ### The reward stream model -/

/-- In LML's reward stream model, the reward sequences `(ω i a)_i` of the arms `a` are
independent. -/
theorem iIndepFun_arm_streamMeasure {𝓡 : Type*} [MeasurableSpace 𝓡] (ν : Kernel α 𝓡)
    [IsMarkovKernel ν] :
    iIndepFun (fun a (ω : ℕ → α → 𝓡) i ↦ ω i a) (streamMeasure ν) := by
  -- the entries `ω i a`, indexed by `(a, i) : Σ _ : α, ℕ`, are independent with laws `ν a`
  have he : Function.Injective fun p : (_ : α) × ℕ ↦ (p.2, p.1) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨⟩
    rfl
  have h_entries : HasLaw (fun (ω : ℕ → α → 𝓡) (p : (_ : α) × ℕ) ↦ ω p.2 p.1)
      (Measure.infinitePi fun p : (_ : α) × ℕ ↦ ν p.1) (streamMeasure ν) :=
    ((iIndepFun_eval_streamMeasure ν).precomp he).hasLaw_infinitePi
      (fun p ↦ hasLaw_eval_eval_streamMeasure ν p.2 p.1)
      (Measurable.of_eval fun p ↦
        (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)).aemeasurable
  -- so the array of the reward sequences of the arms has law `⨂ a, ⨂ i, ν a`
  have h_arms : HasLaw (fun (ω : ℕ → α → 𝓡) a i ↦ ω i a)
      (Measure.infinitePi fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν a) (streamMeasure ν) := by
    have h := (hasLaw_map (P := Measure.infinitePi fun p : (_ : α) × ℕ ↦ ν p.1)
      (MeasurableEquiv.piCurry fun (_ : α) (_ : ℕ) ↦ 𝓡).measurable.aemeasurable).comp h_entries
    -- `Sigma.curry` arranges the entries indexed by `Σ _ : α, ℕ` as the array of the arms
    rwa [Measure.infinitePi_map_piCurry (μ := fun a (_ : ℕ) ↦ ν a), MeasurableEquiv.coe_piCurry,
      Function.comp_def] at h
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun a ↦ by fun_prop, h_arms.map_eq]
  congr 1
  ext a : 1
  rw [← (hasLaw_eval_infinitePi _ a).comp h_arms |>.map_eq, Function.comp_def]

variable {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- The partial sums of `1 / ((s + 1) (s + 2)) = 1 / (s + 1) - 1 / (s + 2)` are at most `1`. -/
private lemma sum_range_inv_mul_le_one (n : ℕ) :
    ∑ s ∈ range n, ((s + 1 : ℝ) * (s + 1 + 1))⁻¹ ≤ 1 := by
  have h (s : ℕ) : ((s + 1 : ℝ) * (s + 1 + 1))⁻¹ = ((s : ℝ) + 1)⁻¹ - (((s + 1 : ℕ) : ℝ) + 1)⁻¹ := by
    push_cast
    field_simp
    ring
  rw [sum_congr rfl fun s _ ↦ h s, sum_range_sub' (fun s : ℕ ↦ ((s : ℝ) + 1)⁻¹) n]
  simp only [CharP.cast_eq_zero, zero_add, inv_one]
  exact sub_le_self _ (by positivity)

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
  have h_up : (streamMeasure ν).real {ω | ε ≤ T ω} ≤ exp (-z) :=
    hε2 ▸ HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
      (Bandits.iIndepFun_streamMeasure_sub_mean ν a)
      (fun i _ ↦ Bandits.hasSubgaussianMGF_streamMeasure_sub_mean hν i) (sqrt_nonneg _)
  have h_low : (streamMeasure ν).real {ω | T ω ≤ -ε} ≤ exp (-z) :=
    hε2 ▸ HasSubgaussianMGF.measure_sum_range_le_le_of_iIndepFun
      (Bandits.iIndepFun_streamMeasure_sub_mean ν a)
      (fun i _ ↦ Bandits.hasSubgaussianMGF_streamMeasure_sub_mean hν i) (sqrt_nonneg _)
  calc streamMeasure ν {ω | z ≤ T ω ^ 2 / (2 * σ2 * s)}
  _ ≤ streamMeasure ν {ω | ε ≤ T ω} + streamMeasure ν {ω | T ω ≤ -ε} :=
    (measure_mono h_sub).trans (measure_union_le _ _)
  _ ≤ ENNReal.ofReal (exp (-z)) + ENNReal.ofReal (exp (-z)) := by
    rw [← ofReal_measureReal, ← ofReal_measureReal]
    exact add_le_add (ENNReal.ofReal_le_ofReal h_up) (ENNReal.ofReal_le_ofReal h_low)
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
  rcases hy.eq_or_lt with rfl | hy
  · simpa using prob_le_one
  set E : ℕ → Set (ℕ → α → ℝ) := fun s ↦ {ω | log (2 * s * (s + 1)) + y ≤
    (∑ i ∈ range s, (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 * s)}
  -- no deviation with `0` rewards, and the two-sided bound with `s + 1 ≥ 1` rewards
  have hE0 : E 0 = ∅ := by
    ext ω
    simp [E, hy.not_ge]
  have hE (s : ℕ) : streamMeasure ν (E (s + 1)) ≤
      ENNReal.ofReal (exp (-y) * ((s + 1 : ℝ) * (s + 1 + 1))⁻¹) := by
    have hlog : 0 ≤ log (2 * (s + 1 : ℕ) * ((s + 1 : ℕ) + 1)) :=
      log_nonneg (by push_cast; nlinarith)
    refine (streamMeasure_le_sq_div_le hν s.succ_ne_zero (by positivity)).trans_eq ?_
    congr 1
    rw [neg_add, exp_add, exp_neg, exp_log (by positivity)]
    push_cast
    field_simp
  -- a union bound over the number of rewards
  calc streamMeasure ν {ω | ∃ s : ℕ, log (2 * s * (s + 1)) + y ≤
      (∑ i ∈ range s, (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 * s)}
  _ = streamMeasure ν (⋃ s, E s) := by
    congr 1
    ext ω
    simp [E]
  _ ≤ ∑' s, streamMeasure ν (E s) := measure_iUnion_le _
  _ ≤ ENNReal.ofReal (exp (-y)) := by
    refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
    cases n with
    | zero => simp
    | succ n =>
      rw [sum_range_succ', hE0, measure_empty, add_zero]
      calc ∑ s ∈ range n, streamMeasure ν (E (s + 1))
      _ ≤ ∑ s ∈ range n, ENNReal.ofReal (exp (-y) * ((s + 1 : ℝ) * (s + 1 + 1))⁻¹) :=
        sum_le_sum fun s _ ↦ hE s
      _ = ENNReal.ofReal (exp (-y) * ∑ s ∈ range n, ((s + 1 : ℝ) * (s + 1 + 1))⁻¹) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ by positivity, mul_sum]
      _ ≤ ENNReal.ofReal (exp (-y)) :=
        ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (exp_pos _).le
          (sum_range_inv_mul_le_one n))

/-- The boundary `n ↦ log (2 n (n + 1))` of [LS, Lemma 33.8] is monotone. -/
private lemma monotone_log_two_mul_mul_add_one :
    Monotone fun n : ℕ ↦ log (2 * n * (n + 1)) := by
  intro n m hnm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using Real.log_natCast_nonneg (2 * m * (m + 1))
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
    exact log_le_log (by positivity) (by gcongr)

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
  -- the statistics of the arms are functions of their independent reward sequences
  have h_indep : iIndepFun (fun a (ω : ℕ → α → ℝ) (s : ℕ) ↦
      (∑ i ∈ range s, (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 a * s)) (streamMeasure ν) :=
    (iIndepFun_arm_streamMeasure ν).comp
      (fun a (f : ℕ → ℝ) (s : ℕ) ↦ (∑ i ∈ range s, (f i - (ν a)[id])) ^ 2 / (2 * σ2 a * s))
      fun a ↦ Measurable.of_eval fun s ↦ by fun_prop
  exact measure_exists_card_mul_add_le_sum_le (P := streamMeasure ν)
    (S := fun a s ω ↦ (∑ i ∈ range s, (ω i a - (ν a)[id])) ^ 2 / (2 * σ2 a * s))
    (g := fun n : ℕ ↦ log (2 * n * (n + 1))) h_indep (fun a s ↦ by fun_prop)
    monotone_log_two_mul_mul_add_one
    (fun a y hy ↦ streamMeasure_exists_log_add_le_sq_div_le (hν a) hy) hx

/-! ### Runs of an algorithm -/

variable [Fintype α] [DecidableEq α] [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}

/-- **Time-uniform deviations of the empirical means of sub-Gaussian arms along a run** (the
deviation inequality of [LS, Lemma 33.7]). In a run of any algorithm against `stationaryEnv ν`,
if each arm `a` is `σ²_a`-sub-Gaussian with mean `μ_a`, then for `x ≥ K`, with `K` the number of
arms, the probability that at some round `t`, the pull counts `N_a(t)` and the empirical means
`μ̂_a(t)` satisfy `K log (2 t (t + 1)) + x ≤ ∑ a, N_a(t) (μ̂_a(t) - μ_a)² / (2 σ²_a)`, is at most
`(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_card_mul_log_add_le_sum_pullCount_mul_sq_div_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) {σ2 : α → ℝ≥0}
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) (σ2 a) (ν a)) {x : ℝ}
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ t : ℕ, Fintype.card α * log (2 * t * (t + 1)) + x ≤
        ∑ a, pullCount A a t ω * (empMean A R a t ω - (ν a)[id]) ^ 2 / (2 * σ2 a)} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  -- the statistic of an arm with `N` pulls, sum of rewards `S` and empirical mean `M`
  have h_stat (N : ℕ) (S M m : ℝ) (σ2 : ℝ≥0) (hS : N ≠ 0 → S = N * M) :
      N * (M - m) ^ 2 / (2 * σ2) = (S - N * m) ^ 2 / (2 * σ2 * N) := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
      rw [hS hN]
      field_simp
  refine le_trans (measure_mono fun ω ⟨t, ht⟩ ↦ ?_)
    ((measure_exists_pullCount_sumRewards_pi_le h fun s y ↦
      Fintype.card α * log (2 * ((∑ a, s a : ℕ) : ℝ) * (((∑ a, s a : ℕ) : ℝ) + 1)) + x ≤
        ∑ a, (y a - s a * (ν a)[id]) ^ 2 / (2 * σ2 a * s a)).trans
      (le_of_eq_of_le ?_ (streamMeasure_exists_card_mul_log_add_le_sum_sq_div_le hν hx)))
  · refine ⟨t, ?_⟩
    simp only [sum_pullCount]
    refine ht.trans_eq (sum_congr rfl fun a _ ↦ ?_)
    exact h_stat _ _ _ _ _ sumRewards_eq_pullCount_mul_empMean
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]

end LMLExplore
