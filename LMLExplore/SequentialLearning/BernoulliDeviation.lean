/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.InformationTheory.KrichevskyTrofimov
public import LMLExplore.SequentialLearning.LikelihoodRatio
public import LMLExplore.Bandits.Instances
public import LMLExplore.SequentialLearning.SumRewards

/-!
# Pairwise deviations of Bernoulli arms through the Krichevsky–Trofimov mixture

Along a run of any algorithm against a Bernoulli bandit with means `p`, for two arms `a ≠ b` with
means in `(0, 1)` and every `x > 0`,
`P(∃ n, log (2 n x) < N_a(n) d(μ̂_a(n), p_a) + N_b(n) d(μ̂_b(n), p_b)) ≤ 1 / x`,
where `N_c(n)` is the number of pulls of the arm `c` and `μ̂_c(n)` its empirical mean before round
`n`, and `d` is the binary relative entropy. This is the deviation inequality behind the
informational threshold of the GLRT for Bernoulli arms [GK16, Theorem 10], whose pairwise evidence
of a wrong arm and the best arm is the right-hand side.

## Main statements

* `LMLExplore.measure_exists_log_two_mul_mul_lt_klBer_le`: the pairwise deviation inequality.

## Implementation notes

As in [GK16, Appendix C.1], the proof mixes the likelihood ratios of the Bernoulli bandits whose
means on the arms `a` and `b` are `u` and `v`, against the true bandit, over the prior
`Beta(1/2, 1/2) ⊗ Beta(1/2, 1/2)` of `(u, v)`, and the mixture is the product of the
Krichevsky–Trofimov likelihood ratios of the two arms. In place of the change of measure of the
paper, the mixture is a nonnegative supermartingale with initial value `1`
(`SequentialLearning/LikelihoodRatio.lean`), so Ville's inequality bounds the probability that it
ever reaches `x` by `1 / x`. The Krichevsky–Trofimov bound [GK16, Lemma 11] bounds
`N_c d(μ̂_c, p_c)` by the logarithm of `2 √N_c` times the likelihood ratio of the arm `c`, and
`2 √N_a ⋅ 2 √N_b ≤ 2 (N_a + N_b) ≤ 2 n`.

This file is adapted from `SequentialLearning/KTDeviation.lean` of the formalization in
RemyDegenne/Garivier2016Optimal (commit 53ac67e4, directory `ForLMLExplore/`).

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, arXiv:1602.04589v2.
-/

public section

open MeasureTheory InformationTheory ProbabilityTheory Learning Finset Real unitInterval

open scoped ENNReal

namespace LMLExplore

variable {α Ω : Type*} [DecidableEq α] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {A : ℕ → Ω → α} {Y : ℕ → Ω → ℝ}

/-- The integral against `Beta(1/2, 1/2)` of the likelihood ratio `(u / p) ^ j ((1 - u) / (1 - p))
^ m`, written as the exponential of the log-likelihood ratio on `(0, 1)`, is the
Krichevsky–Trofimov likelihood ratio `kt(j, m) / (p ^ j (1 - p) ^ m)`. -/
private lemma integral_exp_ite_betaMeasure {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (j m : ℕ) :
    ∫ u, exp (if u ∈ Set.Ioo 0 1 then j * log (u / p) + m * log ((1 - u) / (1 - p)) else 0)
        ∂betaMeasure (1 / 2) (1 / 2) =
      (∫ u, u ^ j * (1 - u) ^ m ∂betaMeasure (1 / 2) (1 / 2)) / (p ^ j * (1 - p) ^ m) := by
  have hp1 : 0 < 1 - p := sub_pos.2 hp.2
  rw [← integral_div]
  refine integral_congr_ae ?_
  filter_upwards [TauCeti.Probability.ae_mem_Ioo_betaMeasure (1 / 2) (1 / 2)] with u hu
  have hu1 : 0 < 1 - u := sub_pos.2 hu.2
  rw [ite_eq_left hu, exp_add, ← log_pow, ← log_pow, exp_log (pow_pos (div_pos hu.1 hp.1) _),
    exp_log (pow_pos (div_pos hu1 hp1) _), div_pow, div_pow]
  field_simp

/-- Per arm: `N d(j / N, p) ≤ log (w Λ)`, with `Λ` the Krichevsky–Trofimov likelihood ratio and
`w = 2 √N`, or `w = 1` for `N = 0`. -/
private lemma mul_klBerReal_le_log {p : ℝ} (hp : p ∈ Set.Ioo 0 1) {j N : ℕ} (hj : j ≤ N) :
    (N : ℝ) * klBerReal (j / N) p ≤
      log ((if N = 0 then 1 else 2 * √(N : ℝ)) *
        ((∫ u, u ^ j * (1 - u) ^ (N - j) ∂betaMeasure (1 / 2) (1 / 2)) /
          (p ^ j * (1 - p) ^ (N - j)))) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : j = 0 := by omega
    rw [integral_pow_mul_one_sub_pow_betaMeasure (by norm_num) (by norm_num)]
    have hB := (beta_pos (α := 1 / 2) (β := 1 / 2) (by norm_num) (by norm_num)).ne'
    simp only [Nat.cast_zero, Nat.sub_self, add_zero]
    rw [div_self hB]
    simp
  rw [ite_eq_right hN.ne']
  exact mul_klBerReal_div_le_log_two_mul_sqrt_mul_integral_betaMeasure_div
    (k := j) (m := N - j) (n := N) (by omega) hN hp

/-- `w_a w_b ≤ 2 n` for the weights of `mul_klBerReal_le_log`, when `1 ≤ N_a + N_b ≤ n`. -/
private lemma ite_mul_ite_le {Na Nb n : ℕ} (h1 : 1 ≤ Na + Nb) (hn : Na + Nb ≤ n) :
    (if Na = 0 then 1 else 2 * √(Na : ℝ)) * (if Nb = 0 then 1 else 2 * √(Nb : ℝ)) ≤
      2 * n := by
  have hn' : ((Na : ℝ) + Nb) ≤ n := by exact_mod_cast hn
  have hsa := Real.sq_sqrt (Nat.cast_nonneg Na : (0 : ℝ) ≤ Na)
  have hsb := Real.sq_sqrt (Nat.cast_nonneg Nb : (0 : ℝ) ≤ Nb)
  have ha0 := Real.sqrt_nonneg (Na : ℝ)
  have hb0 := Real.sqrt_nonneg (Nb : ℝ)
  split_ifs with ha hb hb
  · omega
  · subst ha
    have hb1 : (1 : ℝ) ≤ Nb := by exact_mod_cast (by omega : 1 ≤ Nb)
    simp only [CharP.cast_eq_zero, zero_add] at hn'
    nlinarith
  · subst hb
    have ha1 : (1 : ℝ) ≤ Na := by exact_mod_cast (by omega : 1 ≤ Na)
    simp only [CharP.cast_eq_zero, add_zero] at hn'
    nlinarith
  · nlinarith [sq_nonneg (√(Na : ℝ) - √(Nb : ℝ))]

/-- The log-likelihood ratio `y log (q / r) + (1 - y) log ((1 - q) / (1 - r))` of a Bernoulli
observation `y` under the mean `q` against the mean `r`, set to `0` for `q ∉ (0, 1)`. -/
private noncomputable def berLLR (q r y : ℝ) : ℝ :=
  if q ∈ Set.Ioo 0 1 then y * log (q / r) + (1 - y) * log ((1 - q) / (1 - r)) else 0

/-- `berLLR q r y` is measurable in `(q, y)`. -/
private lemma measurable_berLLR (r : ℝ) : Measurable fun q : ℝ × ℝ ↦ berLLR q.1 r q.2 :=
  Measurable.ite (measurableSet_Ioo.preimage measurable_fst) (by fun_prop) measurable_const

/-- The likelihood ratio of a Bernoulli observation under the mean `q ∈ (0, 1)` against the mean
`p ∈ (0, 1)`, written as the exponential of its logarithm, has expectation `1` under the mean `p`;
so has the constant `1` used for `q ∉ (0, 1)`. -/
private lemma lintegral_ofReal_exp_berLLR_bernoulliMeasure {p : I} (hp : (p : ℝ) ∈ Set.Ioo 0 1)
    (q : ℝ) : ∫⁻ y, ENNReal.ofReal (exp (berLLR q p y)) ∂Ber((1 : ℝ), 0, p) = 1 := by
  by_cases hq : q ∈ Set.Ioo 0 1
  · have h1 : 0 < 1 - (p : ℝ) := sub_pos.2 hp.2
    have h2 : 0 < 1 - q := sub_pos.2 hq.2
    have hpq := div_pos hq.1 hp.1
    have hpq' := div_pos h2 h1
    rw [lintegral_bernoulliMeasure]
    norm_num [berLLR, hq, exp_log hpq, exp_log hpq']
    rw [← ENNReal.ofReal_mul hp.1.le, ← ENNReal.ofReal_mul h1.le,
      ← ENNReal.ofReal_add (mul_pos hp.1 hpq).le (mul_pos h1 hpq').le, ← ENNReal.ofReal_one]
    congr 1
    field_simp [hp.1.ne', h1.ne']
    ring
  · simp [berLLR, hq]

/-- The log-likelihood ratio of the bandit whose means on the arms `a` and `b` are `l.1` and `l.2`
against the bandit whose means on them are `pa` and `pb`, for the observation `y` of the arm `c`. -/
private noncomputable def pairLLR (a b : α) (pa pb : ℝ) (l : ℝ × ℝ) (c : α) (y : ℝ) : ℝ :=
  (if c = a then berLLR l.1 pa y else 0) + (if c = b then berLLR l.2 pb y else 0)

/-- `pairLLR a b pa pb l c y` is measurable in `(l, c, y)`. -/
private lemma measurable_pairLLR [MeasurableSingletonClass α] (a b : α) (pa pb : ℝ) :
    Measurable fun q : (ℝ × ℝ) × α × ℝ ↦ pairLLR a b pa pb q.1 q.2.1 q.2.2 := by
  refine Measurable.add ?_ ?_
  · refine Measurable.ite ((measurableSet_singleton a).preimage
      (measurable_fst.comp measurable_snd)) ?_ measurable_const
    exact (measurable_berLLR pa).comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  · refine Measurable.ite ((measurableSet_singleton b).preimage
      (measurable_fst.comp measurable_snd)) ?_ measurable_const
    exact (measurable_berLLR pb).comp ((measurable_snd.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))

/-- Under the Bernoulli bandit with means `p`, with `p a, p b ∈ (0, 1)`, the exponential of
`pairLLR` has expectation at most `1` for every arm: it is a likelihood ratio. -/
private lemma lintegral_ofReal_exp_pairLLR_le [Countable α] [MeasurableSingletonClass α]
    {p : α → I} {a b : α} (hab : a ≠ b) (hpa : (p a : ℝ) ∈ Set.Ioo 0 1)
    (hpb : (p b : ℝ) ∈ Set.Ioo 0 1) (l : ℝ × ℝ) (c : α) :
    ∫⁻ y, ENNReal.ofReal (exp (pairLLR a b (p a) (p b) l c y)) ∂(Bandits.bernoulliBandit p) c ≤
      1 := by
  rw [Bandits.bernoulliBandit_apply]
  by_cases hca : c = a
  · subst hca
    simpa [pairLLR, hab] using (lintegral_ofReal_exp_berLLR_bernoulliMeasure hpa l.1).le
  · by_cases hcb : c = b
    · subst hcb
      simpa [pairLLR, hca] using (lintegral_ofReal_exp_berLLR_bernoulliMeasure hpb l.2).le
    · simp [pairLLR, hca, hcb]

/-- The sum of the log-likelihood ratios `berLLR q r` of the observations of the arm `c`, with
`j` ones among its `N` observations, is `j log (q / r) + (N - j) log ((1 - q) / (1 - r))` for
`q ∈ (0, 1)`, and `0` otherwise. -/
private lemma sum_ite_berLLR {c : α} {n : ℕ} {ω : Ω} {j : ℕ} (hj : j ≤ pullCount A c n ω)
    (hS : sumRewards A Y c n ω = j) (q r : ℝ) :
    ∑ k ∈ range n, (if A k ω = c then berLLR q r (Y k ω) else 0) =
      if q ∈ Set.Ioo 0 1 then (j : ℝ) * log (q / r) +
        ((pullCount A c n ω - j : ℕ) : ℝ) * log ((1 - q) / (1 - r)) else 0 := by
  by_cases hq : q ∈ Set.Ioo 0 1
  · simp only [berLLR, hq, ↓reduceIte, sum_ite_mul_add_one_sub_mul, hS, Nat.cast_sub hj]
  · simp only [berLLR, hq, ↓reduceIte, ite_self, sum_const_zero]

/-- The last step of `measure_exists_log_two_mul_mul_lt_klBer_le`: if
`log (2 n x) < N_a d(j_a / N_a, p_a) + N_b d(j_b / N_b, p_b)` with `1 ≤ N_a + N_b ≤ n`, then the
product `Λ_a Λ_b` of the Krichevsky–Trofimov likelihood ratios of the two arms is at least `x`. -/
private lemma le_mul_of_log_two_mul_mul_lt {pa pb : ℝ} (hpa : pa ∈ Set.Ioo 0 1)
    (hpb : pb ∈ Set.Ioo 0 1) {ja jb Na Nb n : ℕ} (hja : ja ≤ Na) (hjb : jb ≤ Nb)
    (h1 : 1 ≤ Na + Nb) (hn : Na + Nb ≤ n) {x : ℝ} (hx : 0 < x)
    (hlt : log (2 * n * x) < Na * klBerReal (ja / Na) pa + Nb * klBerReal (jb / Nb) pb) :
    x ≤ (∫ u, u ^ ja * (1 - u) ^ (Na - ja) ∂betaMeasure (1 / 2) (1 / 2)) /
          (pa ^ ja * (1 - pa) ^ (Na - ja)) *
        ((∫ u, u ^ jb * (1 - u) ^ (Nb - jb) ∂betaMeasure (1 / 2) (1 / 2)) /
          (pb ^ jb * (1 - pb) ^ (Nb - jb))) := by
  set Λa := (∫ u, u ^ ja * (1 - u) ^ (Na - ja) ∂betaMeasure (1 / 2) (1 / 2)) /
    (pa ^ ja * (1 - pa) ^ (Na - ja)) with hΛa
  set Λb := (∫ u, u ^ jb * (1 - u) ^ (Nb - jb) ∂betaMeasure (1 / 2) (1 / 2)) /
    (pb ^ jb * (1 - pb) ^ (Nb - jb)) with hΛb
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1.trans hn
  have hΛa_pos : 0 < Λa := div_pos (integral_pow_mul_one_sub_pow_betaMeasure_pos
    (by norm_num) (by norm_num) _ _) (mul_pos (pow_pos hpa.1 _) (pow_pos (sub_pos.2 hpa.2) _))
  have hΛb_pos : 0 < Λb := div_pos (integral_pow_mul_one_sub_pow_betaMeasure_pos
    (by norm_num) (by norm_num) _ _) (mul_pos (pow_pos hpb.1 _) (pow_pos (sub_pos.2 hpb.2) _))
  have hw_pos : ∀ N : ℕ, 0 < (if N = 0 then (1 : ℝ) else 2 * √(N : ℝ)) := fun N ↦ by
    split_ifs with h0
    · exact one_pos
    · exact mul_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0))
  have hTa := mul_klBerReal_le_log hpa hja
  have hTb := mul_klBerReal_le_log hpb hjb
  rw [← hΛa] at hTa
  rw [← hΛb] at hTb
  -- `log (2 n x) < log (w_a Λ_a) + log (w_b Λ_b) ≤ log (2 n Λ_a Λ_b)`
  have hlog : log (2 * n * x) < log (2 * n * (Λa * Λb)) := by
    calc log (2 * n * x) < _ := hlt
      _ ≤ _ := add_le_add hTa hTb
      _ = log ((if Na = 0 then (1 : ℝ) else 2 * √(Na : ℝ)) *
          (if Nb = 0 then (1 : ℝ) else 2 * √(Nb : ℝ)) * (Λa * Λb)) := by
        rw [← log_mul (mul_pos (hw_pos Na) hΛa_pos).ne' (mul_pos (hw_pos Nb) hΛb_pos).ne']
        ring_nf
      _ ≤ _ := log_le_log (mul_pos (mul_pos (hw_pos Na) (hw_pos Nb)) (mul_pos hΛa_pos hΛb_pos))
          (mul_le_mul_of_nonneg_right (ite_mul_ite_le h1 hn) (mul_pos hΛa_pos hΛb_pos).le)
  rw [log_lt_log_iff (by positivity) (by positivity)] at hlog
  have h2n : 0 < 2 * (n : ℝ) := by positivity
  nlinarith

variable [Countable α] [MeasurableSingletonClass α] {P : Measure Ω}
  [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {p : α → I}

/-- **Pairwise deviations of Bernoulli arms** [GK16, proof of Theorem 10]. Along a run of any
algorithm against the Bernoulli bandit with means `p`, for two arms `a ≠ b` with means in `(0, 1)`
and every `x > 0`, the probability that at some round `n`
`log (2 n x) < N_a(n) d(μ̂_a(n), p_a) + N_b(n) d(μ̂_b(n), p_b)` is at most `1 / x`, where `N_c(n)`
is the number of pulls and `μ̂_c(n)` the empirical mean of the arm `c` before round `n`, and `d`
is the binary relative entropy. -/
theorem measure_exists_log_two_mul_mul_lt_klBer_le
    (h : IsAlgEnvSeq O A Y alg (Environment.bandit (Bandits.bernoulliBandit p)) P) {a b : α}
    (hab : a ≠ b) (hpa : (p a : ℝ) ∈ Set.Ioo 0 1) (hpb : (p b : ℝ) ∈ Set.Ioo 0 1) {x : ℝ}
    (hx : 0 < x) :
    P {ω | ∃ n : ℕ, ENNReal.ofReal (log (2 * n * x)) <
      (pullCount A a n ω : ℝ≥0∞) * klBer (empMean A Y a n ω) (p a) +
        (pullCount A b n ω : ℝ≥0∞) * klBer (empMean A Y b n ω) (p b)} ≤
      ENNReal.ofReal (1 / x) := by
  have := isProbabilityMeasureBeta (α := 1 / 2) (β := 1 / 2) (by norm_num) (by norm_num)
  -- Ville's inequality for the mixture over the prior `Beta(1/2, 1/2) ⊗ Beta(1/2, 1/2)` of the
  -- likelihood ratios of the bandits with means `u` and `v` on the arms `a` and `b`
  refine le_trans (measure_mono_ae ?_) (measure_exists_le_integral_exp_sum_le
    (ρ := (betaMeasure (1 / 2) (1 / 2)).prod (betaMeasure (1 / 2) (1 / 2))) h
    (measurable_pairLLR a b (p a) (p b)) (lintegral_ofReal_exp_pairLLR_le hab hpa hpb) hx)
  have hgood : ∀ᵐ ω ∂P, ∀ k, Y k ω ∈ ({0, 1} : Set ℝ) := by
    exact h.ae_forall_feedback_mem_bandit (by measurability)
      (Bandits.ae_mem_zero_one_bernoulliBandit p)
  filter_upwards [hgood] with ω hω hmem
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, ?_⟩
  -- the numbers of ones
  obtain ⟨ja, hja, hSa⟩ := exists_sumRewards_eq_natCast (A := A) a n fun k _ ↦ hω k
  obtain ⟨jb, hjb, hSb⟩ := exists_sumRewards_eq_natCast (A := A) b n fun k _ ↦ hω k
  -- the mixture is the product of the Krichevsky–Trofimov likelihood ratios
  simp_rw [pairLLR, sum_add_distrib, sum_ite_berLLR hja hSa, sum_ite_berLLR hjb hSb, exp_add]
  rw [integral_prod_mul (fun u ↦ exp (if u ∈ Set.Ioo 0 1 then (ja : ℝ) * log (u / p a) +
        ((pullCount A a n ω - ja : ℕ) : ℝ) * log ((1 - u) / (1 - p a)) else 0))
    (fun v ↦ exp (if v ∈ Set.Ioo 0 1 then (jb : ℝ) * log (v / p b) +
        ((pullCount A b n ω - jb : ℕ) : ℝ) * log ((1 - v) / (1 - p b)) else 0)),
    integral_exp_ite_betaMeasure hpa, integral_exp_ite_betaMeasure hpb]
  set Na := pullCount A a n ω
  set Nb := pullCount A b n ω
  -- the statistic in real form
  have hmean : ∀ {c : α} {j N : ℕ}, (p c : ℝ) ∈ Set.Ioo 0 1 → j ≤ N →
      empMean A Y c n ω = j / N →
      (N : ℝ≥0∞) * klBer (empMean A Y c n ω) (p c) =
        ENNReal.ofReal ((N : ℝ) * klBerReal (j / N) (p c)) := by
    intro c j N hpc hj he
    rw [he, klBer_eq_ofReal_klBerReal
      (div_mem (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hj))
      ⟨hpc.1.le, hpc.2.le⟩ (klBer_ne_top hpc), ENNReal.ofReal_mul (Nat.cast_nonneg N),
      ENNReal.ofReal_natCast]
  have hT_nonneg : ∀ {q : ℝ} {j N : ℕ}, q ∈ Set.Ioo 0 1 → j ≤ N →
      0 ≤ (N : ℝ) * klBerReal (j / N) q := fun {q j N} hq hj ↦
    mul_nonneg (Nat.cast_nonneg _) (klBerReal_nonneg_of_klBer_ne_top
      (div_mem (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hj))
      ⟨hq.1.le, hq.2.le⟩ (klBer_ne_top hq))
  rw [hmean hpa hja (by rw [empMean, hSa]), hmean hpb hjb (by rw [empMean, hSb]),
    ← ENNReal.ofReal_add (hT_nonneg hpa hja) (hT_nonneg hpb hjb),
    ENNReal.ofReal_lt_ofReal_iff'] at hn
  obtain ⟨hlt, hpos⟩ := hn
  -- at least one of the two arms was pulled, and at most `n` times in total
  have h1 : 1 ≤ Na + Nb := by
    by_contra h0
    obtain ⟨ha0, hb0⟩ : Na = 0 ∧ Nb = 0 := by omega
    rw [ha0, hb0] at hpos
    simp at hpos
  have hnab : Na + Nb ≤ n := by
    classical
    simpa [sum_pair hab] using sum_pullCount_le (A := A) {a, b} n ω
  exact le_mul_of_log_two_mul_mul_lt hpa hpb hja hjb h1 hnab hx hlt

end LMLExplore
