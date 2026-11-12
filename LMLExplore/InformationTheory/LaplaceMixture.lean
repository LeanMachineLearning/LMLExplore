/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import LMLExplore.Data.Nat.Choose.Bounds
public import LMLExplore.Probability.Martingale.LikelihoodRatio
public import LMLExplore.Probability.Martingale.Ville
public import LMLExplore.SequentialLearning.FiniteActions
public import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue
public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Time-uniform concentration of empirical distributions by the Laplace mixture

Let `ξ 0, ξ 1, …` be independent with law `ν` on a finite type `α` with `m` elements, let
`N_n(a) = #{k < n | ξ k = a}` be the counts (LML's `pullCount`) and `p̂_n` the empirical
distribution of `ξ 0, …, ξ (n - 1)` (Tau Ceti's `empiricalFiniteMeasure`). For every `δ > 0`,
`P(∃ n ≥ 1, log (1/δ) + (m - 1) log (e (1 + n / (m - 1))) ≤ n KL(p̂_n ‖ ν)) ≤ δ`
[JKMDLV20, Proposition 1].

The proof uses *Laplace's rule of succession*, the sequential predictor
`q_t(a) = (N_t(a) + 1) / (t + m)` (`LMLExplore.laplacePredictor`). Its likelihood ratio
`L_n = ∏_{t < n} q_t(ξ t) / ν{ξ t}` against `ν` is a nonnegative supermartingale with `L_0 = 1`
(`LMLExplore.supermartingale_predictorLikelihoodRatio`), so that Ville's inequality bounds by `δ`
the probability that it ever reaches `1 / δ`. The likelihood of the rule of succession is
`∏_{t < n} q_t(ξ t) = ∏ₐ N_n(a)! / (m (m + 1) ⋯ (m + n - 1))`
(`LMLExplore.prod_range_laplacePredictor`), the mixture of the likelihoods `∏_{t < n} p(ξ t)` over
the uniform law of the probability vector `p`. It is within the factor
`binom(n + m - 1, m - 1) ≤ (e (1 + n / (m - 1)))^{m - 1}` of the maximum likelihood
`∏ₐ (N_n(a) / n)^{N_n(a)} = exp (n KL(p̂_n ‖ ν)) ∏_{t < n} ν{ξ t}`, by the multinomial bound
`Nat.multinomial_mul_prod_pow_le_one`
(`LMLExplore.exp_mul_toReal_klDiv_le_mul_predictorLikelihoodRatio_laplacePredictor`).

## Main statements

* `LMLExplore.exp_mul_toReal_klDiv_empiricalFiniteMeasure`: for a finite family `x` of points
  charged by `ν`, `exp (card κ KL(p̂ ‖ ν)) = ∏ᵢ p̂{x i} / ν{x i}`.
* `LMLExplore.exp_mul_toReal_klDiv_le_mul_predictorLikelihoodRatio_laplacePredictor`:
  `exp (n KL(p̂_n ‖ ν)) ≤ (e (1 + n / (m - 1)))^{m - 1} L_n`.
* `LMLExplore.measure_exists_le_mul_klDiv_empiricalFiniteMeasure_le`: the time-uniform bound,
  for observations adapted to a filtration, each independent of the past.
* `ProbabilityTheory.iIndepFun.measure_exists_le_mul_klDiv_empiricalFiniteMeasure_le`: the
  time-uniform bound for independent observations.

## Implementation notes

[JKMDLV20, Proposition 1] states the event with a strict inequality; the event here, with `≤`,
contains it. For `m = 1` the second term of the threshold vanishes.

The time-uniform bound is adapted from `InformationTheory/KLTimeUniform.lean` of the formalization
RemyDegenne/Essakine2026Tight (commit 38bbd16f, directory `ForLMLExplore/`), which bounds the same
mixture with Stirling's formula and obtains the threshold
`log (1/δ) + (m - 1) log (n + 1) + 1 + log n / 2`.

## References

* [JKMDLV20] A. Jonsson, E. Kaufmann, P. Ménard, O. D. Domingues, E. Leurent and M. Valko,
  *Planning in Markov decision processes with gap-dependent sample complexity*, NeurIPS 2020,
  Proposition 1.
* [EV26] Y. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, 2026, Lemma 5.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning TauCeti.Probability InformationTheory
open scoped ENNReal Nat

namespace LMLExplore

variable {α Ω : Type*} [Fintype α] [DecidableEq α] {mΩ : MeasurableSpace Ω} {ξ : ℕ → Ω → α}

/-! ### Laplace's rule of succession -/

/-- **Laplace's rule of succession**: after the observations `ξ 0, …, ξ (t - 1)`, predict `a` with
probability `(N_t(a) + 1) / (t + m)`, where `N_t(a)` is the number of occurrences of `a` and `m`
the cardinality of `α`. -/
noncomputable def laplacePredictor (ξ : ℕ → Ω → α) (t : ℕ) (ω : Ω) (a : α) : ℝ :=
  (pullCount ξ a t ω + 1) / (t + Fintype.card α)

lemma laplacePredictor_def (t : ℕ) (ω : Ω) (a : α) :
    laplacePredictor ξ t ω a = (pullCount ξ a t ω + 1) / (t + Fintype.card α) :=
  (rfl)

lemma laplacePredictor_nonneg (t : ℕ) (ω : Ω) (a : α) : 0 ≤ laplacePredictor ξ t ω a := by
  rw [laplacePredictor_def]
  positivity

/-- The rule of succession predicts a probability vector. -/
lemma sum_laplacePredictor (t : ℕ) (ω : Ω) : ∑ a, laplacePredictor ξ t ω a = 1 := by
  have : Nonempty α := ⟨ξ 0 ω⟩
  have hm : (0 : ℝ) < t + Fintype.card α := by positivity
  simp_rw [laplacePredictor_def, ← sum_div, sum_add_distrib, sum_natCast_pullCount, sum_const,
    card_univ, nsmul_eq_mul, mul_one, div_self hm.ne']

/-- If `ξ s` is `ℱ (s + 1)`-measurable for every `s`, the rule of succession at time `t` is
`ℱ t`-measurable. -/
lemma measurable_laplacePredictor [MeasurableSpace α] [MeasurableSingletonClass α]
    {ℱ : Filtration ℕ mΩ} (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t)) (t : ℕ) (a : α) :
    Measurable[ℱ t] (fun ω ↦ laplacePredictor ξ t ω a) := by
  simp_rw [laplacePredictor_def, pullCount_eq_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  refine ((Finset.measurable_sum _ fun s hs ↦ Measurable.ite ?_ measurable_const
    measurable_const).add_const 1).div_const _
  exact (hξ s).mono (ℱ.mono (mem_range.1 hs)) le_rfl (measurableSet_singleton a)

/-- **The likelihood of the rule of succession**: `∏_{t < n} q_t(ξ t) = ∏ₐ N_n(a)! / m^{(n)}`,
where `m^{(n)} = m (m + 1) ⋯ (m + n - 1)` is the ascending factorial. -/
lemma prod_range_laplacePredictor (n : ℕ) (ω : Ω) :
    ∏ t ∈ range n, laplacePredictor ξ t ω (ξ t ω) =
      (∏ a, ((pullCount ξ a n ω)! : ℝ)) / (Fintype.card α).ascFactorial n := by
  simp_rw [laplacePredictor_def, prod_div_distrib, Nat.ascFactorial_eq_prod_range]
  congr 1
  · exact_mod_cast prod_range_pullCount_action_add_one n ω
  · push_cast
    exact prod_congr rfl fun t _ ↦ add_comm _ _

/-! ### The divergence of an empirical distribution -/

section Empirical

variable [MeasurableSpace α] [MeasurableSingletonClass α]

omit [Fintype α] in
/-- The mass of a point under the empirical distribution of `ξ 0, …, ξ (n - 1)` is its frequency
`N_n(a) / n`. -/
lemma measureReal_empiricalFiniteMeasure_singleton_eq_pullCount (n : ℕ) (ω : Ω) (a : α) :
    (empiricalFiniteMeasure (fun k : Fin n ↦ ξ k ω) : Measure α).real {a} =
      pullCount ξ a n ω / n := by
  have h_sum : ∑ k : Fin n, ({a} : Set α).indicator (1 : α → ℝ≥0∞) (ξ k ω) = pullCount ξ a n ω := by
    rw [pullCount_eq_sum, Nat.cast_sum,
      ← Fin.sum_univ_eq_sum_range (fun s ↦ ((if ξ s ω = a then 1 else 0 : ℕ) : ℝ≥0∞))]
    refine sum_congr rfl fun k _ ↦ ?_
    simp [Set.indicator_apply]
  rw [measureReal_def, empiricalFiniteMeasure_apply (measurableSet_singleton a), h_sum,
    ENNReal.toReal_mul, ENNReal.toReal_inv, Fintype.card_fin, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, inv_mul_eq_div]

omit [Fintype α] [DecidableEq α] in
/-- **The divergence of an empirical distribution**: for a nonempty finite family `x` of points
charged by a probability measure `ν`, with empirical distribution `p̂`,
`exp (card κ KL(p̂ ‖ ν)) = ∏ᵢ p̂{x i} / ν{x i}`. -/
theorem exp_mul_toReal_klDiv_empiricalFiniteMeasure {κ : Type*} [Fintype κ] [Nonempty κ]
    {ν : Measure α} [IsProbabilityMeasure ν] {x : κ → α} (hx : ∀ i, ν {x i} ≠ 0) :
    exp (Fintype.card κ * (klDiv (empiricalFiniteMeasure x : Measure α) ν).toReal) =
      ∏ i, (empiricalFiniteMeasure x : Measure α).real {x i} / ν.real {x i} := by
  set p : Measure α := (empiricalFiniteMeasure x : Measure α)
  have hκ : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  -- the empirical distribution only charges the points `x i`
  have hac : p ≪ ν := Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ by
    rw [empiricalFiniteMeasure_apply hs, sum_eq_zero fun i _ ↦ Set.indicator_of_notMem
      (fun hi ↦ hx i (measure_mono_null (Set.singleton_subset_iff.2 hi) hνs)) _, mul_zero]
  have hp_pos : ∀ i, 0 < p.real {x i} := fun i ↦ by
    refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
    rw [empiricalFiniteMeasure_apply (measurableSet_singleton _)]
    refine mul_ne_zero (by simp) (ne_of_gt ?_)
    refine lt_of_lt_of_le ?_ (single_le_sum (fun j _ ↦ zero_le) (mem_univ i))
    simp
  have hν_pos : ∀ i, 0 < ν.real {x i} := fun i ↦
    ENNReal.toReal_pos (hx i) (measure_ne_top _ _)
  have h_llr : ∀ i, llr p ν (x i) = log (p.real {x i} / ν.real {x i}) := fun i ↦ by
    simp only [llr_def, Measure.rnDeriv_eq_measure_singleton_div (hx i) (measure_ne_top _ _),
      ENNReal.toReal_div, measureReal_def]
  rw [toReal_klDiv_of_measure_eq hac (by simp only [p, measure_univ]),
    integral_empiricalFiniteMeasure_of_measurableSingletonClass, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hκ.ne', one_mul, exp_sum]
  exact prod_congr rfl fun i _ ↦ by
    rw [h_llr, exp_log (div_pos (hp_pos i) (hν_pos i))]

end Empirical

/-! ### The likelihood ratio of the rule of succession -/

section Ratio

variable [MeasurableSpace α] [MeasurableSingletonClass α] {ν : Measure α}

/-- **The rule of succession is within `(e (1 + n / (m - 1)))^{m - 1}` of the maximum
likelihood**: if `n ≥ 1` and `ν` charges `ξ 0, …, ξ (n - 1)`, the empirical distribution `p̂_n` of
these observations satisfies `exp (n KL(p̂_n ‖ ν)) ≤ (e (1 + n / (m - 1)))^{m - 1} L_n`, where
`L_n` is the likelihood ratio of the rule of succession against `ν` and `m` the cardinality of
`α`. -/
theorem exp_mul_toReal_klDiv_le_mul_predictorLikelihoodRatio_laplacePredictor
    [IsProbabilityMeasure ν] {n : ℕ} (hn : n ≠ 0) {ω : Ω} (hξ : ∀ k < n, ν {ξ k ω} ≠ 0) :
    exp (n * (klDiv (empiricalFiniteMeasure fun k : Fin n ↦ ξ k ω : Measure α) ν).toReal) ≤
      (exp 1 * (1 + n / (Fintype.card α - 1 : ℕ))) ^ (Fintype.card α - 1) *
        predictorLikelihoodRatio ν (laplacePredictor ξ) ξ n ω := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have : Nonempty α := ⟨ξ 0 ω⟩
  set m := Fintype.card α with hm_def
  have hm : 1 ≤ m := Fintype.card_pos
  set N : α → ℕ := fun a ↦ pullCount ξ a n ω with hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hN_sum : ∑ a, N a = n := sum_pullCount
  -- `P = ∏_{t < n} ν{ξ t} > 0`
  set P := ∏ t ∈ range n, ν.real {ξ t ω}
  have hP : 0 < P := prod_pos fun t ht ↦ ENNReal.toReal_pos (hξ t (mem_range.1 ht))
    (measure_ne_top _ _)
  -- the maximum likelihood: `exp (n KL(p̂_n ‖ ν)) P = ∏ₐ (N a / n) ^ N a`
  have h_max : exp (n * (klDiv (empiricalFiniteMeasure fun k : Fin n ↦ ξ k ω : Measure α)
      ν).toReal) = (∏ a, ((N a : ℝ) / n) ^ N a) / P := by
    have h := exp_mul_toReal_klDiv_empiricalFiniteMeasure (ν := ν)
      (x := fun k : Fin n ↦ ξ k ω) fun k ↦ hξ k k.2
    rw [Fintype.card_fin] at h
    rw [h, Fin.prod_univ_eq_prod_range (fun t ↦ (empiricalFiniteMeasure fun k : Fin n ↦ ξ k ω :
      Measure α).real {ξ t ω} / ν.real {ξ t ω}) n, prod_div_distrib]
    simp_rw [measureReal_empiricalFiniteMeasure_singleton_eq_pullCount]
    rw [← prod_pow_pullCount (A := ξ) (fun a ↦ (pullCount ξ a n ω : ℝ) / n) n ω]
  -- the likelihood of the rule of succession: `L_n P = ∏ₐ N a ! / m^{(n)}`
  have h_lap : predictorLikelihoodRatio ν (laplacePredictor ξ) ξ n ω =
      (∏ a, ((N a)! : ℝ)) / m.ascFactorial n / P := by
    rw [predictorLikelihoodRatio_def, prod_div_distrib, prod_range_laplacePredictor]
  -- the multinomial bound: `∏ₐ (N a / n) ^ N a ≤ ∏ₐ N a ! / n!`
  have h_mult : ∏ a, ((N a : ℝ) / n) ^ N a ≤ (∏ a, ((N a)! : ℝ)) / n ! := by
    have h1 := Nat.multinomial_mul_prod_pow_le_one univ N (p := fun a ↦ (N a : ℝ) / n)
      (fun a _ ↦ by positivity) (by rw [← sum_div, ← Nat.cast_sum, hN_sum, div_self hnR.ne'])
    have h2 : (∏ a, ((N a)! : ℝ)) * (Nat.multinomial univ N : ℝ) = n ! := by
      exact_mod_cast hN_sum ▸ Nat.multinomial_spec univ N
    have h3 : (0 : ℝ) < Nat.multinomial univ N := by exact_mod_cast Nat.multinomial_pos _ _
    rw [le_div_iff₀ (by positivity), ← h2]
    nlinarith [prod_nonneg fun a (_ : a ∈ univ) ↦ (Nat.cast_nonneg (N a)! : (0 : ℝ) ≤ _),
      mul_le_mul_of_nonneg_left h1 (prod_nonneg fun a (_ : a ∈ univ) ↦
        (Nat.cast_nonneg (N a)! : (0 : ℝ) ≤ _))]
  -- the binomial bound: `m^{(n)} / n! = binom(n + m - 1, m - 1) ≤ (e (1 + n / (m - 1)))^{m - 1}`
  have h_choose : (m.ascFactorial n : ℝ) / n ! ≤
      (exp 1 * (1 + n / (m - 1 : ℕ))) ^ (m - 1) := by
    rw [Nat.ascFactorial_eq_factorial_mul_choose', Nat.cast_mul, mul_div_cancel_left₀ _
      (by positivity), show m + n - 1 = (m - 1) + n by omega, ← Nat.choose_symm_add]
    refine (Nat.choose_le_exp_one_mul_div_pow _ _).trans_eq ?_
    rcases Nat.eq_zero_or_pos (m - 1) with h0 | h0
    · simp [h0]
    · have : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast h0
      congr 1
      push_cast
      field_simp
  rw [h_max, h_lap]
  have h_asc : (0 : ℝ) < m.ascFactorial n := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    rw [hk, add_comm]
    exact_mod_cast Nat.ascFactorial_pos k n
  rw [div_le_iff₀ hP, mul_div_assoc', div_mul_cancel₀ _ hP.ne']
  calc ∏ a, ((N a : ℝ) / n) ^ N a ≤ (∏ a, ((N a)! : ℝ)) / n ! := h_mult
    _ = (m.ascFactorial n : ℝ) / n ! * ((∏ a, ((N a)! : ℝ)) / m.ascFactorial n) := by
        field_simp
    _ ≤ _ := by gcongr

/-- On the deviation event, the likelihood ratio of the rule of succession is at least `1 / δ`. -/
private lemma one_div_le_predictorLikelihoodRatio [IsProbabilityMeasure ν] {n : ℕ} (hn : n ≠ 0)
    {ω : Ω} (hξ : ∀ k < n, ν {ξ k ω} ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (h : ENNReal.ofReal (log (1 / δ) + ((Fintype.card α : ℝ) - 1) *
        log (exp 1 * (1 + n / ((Fintype.card α : ℝ) - 1)))) ≤
      n * klDiv (empiricalFiniteMeasure fun k : Fin n ↦ ξ k ω : Measure α) ν) :
    1 / δ ≤ predictorLikelihoodRatio ν (laplacePredictor ξ) ξ n ω := by
  have : Nonempty α := ⟨ξ 0 ω⟩
  set p : Measure α := (empiricalFiniteMeasure fun k : Fin n ↦ ξ k ω : Measure α)
  have hm : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  set C := (exp 1 * (1 + n / (Fintype.card α - 1 : ℕ))) ^ (Fintype.card α - 1) with hC
  have hC_pos : 0 < C := by positivity
  -- the divergence is finite, since `p̂_n` is absolutely continuous with respect to `ν`
  have hKL : klDiv p ν ≠ ∞ := by
    refine klDiv_ne_top (Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_) Integrable.of_finite
    rw [empiricalFiniteMeasure_apply hs, sum_eq_zero fun (i : Fin n) _ ↦ Set.indicator_of_notMem
      (fun hi ↦ hξ i i.2 (measure_mono_null (Set.singleton_subset_iff.2 hi) hνs)) _, mul_zero]
  have h_le : log (1 / δ) + log C ≤ n * (klDiv p ν).toReal := by
    rw [← ENNReal.ofReal_toReal hKL, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by simp),
      ENNReal.ofReal_le_ofReal_iff'] at h
    rw [hC, log_pow, hm]
    rcases h with h | h
    · exact h
    · exact h.trans (by positivity)
  have h_exp := (exp_le_exp.2 h_le).trans
    (exp_mul_toReal_klDiv_le_mul_predictorLikelihoodRatio_laplacePredictor hn hξ)
  rw [exp_add, exp_log (by positivity), exp_log hC_pos, mul_comm] at h_exp
  exact le_of_mul_le_mul_left h_exp hC_pos

end Ratio

/-! ### Time-uniform concentration -/

variable [MeasurableSpace α] [MeasurableSingletonClass α] {ν : Measure α} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [DecidableEq α] in
/-- **Time-uniform concentration of the empirical distribution**, for observations adapted to a
filtration [JKMDLV20, Proposition 1]: if `ξ t` is `ℱ (t + 1)`-measurable, independent of `ℱ t`
and of law `ν` on a finite type with `m` elements, then for every `δ > 0`, the probability that
`log (1/δ) + (m - 1) log (e (1 + n / (m - 1))) ≤ n KL(p̂_n ‖ ν)` for some `n ≥ 1` is at most `δ`,
where `p̂_n` is the empirical distribution of `ξ 0, …, ξ (n - 1)`. -/
theorem measure_exists_le_mul_klDiv_empiricalFiniteMeasure_le {ℱ : Filtration ℕ mΩ}
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (ξ t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (ξ t) ν μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal (log (1 / δ) + ((Fintype.card α : ℝ) - 1) *
        log (exp 1 * (1 + n / ((Fintype.card α : ℝ) - 1)))) ≤
      n * klDiv (empiricalFiniteMeasure fun k : Fin n ↦ ξ k ω : Measure α) ν} ≤
      ENNReal.ofReal δ := by
  classical
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have h_ville := (supermartingale_predictorLikelihoodRatio hξ hind hlaw
    (measurable_laplacePredictor hξ) laplacePredictor_nonneg
    fun t ω ↦ (sum_laplacePredictor t ω).le).measure_exists_le_le
    (fun n ↦ ae_of_all _ (predictorLikelihoodRatio_nonneg laplacePredictor_nonneg n))
    (one_div_pos.2 hδ)
  simp only [predictorLikelihoodRatio_zero, integral_const, probReal_univ, smul_eq_mul, mul_one,
    one_div_one_div] at h_ville
  refine (measure_mono_ae ?_).trans h_ville
  -- almost surely, `ν` charges every observation
  have h_ae : ∀ᵐ ω ∂μ, ∀ k, ν {ξ k ω} ≠ 0 := by
    rw [ae_all_iff]
    intro k
    have hν : ∀ᵐ a ∂ν, ν {a} ≠ 0 := by
      rw [ae_iff, ← Set.biUnion_of_singleton {a | ¬ν {a} ≠ 0},
        measure_biUnion_null_iff (Set.to_countable _)]
      exact fun a ha ↦ not_not.1 ha
    exact ae_of_ae_map (hlaw k).aemeasurable (by rw [(hlaw k).map_eq]; exact hν)
  filter_upwards [h_ae] with ω hω ⟨n, hn, h⟩
  exact ⟨n, one_div_le_predictorLikelihoodRatio hn.ne' (fun k _ ↦ hω k) hδ h⟩

omit [DecidableEq α] in
/-- **Time-uniform concentration of the empirical distribution** of independent observations
[JKMDLV20, Proposition 1]: if `ξ 0, ξ 1, …` are independent with law `ν` on a finite type with `m`
elements, then for every `δ > 0`, the probability that
`log (1/δ) + (m - 1) log (e (1 + n / (m - 1))) ≤ n KL(p̂_n ‖ ν)` for some `n ≥ 1` is at most `δ`,
where `p̂_n` is the empirical distribution of `ξ 0, …, ξ (n - 1)`. -/
theorem _root_.ProbabilityTheory.iIndepFun.measure_exists_le_mul_klDiv_empiricalFiniteMeasure_le
    (h_indep : iIndepFun ξ μ) (hlaw : ∀ t, HasLaw (ξ t) ν μ) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal (log (1 / δ) + ((Fintype.card α : ℝ) - 1) *
        log (exp 1 * (1 + n / ((Fintype.card α : ℝ) - 1)))) ≤
      n * klDiv (empiricalFiniteMeasure fun k : Fin n ↦ ξ k ω : Measure α) ν} ≤
      ENNReal.ofReal δ := by
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  -- transfer to the coordinates of `ν^{⊗ℕ}`
  set P : Measure (ℕ → α) := Measure.infinitePi fun _ ↦ ν
  have h_meas : AEMeasurable (fun ω k ↦ ξ k ω) μ :=
    aemeasurable_pi_iff.2 fun k ↦ (hlaw k).aemeasurable
  set E : Set (ℕ → α) := {x | ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal (log (1 / δ) +
    ((Fintype.card α : ℝ) - 1) * log (exp 1 * (1 + n / ((Fintype.card α : ℝ) - 1)))) ≤
      n * klDiv (empiricalFiniteMeasure fun k : Fin n ↦ x k : Measure α) ν}
  have h_map := Measure.le_map_apply h_meas E
  rw [(h_indep.hasLaw_infinitePi hlaw h_meas).map_eq] at h_map
  refine h_map.trans ?_
  -- the filtration generated by the coordinates of index `k < n`
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (ℕ → α)) :=
    { seq n := ⨆ k < n, MeasurableSpace.comap (fun x : ℕ → α ↦ x k) inferInstance
      mono' _ _ hij := biSup_mono fun _ hk ↦ lt_of_lt_of_le hk hij
      le' _ := iSup₂_le fun k _ ↦ (measurable_pi_apply k).comap_le }
  have hY : ∀ n, Measurable[ℱ (n + 1)] (fun x : ℕ → α ↦ x n) := fun n ↦
    (comap_measurable _).mono (le_iSup₂ (f := fun k (_ : k < n + 1) ↦
      MeasurableSpace.comap (fun x : ℕ → α ↦ x k) inferInstance) n n.lt_succ_self) le_rfl
  have h_iIndep : iIndep (fun k ↦ MeasurableSpace.comap (fun x : ℕ → α ↦ x k) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_infinitePi (X := fun _ ↦ id) fun _ ↦ measurable_id)
  have hind : ∀ n, Indep (MeasurableSpace.comap (fun x : ℕ → α ↦ x n) inferInstance) (ℱ n) P :=
    fun n ↦ by
      have h := indep_iSup_of_disjoint (fun k ↦ (measurable_pi_apply k).comap_le) h_iIndep
        (S := {n}) (T := Set.Iio n) (by simp)
      simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left, Set.mem_Iio] using h
  exact LMLExplore.measure_exists_le_mul_klDiv_empiricalFiniteMeasure_le
    (ξ := fun k (x : ℕ → α) ↦ x k) hY hind
    (fun n ↦ (measurePreserving_eval_infinitePi (fun _ ↦ ν) n).hasLaw) hδ

end LMLExplore
