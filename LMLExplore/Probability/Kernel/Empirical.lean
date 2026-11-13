/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LMLExplore.MeasureTheory.Measure.Real
public import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic
public import LMLExplore.Probability.Kernel.Basic
public import LMLExplore.Probability.Moments.EmpiricalBernstein
public import LMLExplore.Probability.Moments.SubGaussian.Bounded
public import LMLExplore.Probability.Moments.SubGaussian.EmpiricalLaw
public import TauCeti.Probability.Process.EmpiricalMeasure
import LMLExplore.Probability.Moments.Bernstein

/-!
# Empirical kernels of arrays of samples

An array `ω : ℕ → α → β` holds, for every key `a : α`, a sequence of samples `ω 0 a, ω 1 a, …`.
Its empirical kernel `empiricalKernel N ω` maps each key `a` to the empirical law
`N⁻¹ ∑_{i < N} δ_{ω i a}` of its first `N` samples, Tau Ceti's empirical measure of the family
`(ω i a)_{i < N}`. For `N ≠ 0` it is a Markov kernel, and it depends measurably on the array.

Under LML's stream model `Bandits.streamMeasure ν`, the samples `ω i a` are independent with laws
`ν a`, so that `empiricalKernel N ω` estimates the kernel `ν` from `N` samples per key; this is
the generative model of a transition kernel. When the keys and the values range over finite
types, the `ℓ¹` deviation of empirical laws [WOSVW03, Theorem 2.1] and a union bound over the keys
give: for `δ > 0`, with probability at least `1 - δ`, every key `a` satisfies
`tvDist (ν a) (empiricalKernel N ω a) < √(2 (log (card α / δ) + card β log 2) / N)`.

For a single function `f` with values in `[l, u]`, Hoeffding's inequality gives the sharper
deviation of its empirical means, which does not depend on the size of `β`: for every key `a` and
`t ≥ 0`, `|∫ f d(ν a) - ∫ f d(empiricalKernel N ω a)| ≥ t` has probability at most
`2 exp (-2 N t² / (u - l)²)`. For finitely many keys and `δ > 0`, with probability at least
`1 - δ`, every key `a` satisfies
`|∫ f d(ν a) - ∫ f d(empiricalKernel N ω a)| ≤ (u - l) √(log (2 card α / δ) / (2 N))`.

The empirical Bernstein inequality [AMS09, Theorem 1] replaces the range `u - l` of `f` in the
leading term by its observed standard deviation: the variance `Var[f; empiricalKernel N ω a]` is
the biased sample variance of the values of `f` at the samples. For finitely many keys and
`δ > 0`, with probability at least `1 - δ`, every key `a` satisfies
`|∫ f d(ν a) - ∫ f d(empiricalKernel N ω a)| < √(2 V L / N) + 3 (u - l) L / N`, with
`V = Var[f; empiricalKernel N ω a]` and `L = log (3 card α / δ)`. When the variance of `f` is
small, this is much sharper than Hoeffding's bound.

Bernstein's inequality uses the variance of `f` under `ν a` instead: for `N ≠ 0` and every `x`,
`|∫ f d(ν a) - ∫ f d(empiricalKernel N ω a)|` is at least
`√(2 Var[f; ν a] x / N) + (u - l) x / (3 N)` with probability at most `2 exp (-x)`. This also
holds for a random function `W ω` with values in `[l, u]` that is independent of the samples
`(ω i a)_i` of the key `a`, as for a function computed from the samples of the other keys: for
countably many values, `N ≠ 0` and every `x`, `|∫ W ω d(ν a) - ∫ W ω d(empiricalKernel N ω a)|` is
at least `√(2 Var[W ω; ν a] x / N) + (u - l) x / (3 N)` with probability at most `2 exp (-x)`.
This is the decoupling device of [AKY20, Lemma 6].

## Main definitions

* `LMLExplore.empiricalKernel N ω`: the empirical kernel of the first `N` samples of `ω`.

## Main statements

* `LMLExplore.empiricalKernel_apply_congr`, `LMLExplore.empiricalKernel_congr`: the empirical
  kernel only depends on the first `N` samples.
* `LMLExplore.empiricalKernel_apply_of_measurableSet`,
  `LMLExplore.measureReal_empiricalKernel_apply_singleton`: the empirical kernel gives a
  measurable set the proportion of the first `N` samples that fall in it.
* `LMLExplore.integral_empiricalKernel`: integrating against the empirical kernel averages over
  the first `N` samples.
* `LMLExplore.measurable_empiricalKernel_apply`: the empirical law of a key is a measurable
  function of the array.
* `LMLExplore.le_streamMeasure_forall_tvDist_empiricalKernel_lt`: the uniform deviation in total
  variation of the empirical kernel under the stream model.
* `LMLExplore.measureReal_le_abs_integral_sub_integral_empiricalKernel_le`,
  `LMLExplore.le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_le`: Hoeffding's
  inequality for the empirical means of a bounded function, for one key and uniformly over finitely
  many keys.
* `LMLExplore.variance_empiricalKernel`: the variance under the empirical kernel is the biased
  sample variance.
* `LMLExplore.measureReal_sqrt_add_le_abs_integral_sub_integral_empiricalKernel_le`,
  `LMLExplore.le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_lt_sqrt_add`: the
  empirical Bernstein inequality for the empirical means of a bounded function, for one key and
  uniformly over finitely many keys.
* `LMLExplore.measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empiricalKernel_le`:
  Bernstein's inequality for the empirical means of a bounded function, with its variance under
  `ν a`.
* `measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empiricalKernel_le_of_indepFun`:
  Bernstein's inequality for the empirical means of a random function independent of the samples
  of the key.

## References

* [A. Agarwal, S. Kakade and L. F. Yang, *Model-based reinforcement learning with a generative
  model is minimax optimal*, COLT 2020][AKY20], Lemma 6
* [J.-Y. Audibert, R. Munos and Cs. Szepesvári, *Exploration–exploitation tradeoff using variance
  estimates in multi-armed bandits*, Theoretical Computer Science 410 (2009)][AMS09], Theorem 1
* [T. Weissman, E. Ordentlich, G. Seroussi, S. Verdú and M. J. Weinberger, *Inequalities for the
  L1 deviation of the empirical distribution*][WOSVW03]
-/

public section

open Finset MeasureTheory ProbabilityTheory Real Bandits
open scoped ENNReal

namespace LMLExplore

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]

section Countable

variable [Countable α]

/-- The empirical kernel of the first `N` samples of an array `ω : ℕ → α → β`: it maps a key `a`
to the empirical law `N⁻¹ ∑_{i < N} δ_{ω i a}` of the samples `ω 0 a, …, ω (N - 1) a`, Tau Ceti's
empirical measure of this family. It is a Markov kernel for `N ≠ 0`. -/
noncomputable def empiricalKernel (N : ℕ) (ω : ℕ → α → β) : Kernel α β :=
  Kernel.ofFunOfCountable fun a ↦
    (TauCeti.Probability.empiricalFiniteMeasure fun i : Fin N ↦ ω i a : Measure β)

lemma empiricalKernel_apply (N : ℕ) (ω : ℕ → α → β) (a : α) :
    empiricalKernel N ω a =
      (TauCeti.Probability.empiricalFiniteMeasure fun i : Fin N ↦ ω i a : Measure β) :=
  (rfl)

/-- The empirical law of a key `a` only depends on the first `N` samples of `a`. -/
lemma empiricalKernel_apply_congr {N : ℕ} {ω ω' : ℕ → α → β} {a : α}
    (h : ∀ i < N, ω i a = ω' i a) :
    empiricalKernel N ω a = empiricalKernel N ω' a := by
  simp_rw [empiricalKernel_apply]
  congr 3 with i
  rw [h i i.isLt]

/-- The empirical kernel of the first `N` samples only depends on these samples. -/
lemma empiricalKernel_congr {N : ℕ} {ω ω' : ℕ → α → β} (h : ∀ i < N, ω i = ω' i) :
    empiricalKernel N ω = empiricalKernel N ω' :=
  Kernel.ext fun _ ↦ empiricalKernel_apply_congr fun i hi ↦ by rw [h i hi]

/-- The empirical kernel gives a measurable set `s` the proportion of the first `N` samples that
fall in `s`. -/
lemma empiricalKernel_apply_of_measurableSet (N : ℕ) (ω : ℕ → α → β) (a : α) {s : Set β}
    (hs : MeasurableSet s) :
    empiricalKernel N ω a s = (N : ℝ≥0∞)⁻¹ * ∑ i ∈ range N, s.indicator 1 (ω i a) := by
  rw [empiricalKernel_apply, TauCeti.Probability.empiricalFiniteMeasure_apply hs, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range (fun i ↦ s.indicator (1 : β → ℝ≥0∞) (ω i a))]

instance (N : ℕ) [NeZero N] (ω : ℕ → α → β) : IsMarkovKernel (empiricalKernel N ω) :=
  inferInstanceAs (IsMarkovKernel (Kernel.ofFunOfCountable _))

/-- The empirical kernel gives a point `b` the proportion `#{i < N | ω i a = b} / N` of the first
`N` samples equal to `b`. -/
@[simp]
lemma measureReal_empiricalKernel_apply_singleton [MeasurableSingletonClass β] [DecidableEq β]
    (N : ℕ) (ω : ℕ → α → β) (a : α) (b : β) :
    (empiricalKernel N ω a).real {b} = (#{i ∈ range N | ω i a = b} : ℝ) / N := by
  simp [measureReal_def, empiricalKernel_apply_of_measurableSet N ω a (measurableSet_singleton b),
    Set.indicator_apply, div_eq_inv_mul]

/-- Integrating a strongly measurable function against the empirical kernel averages it over the
first `N` samples. -/
lemma integral_empiricalKernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (N : ℕ) (ω : ℕ → α → β) (a : α) {f : β → E} (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(empiricalKernel N ω a) = (N : ℝ)⁻¹ • ∑ i ∈ range N, f (ω i a) := by
  rw [empiricalKernel_apply, TauCeti.Probability.integral_empiricalFiniteMeasure hf,
    Fintype.card_fin, Fin.sum_univ_eq_sum_range (fun i ↦ f (ω i a))]

/-- The empirical law of the first `N` samples of a key is a measurable function of the array. -/
lemma measurable_empiricalKernel_apply (N : ℕ) (a : α) :
    Measurable fun ω : ℕ → α → β ↦ empiricalKernel N ω a := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp_rw [empiricalKernel_apply_of_measurableSet _ _ _ hs]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ ↦ ?_) _
  exact (measurable_one.indicator hs).comp ((measurable_pi_apply a).comp (measurable_pi_apply i))

/-- **Hoeffding's inequality for the empirical kernel.** Under the stream model `streamMeasure ν`
of a Markov kernel `ν`, let `f` be a measurable function with values in `[l, u]`
`ν a`-almost everywhere. For `t ≥ 0`, the mean of `f` over the first `N` samples of the key `a`
deviates from its mean under `ν a` by at least `t` with probability at most
`2 exp (-2 N t² / (u - l)²)`. -/
theorem measureReal_le_abs_integral_sub_integral_empiricalKernel_le (ν : Kernel α β)
    [IsMarkovKernel ν] {f : β → ℝ} (hf : Measurable f) {l u : ℝ} {a : α}
    (hfb : ∀ᵐ y ∂(ν a), f y ∈ Set.Icc l u) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (streamMeasure ν).real {ω | t ≤ |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)|} ≤
      2 * exp (-(2 * N * t ^ 2 / (u - l) ^ 2)) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact measureReal_le_one.trans (by norm_num)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  -- the samples `f (ω i a)` are independent, with values in `[l, u]` and mean `∫ f d(ν a)`
  have h_law (i : ℕ) := hasLaw_eval_eval_streamMeasure ν i a
  have h_indep : iIndepFun (fun i (ω : ℕ → α → β) ↦ f (ω i a)) (streamMeasure ν) :=
    (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ ↦ f) fun _ ↦ hf
  have h_mean (i : ℕ) : ∫ ω, f (ω i a) ∂(streamMeasure ν) = ∫ y, f y ∂(ν a) :=
    (h_law i).integral_comp hf.aestronglyMeasurable
  have h := measureReal_le_abs_sum_sub_integral_le h_indep (s := range N) (l := fun _ ↦ l)
    (u := fun _ ↦ u) (fun i _ ↦ hf.comp_aemeasurable (h_law i).aemeasurable)
    (fun i _ ↦ ae_of_ae_map (h_law i).aemeasurable ((h_law i).map_eq ▸ hfb))
    (t := N * t) (by positivity)
  simp_rw [h_mean, sum_const, card_range, nsmul_eq_mul] at h
  refine le_trans (measureReal_mono ?_) (h.trans_eq ?_)
  · intro ω (hω : t ≤ _)
    -- the centered sum is `-N` times the deviation of the empirical mean
    have h_sum : ∑ i ∈ range N, (f (ω i a) - ∫ y, f y ∂(ν a)) =
        -(N * (∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a))) := by
      rw [integral_empiricalKernel N ω a hf.stronglyMeasurable]
      simp [sum_sub_distrib]
      field_simp
      ring
    simp only [Set.mem_ofPred_eq, h_sum, abs_neg, abs_mul, abs_of_pos hN']
    exact mul_le_mul_of_nonneg_left hω hN'.le
  · rw [show 2 * (N * t) ^ 2 = N * (2 * N * t ^ 2) by ring, mul_div_mul_left _ _ hN'.ne']

/-- For `0 < δ < 1` and `m ≥ 1`, the mean of `f` over the first `N` samples of the key `a`
deviates from its mean under `ν a` by more than `(u - l) √(log (2 m / δ) / (2 N))` with
probability at most `δ / m`: by Hoeffding's inequality, or, when `l = u`, because both means are
almost surely equal to `l`. -/
private lemma measureReal_lt_abs_integral_sub_integral_empiricalKernel_le (ν : Kernel α β)
    [IsMarkovKernel ν] {f : β → ℝ} (hf : Measurable f) {l u : ℝ} {a : α}
    (hfb : ∀ᵐ y ∂(ν a), f y ∈ Set.Icc l u) (N : ℕ) [NeZero N] {δ m : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) (hm : 1 ≤ m) :
    (streamMeasure ν).real {ω | (u - l) * √(log (2 * m / δ) / (2 * N)) <
      |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)|} ≤ δ / m := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hlu : l ≤ u := by
    obtain ⟨y, hy⟩ := hfb.exists
    exact hy.1.trans hy.2
  rcases hlu.lt_or_eq with hlu | rfl
  · -- Hoeffding's inequality at the radius `r`, where `2 N r² / (u - l)² = log (2 m / δ)`
    have hlog : 0 ≤ log (2 * m / δ) / (2 * N) := by
      refine div_nonneg (log_nonneg ?_) (by positivity)
      rw [le_div_iff₀ hδ]
      linarith
    have hr : 2 * N * ((u - l) * √(log (2 * m / δ) / (2 * N))) ^ 2 / (u - l) ^ 2 =
        log (2 * m / δ) := by
      rw [mul_pow, sq_sqrt hlog]
      field_simp [(sub_pos.2 hlu).ne']
    refine le_trans (measureReal_mono fun ω (hω : _ < _) ↦ hω.le)
      ((measureReal_le_abs_integral_sub_integral_empiricalKernel_le ν hf hfb N
        (mul_nonneg (sub_pos.2 hlu).le (sqrt_nonneg _))).trans_eq ?_)
    rw [hr, exp_neg, exp_log (by positivity)]
    field_simp
  · -- for `l = u`, the samples are almost surely equal to `l`, and so are both means
    have h_const : f =ᵐ[ν a] fun _ ↦ l := by
      filter_upwards [hfb] with y hy
      exact le_antisymm hy.2 hy.1
    have h_mean : ∫ y, f y ∂(ν a) = l := by
      rw [integral_congr_ae h_const]
      simp
    have h_ae : ∀ᵐ ω ∂(streamMeasure ν), ∀ i, f (ω i a) = l := by
      refine ae_all_iff.2 fun i ↦ ?_
      have h_law := hasLaw_eval_eval_streamMeasure ν i a
      filter_upwards [ae_of_ae_map h_law.aemeasurable (h_law.map_eq ▸ hfb)] with ω hω
      exact le_antisymm hω.2 hω.1
    have h_null : streamMeasure ν {ω | (l - l) * √(log (2 * m / δ) / (2 * N)) <
        |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)|} = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [h_ae] with ω hω
      simp [integral_empiricalKernel N ω a hf.stronglyMeasurable, h_mean, hω,
        inv_mul_cancel_left₀ hN.ne']
    rw [measureReal_def, h_null, ENNReal.toReal_zero]
    positivity

/-- The variance of a measurable function `f` under the empirical kernel is the biased sample
variance `N⁻¹ ∑_{i < N} (f (ω i a) - f̂) ^ 2` of its values at the first `N` samples of the key
`a`, with `f̂ = N⁻¹ ∑_{j < N} f (ω j a)` their mean. -/
lemma variance_empiricalKernel (N : ℕ) (ω : ℕ → α → β) (a : α) {f : β → ℝ} (hf : Measurable f) :
    Var[f; empiricalKernel N ω a] =
      (∑ i ∈ range N, (f (ω i a) - (∑ j ∈ range N, f (ω j a)) / N) ^ 2) / N := by
  rw [variance_eq_integral hf.aemeasurable,
    integral_empiricalKernel N ω a ((hf.sub_const _).pow_const 2).stronglyMeasurable,
    integral_empiricalKernel N ω a hf.stronglyMeasurable]
  simp [div_eq_inv_mul]

/-- **The empirical Bernstein inequality for the empirical kernel** [AMS09, Theorem 1]. Under the
stream model `streamMeasure ν` of a Markov kernel `ν`, let `f` be a measurable function with
values in `[l, u]`, `l < u`, `ν a`-almost everywhere. For `N ≠ 0` and every `x`, the mean of `f`
over the first `N` samples of the key `a` deviates from its mean under `ν a` by at least
`√(2 V x / N) + 3 (u - l) x / N` with probability at most `3 exp (-x)`, where
`V = Var[f; empiricalKernel N ω a]` is the sample variance of `f`. -/
theorem measureReal_sqrt_add_le_abs_integral_sub_integral_empiricalKernel_le (ν : Kernel α β)
    [IsMarkovKernel ν] {f : β → ℝ} (hf : Measurable f) {l u : ℝ} (hlu : l < u) {a : α}
    (hfb : ∀ᵐ y ∂(ν a), f y ∈ Set.Icc l u) (N : ℕ) [NeZero N] (x : ℝ) :
    (streamMeasure ν).real {ω | √(2 * Var[f; empiricalKernel N ω a] * x / N) +
      3 * (u - l) * x / N ≤ |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)|} ≤
      3 * exp (-x) := by
  -- the samples `f (ω i a)` are independent, with values in `[l, u]` and mean `∫ f d(ν a)`
  have h_law (i : ℕ) := hasLaw_eval_eval_streamMeasure ν i a
  have h_indep : iIndepFun (fun i (ω : ℕ → α → β) ↦ f (ω i a)) (streamMeasure ν) :=
    (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ ↦ f) fun _ ↦ hf
  have h := h_indep.measureReal_sqrt_add_le_abs_sum_div_card_sub_le (s := range N) (x := x)
    (by simp [NeZero.ne N]) (fun i _ ↦ hf.comp_aemeasurable (h_law i).aemeasurable) hlu
    (fun i _ ↦ ae_of_ae_map (h_law i).aemeasurable ((h_law i).map_eq ▸ hfb))
    (fun i _ ↦ (h_law i).integral_comp hf.aestronglyMeasurable)
  refine le_of_eq_of_le (congrArg _ (Set.ext fun ω ↦ ?_)) h
  simp only [Set.mem_ofPred_eq, card_range, variance_empiricalKernel N ω a hf,
    integral_empiricalKernel N ω a hf.stronglyMeasurable, smul_eq_mul, inv_mul_eq_div]
  rw [abs_sub_comm]

/-- **Bernstein's inequality for the empirical kernel.** Under the stream model `streamMeasure ν`
of a Markov kernel `ν`, let `f` be a measurable function with values in `[l, u]`, `l < u`,
`ν a`-almost everywhere. For `N ≠ 0` and every `x`, the mean of `f` over the first `N` samples of
the key `a` deviates from its mean under `ν a` by at least
`√(2 Var[f; ν a] x / N) + (u - l) x / (3 N)` with probability at most `2 exp (-x)`. -/
theorem measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empiricalKernel_le
    (ν : Kernel α β) [IsMarkovKernel ν] {f : β → ℝ} (hf : Measurable f) {l u : ℝ} (hlu : l < u)
    {a : α} (hfb : ∀ᵐ y ∂(ν a), f y ∈ Set.Icc l u) (N : ℕ) [NeZero N] (x : ℝ) :
    (streamMeasure ν).real {ω | √(2 * Var[f; ν a] * x / N) + (u - l) * x / (3 * N) ≤
      |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)|} ≤ 2 * exp (-x) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set m := ∫ y, f y ∂(ν a)
  have hf_int : Integrable f (ν a) := Integrable.of_mem_Icc l u hf.aemeasurable hfb
  have hm : m ∈ Set.Icc l u := by
    constructor
    · simpa using integral_mono_ae (integrable_const l) hf_int (hfb.mono fun y hy ↦ hy.1)
    · simpa using integral_mono_ae hf_int (integrable_const u) (hfb.mono fun y hy ↦ hy.2)
  -- the centred samples `f (ω i a) - m` are independent, with mean zero and variance `Var[f; ν a]`
  have h_law (i : ℕ) := hasLaw_eval_eval_streamMeasure ν i a
  have h_indep : iIndepFun (fun i (ω : ℕ → α → β) ↦ f (ω i a) - m) (streamMeasure ν) :=
    (iIndepFun_eval_streamMeasure'' ν a).comp (fun _ y ↦ f y - m) fun _ ↦ hf.sub_const m
  have h_mean (i : ℕ) : ∫ ω, f (ω i a) - m ∂(streamMeasure ν) = 0 := by
    refine ((h_law i).integral_comp (f := fun y ↦ f y - m)
      (hf.sub_const m).aestronglyMeasurable).trans ?_
    rw [integral_sub hf_int (integrable_const m)]
    simp [m]
  have h_sq (i : ℕ) : ∫ ω, (f (ω i a) - m) ^ 2 ∂(streamMeasure ν) = Var[f; ν a] := by
    refine ((h_law i).integral_comp (f := fun y ↦ (f y - m) ^ 2)
      ((hf.sub_const m).pow_const 2).aestronglyMeasurable).trans ?_
    rw [variance_eq_integral hf.aemeasurable]
  have h := h_indep.measureReal_sqrt_add_le_abs_sum_le_of_abs_le (s := range N) (b := u - l)
    (v := N * Var[f; ν a]) (L := x)
    (fun i _ ↦ (hf.sub_const m).comp_aemeasurable (h_law i).aemeasurable) (fun i _ ↦ h_mean i)
    (sub_pos.2 hlu)
    (fun i _ ↦ (ae_of_ae_map (h_law i).aemeasurable ((h_law i).map_eq ▸ hfb)).mono fun ω hω ↦
      abs_le.2 ⟨by linarith [hω.1, hm.2], by linarith [hω.2, hm.1]⟩)
    (by simp [h_sq])
  refine le_trans (measureReal_mono fun ω (hω : _ ≤ _) ↦ ?_) h
  -- the centred sum is `-N` times the deviation of the empirical mean
  have h_sum : ∑ i ∈ range N, (f (ω i a) - m) =
      -(N * (m - ∫ y, f y ∂(empiricalKernel N ω a))) := by
    rw [integral_empiricalKernel N ω a hf.stronglyMeasurable]
    simp [sum_sub_distrib]
    field_simp
    ring
  have h_sqrt : √(2 * (N * Var[f; ν a]) * x) = N * √(2 * Var[f; ν a] * x / N) := by
    rw [show 2 * (N * Var[f; ν a]) * x = N ^ 2 * (2 * Var[f; ν a] * x / N) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hN.le]
  simp only [Set.mem_ofPred_eq, h_sum, abs_neg, abs_mul, abs_of_pos hN, h_sqrt]
  calc N * √(2 * Var[f; ν a] * x / N) + (u - l) * x / 3 =
        N * (√(2 * Var[f; ν a] * x / N) + (u - l) * x / (3 * N)) := by
        field_simp
    _ ≤ N * |m - ∫ y, f y ∂(empiricalKernel N ω a)| := by gcongr

/-- **Bernstein's inequality for the empirical means of a random function independent of the
samples.** Under the stream model `streamMeasure ν` with countably many values, let `W ω` be a
random function with values in `[l, u]`, `l < u`, that is independent of the samples
`(ω i a)_i` of the key `a`. For `N ≠ 0` and every `x`, the mean of `W ω` over the first `N`
samples of `a` deviates from its mean under `ν a` by at least
`√(2 Var[W ω; ν a] x / N) + (u - l) x / (3 N)` with probability at most `2 exp (-x)`.

By independence, the law of the pair (random function, samples) is a product, and the bound is
Bernstein's inequality for each fixed function. It applies to a function `W ω` computed from the
samples of the other keys: this is the decoupling of [AKY20, Lemma 6]. -/
theorem measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empiricalKernel_le_of_indepFun
    [Countable β] [MeasurableSingletonClass β] (ν : Kernel α β) [IsMarkovKernel ν]
    {W : (ℕ → α → β) → β → ℝ} (hW : Measurable W) {a : α}
    (h_indep : IndepFun W (fun ω i ↦ ω i a) (streamMeasure ν)) {l u : ℝ} (hlu : l < u)
    (hWb : ∀ ω y, W ω y ∈ Set.Icc l u) (N : ℕ) [NeZero N] (x : ℝ) :
    (streamMeasure ν).real {ω | √(2 * Var[W ω; ν a] * x / N) + (u - l) * x / (3 * N) ≤
      |∫ y, W ω y ∂(ν a) - ∫ y, W ω y ∂(empiricalKernel N ω a)|} ≤ 2 * exp (-x) := by
  set μ := streamMeasure ν
  set Z : (ℕ → α → β) → ℕ → β := fun ω i ↦ ω i a
  have hZ : Measurable Z := Measurable.of_eval fun i ↦ (measurable_pi_apply a).comp
    (measurable_pi_apply i)
  -- the bad event, as a set of pairs (bounded function, samples)
  set bad : Set ((β → ℝ) × (ℕ → β)) := {q | (∀ y, q.1 y ∈ Set.Icc l u) ∧
    √(2 * Var[q.1; ν a] * x / N) + (u - l) * x / (3 * N) ≤
      |∫ y, q.1 y ∂(ν a) - (N : ℝ)⁻¹ * ∑ i ∈ range N, q.1 (q.2 i)|}
  have h_eval : Measurable fun q : (β → ℝ) × β ↦ q.1 q.2 :=
    measurable_from_prod_countable_left fun y ↦ measurable_pi_apply y
  have h_mean : Measurable fun w : β → ℝ ↦ ∫ y, w y ∂(ν a) :=
    h_eval.stronglyMeasurable.integral_prod_right'.measurable
  have h_var : Measurable fun w : β → ℝ ↦ Var[w; ν a] := by
    have h_eq : (fun w : β → ℝ ↦ Var[w; ν a]) =
        fun w ↦ ∫ y, (w y - ∫ y', w y' ∂(ν a)) ^ 2 ∂(ν a) :=
      funext fun w ↦ variance_eq_integral (measurable_of_countable w).aemeasurable
    rw [h_eq]
    exact ((h_eval.sub (h_mean.comp measurable_fst)).pow_const 2).stronglyMeasurable
      |>.integral_prod_right'.measurable
  have h_bad : MeasurableSet bad := by
    refine (measurableSet_setOfPred.2 (Measurable.forall fun y ↦
      (measurableSet_setOfPred (p := fun q : (β → ℝ) × (ℕ → β) ↦ q.1 y ∈ Set.Icc l u)).1
        (measurableSet_Icc.preimage ((measurable_pi_apply y).comp measurable_fst)))).inter
      (measurableSet_le
        (f := fun q : (β → ℝ) × (ℕ → β) ↦ √(2 * Var[q.1; ν a] * x / N) + (u - l) * x / (3 * N))
        (g := fun q ↦ |∫ y, q.1 y ∂(ν a) - (N : ℝ)⁻¹ * ∑ i ∈ range N, q.1 (q.2 i)|) ?_ ?_)
    · exact ((((h_var.comp measurable_fst).const_mul 2).mul_const x).div_const _).sqrt.add_const _
    · refine continuous_abs.measurable.comp ((h_mean.comp measurable_fst).sub
        (Measurable.const_mul (Finset.measurable_sum _ fun i _ ↦ ?_) _))
      exact h_eval.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have h_sub : {ω | √(2 * Var[W ω; ν a] * x / N) + (u - l) * x / (3 * N) ≤
      |∫ y, W ω y ∂(ν a) - ∫ y, W ω y ∂(empiricalKernel N ω a)|} ⊆
        (fun ω ↦ (W ω, Z ω)) ⁻¹' bad := by
    intro ω hω
    refine ⟨hWb ω, ?_⟩
    simpa only [Set.mem_ofPred_eq,
      integral_empiricalKernel N ω a (measurable_of_countable (W ω)).stronglyMeasurable,
      smul_eq_mul] using hω
  -- for each fixed bounded function, the bad event has probability at most `2 exp (-x)`
  have h_sec (w : β → ℝ) : (μ.map Z) (Prod.mk w ⁻¹' bad) ≤ ENNReal.ofReal (2 * exp (-x)) := by
    rw [Measure.map_apply hZ (h_bad.preimage measurable_prodMk_left)]
    by_cases hw : ∀ y, w y ∈ Set.Icc l u
    · calc μ (Z ⁻¹' (Prod.mk w ⁻¹' bad)) ≤ μ {ω | √(2 * Var[w; ν a] * x / N) +
            (u - l) * x / (3 * N) ≤ |∫ y, w y ∂(ν a) - (N : ℝ)⁻¹ * ∑ i ∈ range N, w (ω i a)|} :=
            measure_mono fun ω hω ↦ hω.2
        _ = ENNReal.ofReal (μ.real {ω | √(2 * Var[w; ν a] * x / N) + (u - l) * x / (3 * N) ≤
            |∫ y, w y ∂(ν a) - (N : ℝ)⁻¹ * ∑ i ∈ range N, w (ω i a)|}) :=
            (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (2 * exp (-x)) := by
            have h := measureReal_sqrt_variance_add_le_abs_integral_sub_integral_empiricalKernel_le
              ν (measurable_of_countable w) hlu (a := a) (ae_of_all _ hw) N x
            simp only [smul_eq_mul,
              integral_empiricalKernel N _ a (measurable_of_countable w).stronglyMeasurable] at h
            exact ENNReal.ofReal_le_ofReal h
    · have h_empty : Z ⁻¹' (Prod.mk w ⁻¹' bad) = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω hω ↦ hw hω.1
      simp [h_empty]
  -- by independence, the law of `(W, Z)` is the product of the laws of `W` and `Z`
  have h_prod : μ ((fun ω ↦ (W ω, Z ω)) ⁻¹' bad) ≤ ENNReal.ofReal (2 * exp (-x)) := by
    rw [← Measure.map_apply (hW.prodMk hZ) h_bad,
      (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hZ.aemeasurable).1 h_indep,
      Measure.prod_apply h_bad]
    calc ∫⁻ w, (μ.map Z) (Prod.mk w ⁻¹' bad) ∂(μ.map W)
        ≤ ∫⁻ _, ENNReal.ofReal (2 * exp (-x)) ∂(μ.map W) := lintegral_mono h_sec
      _ = ENNReal.ofReal (2 * exp (-x)) := by
        rw [lintegral_const, Measure.map_apply hW MeasurableSet.univ, Set.preimage_univ,
          measure_univ, mul_one]
  exact (measureReal_mono h_sub (measure_ne_top _ _)).trans
    (ENNReal.toReal_le_of_le_ofReal (by positivity) h_prod)

end Countable

/-- **Uniform deviation of the empirical kernel in total variation.** Under the stream model
`streamMeasure ν` of a Markov kernel `ν` between finite types, for `N ≠ 0` and `δ > 0`, with
probability at least `1 - δ`, the empirical kernel of the first `N` samples satisfies
`tvDist (ν a) (empiricalKernel N ω a) < √(2 (log (card α / δ) + card β log 2) / N)` for every
key `a`. It is the `ℓ¹` deviation of empirical laws [WOSVW03, Theorem 2.1] for each key, with
confidence `δ / card α`, and a union bound over the keys. -/
theorem le_streamMeasure_forall_tvDist_empiricalKernel_lt [Fintype α] [Fintype β]
    [MeasurableSingletonClass β] (ν : Kernel α β) [IsMarkovKernel ν] (N : ℕ) [NeZero N] {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure ν).real {ω | ∀ a, tvDist (ν a) (empiricalKernel N ω a) <
      √(2 * (log (Fintype.card α / δ) + Fintype.card β * log 2) / N)} := by
  classical
  set r := √(2 * (log (Fintype.card α / δ) + Fintype.card β * log 2) / N)
  -- the total variation distance is the `ℓ¹` distance of the mass functions
  have h_tv (ω : ℕ → α → β) (a : α) : tvDist (ν a) (empiricalKernel N ω a) =
      ∑ b, |(empiricalKernel N ω a).real {b} - (ν a).real {b}| := by
    rw [tvDist_eq_sum_abs_measureReal_singleton_sub]
    exact sum_congr rfl fun b _ ↦ abs_sub_comm _ _
  -- the bad event of a key is measurable and has probability at most `δ / card α`
  set bad : α → Set (ℕ → α → β) := fun a ↦ {ω | r ≤ tvDist (ν a) (empiricalKernel N ω a)}
  have h_meas (a : α) : MeasurableSet (bad a) := by
    simp_rw [bad, h_tv, measureReal_def]
    refine measurableSet_le measurable_const (Finset.measurable_sum _ fun b _ ↦ ?_)
    have h := (Measure.measurable_coe (measurableSet_singleton b)).comp
      (measurable_empiricalKernel_apply (β := β) N a)
    exact continuous_abs.measurable.comp (h.ennreal_toReal.sub_const _)
  have h_bad (a : α) : (streamMeasure ν).real (bad a) ≤ δ / Fintype.card α := by
    have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩
    have h := le_measureReal_sum_abs_empirical_sub_lt (iIndepFun_eval_streamMeasure'' ν a)
      (s := range N) (by simp [NeZero.ne N]) (fun i _ ↦ hasLaw_eval_eval_streamMeasure ν i a)
      (div_pos hδ hα)
    have h_set : {ω : ℕ → α → β | ∑ b, |(#{i ∈ range N | ω i a = b} : ℝ) / #(range N) -
        (ν a).real {b}| < √(2 * (log (1 / (δ / Fintype.card α)) + Fintype.card β * log 2) /
          #(range N))} = (bad a)ᶜ := by
      ext ω
      simp [bad, h_tv, r]
    rw [h_set, probReal_compl_eq_one_sub (h_meas a)] at h
    linarith
  -- a union bound over the keys
  have h_eq : {ω | ∀ a, tvDist (ν a) (empiricalKernel N ω a) < r} = (⋃ a, bad a)ᶜ := by
    ext ω
    simp [bad]
  exact h_eq ▸ one_sub_le_measureReal_compl_iUnion hδ.le h_bad

/-- **Uniform Hoeffding bound for the empirical kernel.** Under the stream model `streamMeasure ν`
of a Markov kernel `ν` with finitely many keys, let `f` be a measurable function with values in
`[l, u]` `ν a`-almost everywhere for every key `a`. For `N ≠ 0` and `δ > 0`, with probability at
least `1 - δ`, the mean of `f` over the first `N` samples of every key `a` is within
`(u - l) √(log (2 card α / δ) / (2 N))` of its mean under `ν a`. It is Hoeffding's inequality
for each key, with confidence `δ / card α`, and a union bound over the keys. -/
theorem le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_le [Fintype α]
    (ν : Kernel α β) [IsMarkovKernel ν] {f : β → ℝ} (hf : Measurable f) {l u : ℝ}
    (hfb : ∀ a, ∀ᵐ y ∂(ν a), f y ∈ Set.Icc l u) (N : ℕ) [NeZero N] {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure ν).real {ω | ∀ a,
      |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)| ≤
        (u - l) * √(log (2 * Fintype.card α / δ) / (2 * N))} := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact (sub_nonpos.2 hδ1).trans measureReal_nonneg
  set r := (u - l) * √(log (2 * Fintype.card α / δ) / (2 * N))
  -- the bad event of a key has probability at most `δ / card α`
  set bad : α → Set (ℕ → α → β) :=
    fun a ↦ {ω | r < |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)|}
  have h_bad (a : α) : (streamMeasure ν).real (bad a) ≤ δ / Fintype.card α :=
    measureReal_lt_abs_integral_sub_integral_empiricalKernel_le ν hf (hfb a) N hδ hδ1
      (by exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩)
  -- a union bound over the keys
  have h_eq : {ω | ∀ a, |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)| ≤ r} =
      (⋃ a, bad a)ᶜ := by
    ext ω
    simp [bad]
  exact h_eq ▸ one_sub_le_measureReal_compl_iUnion hδ.le h_bad

/-- **Uniform empirical Bernstein bound for the empirical kernel** [AMS09, Theorem 1]. Under the
stream model `streamMeasure ν` of a Markov kernel `ν` with finitely many keys, let `f` be a
measurable function with values in `[l, u]`, `l < u`, `ν a`-almost everywhere for every key `a`.
For `N ≠ 0` and `δ > 0`, with probability at least `1 - δ`, the mean of `f` over the first `N`
samples of every key `a` is within `√(2 V L / N) + 3 (u - l) L / N` of its mean under `ν a`,
where `V = Var[f; empiricalKernel N ω a]` is the sample variance of `f` and
`L = log (3 card α / δ)`. It is the empirical Bernstein inequality for each key, with confidence
`δ / card α`, and a union bound over the keys. -/
theorem le_streamMeasure_forall_abs_integral_sub_integral_empiricalKernel_lt_sqrt_add
    [Fintype α] (ν : Kernel α β) [IsMarkovKernel ν] {f : β → ℝ} (hf : Measurable f) {l u : ℝ}
    (hlu : l < u) (hfb : ∀ a, ∀ᵐ y ∂(ν a), f y ∈ Set.Icc l u) (N : ℕ) [NeZero N] {δ : ℝ}
    (hδ : 0 < δ) :
    1 - δ ≤ (streamMeasure ν).real {ω | ∀ a,
      |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)| <
        √(2 * Var[f; empiricalKernel N ω a] * log (3 * Fintype.card α / δ) / N) +
          3 * (u - l) * log (3 * Fintype.card α / δ) / N} := by
  set L := log (3 * Fintype.card α / δ)
  -- the bad event of a key has probability at most `δ / card α`
  set bad : α → Set (ℕ → α → β) := fun a ↦ {ω |
    √(2 * Var[f; empiricalKernel N ω a] * L / N) + 3 * (u - l) * L / N ≤
      |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)|}
  have h_bad (a : α) : (streamMeasure ν).real (bad a) ≤ δ / Fintype.card α := by
    have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos_iff.2 ⟨a⟩
    refine (measureReal_sqrt_add_le_abs_integral_sub_integral_empiricalKernel_le ν hf hlu (hfb a)
      N L).trans_eq ?_
    rw [exp_neg, exp_log (by positivity)]
    field_simp
  -- a union bound over the keys
  have h_eq : {ω | ∀ a, |∫ y, f y ∂(ν a) - ∫ y, f y ∂(empiricalKernel N ω a)| <
      √(2 * Var[f; empiricalKernel N ω a] * L / N) + 3 * (u - l) * L / N} = (⋃ a, bad a)ᶜ := by
    ext ω
    simp [bad]
  exact h_eq ▸ one_sub_le_measureReal_compl_iUnion hδ.le h_bad

end LMLExplore
