/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.ArrayProbSpace
public import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic
public import LMLExplore.Probability.Kernel.Basic
public import LMLExplore.Probability.Moments.SubGaussian.EmpiricalLaw
public import TauCeti.Probability.Process.EmpiricalMeasure

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

## Main definitions

* `LMLExplore.empiricalKernel N ω`: the empirical kernel of the first `N` samples of `ω`.

## Main statements

* `LMLExplore.empiricalKernel_apply_of_measurableSet`,
  `LMLExplore.measureReal_empiricalKernel_apply_singleton`: the empirical kernel gives a
  measurable set the proportion of the first `N` samples that fall in it.
* `LMLExplore.integral_empiricalKernel`: integrating against the empirical kernel averages over
  the first `N` samples.
* `LMLExplore.measurable_empiricalKernel_apply`: the empirical law of a key is a measurable
  function of the array.
* `LMLExplore.le_streamMeasure_forall_tvDist_empiricalKernel_lt`: the uniform deviation in total
  variation of the empirical kernel under the stream model.

## References

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
  rw [h_eq, probReal_compl_eq_one_sub (MeasurableSet.iUnion h_meas)]
  have h_sum : ∑ a, (streamMeasure ν).real (bad a) ≤ δ := by
    refine (sum_le_sum fun a _ ↦ h_bad a).trans ?_
    rw [sum_const, card_univ, nsmul_eq_mul]
    rcases eq_or_ne (Fintype.card α) 0 with h | h
    · simp [h, hδ.le]
    · rw [mul_div_cancel₀ _ (by exact_mod_cast h)]
  linarith [measureReal_iUnion_fintype_le (μ := streamMeasure ν) bad]

end LMLExplore
