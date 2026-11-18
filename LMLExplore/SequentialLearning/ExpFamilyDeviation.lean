/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.Probability.Distributions.ExponentialFamily.Chernoff
public import LMLExplore.Probability.Distributions.ExponentialFamily.RateFunction
public import LMLExplore.SequentialLearning.RateFunctionDeviation
public import LMLExplore.SequentialLearning.SelfNormalizedDeviation
public import LMLExplore.SequentialLearning.SumRewards

/-!
# Deviations of empirical means for rewards dominated by an exponential family

Let the rewards of arm `a` of a stochastic environment `Environment.bandit ν` be dominated on
`Set.univ` by the member of mean `μ` of the exponential family of a measure `ρ` and a statistic `T`,
with divergence `d` in the mean parametrization. This file bounds the deviations of the empirical
mean of `a`: first for the first `s` rewards in the reward stream model `streamMeasure ν`, by the
Cramér–Chernoff bounds of `ExponentialFamily/Chernoff.lean`, then in a run of any algorithm, at all
rounds simultaneously, through the transfer of `SequentialLearning/SumRewards.lean`. Nothing here
depends on how the algorithm chooses its actions, so the bounds apply to the sampling rules of
identification algorithms as well as to the policies of regret minimization.

For several arms at once, if the rewards of each arm `a` are dominated by the member of mean `μ_a`
of an exponential family `(ρ_a, T_a)`, the rate function of the arm is at least the extended
divergence `dbar_a(·, μ_a)` of the family (`MeasureTheory.Measure.expFamilyRate`), so the bound of
`SequentialLearning/RateFunctionDeviation.lean` for the rate functions holds for the generalized
likelihood ratio statistic `∑ a ∈ S, N_a dbar_a(μ̂_a, μ_a)` of the empirical means of the arms
of any set `S`, including at empirical means on the boundary of the means of the families, such
as the empirical means `0` and `1` of Bernoulli rewards. This is the deviation inequality behind
the `δ`-correctness of generalized likelihood ratio stopping rules for exponential families
[GK16, Proposition 12; LS, Lemma 33.7]. The same holds for the peeled bound of
`SequentialLearning/RateFunctionDeviation.lean`, whose thresholds grow like `η log₂ t` per arm
for any `η > 0`, and for the self-normalized deviations of the arms of `S` up to a horizon of
`SequentialLearning/SelfNormalizedDeviation.lean` [DKM19, Lemmas 5 and 6].
The peeled bound is adapted from the formalization in the Garivier2016Optimal project
(Rémy Degenne, <https://github.com/RemyDegenne/Garivier2016Optimal>, file
`Garivier2016Optimal/ForLMLExplore/SequentialLearning/ExpFamilyDeviation.lean`).

## Main statements

* `streamMeasure_sum_ge_le_exp_expFamilyDiv`, `streamMeasure_sum_le_le_exp_expFamilyDiv`: the
  Cramér–Chernoff bounds for the first `s` rewards of an arm in the reward stream model.
* `measure_exists_le_pullCount_and_empMean_notMem_Ioo_le`: in a run of any algorithm, the
  probability that, at some round, arm `a` has at least `m` pulls and an empirical mean outside
  `(l, u)` is at most
  `exp (-m d(u, μ)) / (1 - exp (-d(u, μ))) + exp (-m d(l, μ)) / (1 - exp (-d(l, μ)))`.
* `LMLExplore.measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le`: in a run of
  any algorithm, `P(∃ t, #S log (2 t (t + 1)) + x ≤ ∑ a ∈ S, N_a(t) dbar_a(μ̂_a(t), μ_a))` is at
  most `(x / #S) ^ #S exp (#S - x)` for `x ≥ #S`, for rewards dominated by members of exponential
  families.
* `LMLExplore.measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_expFamilyRate_le`: the
  peeled form
  `P(∃ t, 2 (#S (η log₂ t + κ_η) + x) ≤ ∑ a ∈ S, N_a(t) dbar_a(μ̂_a(t), μ_a)) ≤
  (x / #S) ^ #S exp (#S - x)` for `η > 0` and `x ≥ #S`, with `κ_η = log (2 / (1 - exp (-η)))`.
* `LMLExplore.measure_exists_mem_exists_le_pullCount_mul_expFamilyRate_le` [DKM19, Lemma 5]: in a
  run of any algorithm, the probability that some arm `a ∈ S` has
  `x ≤ N_a(t) dbar_a(μ̂_a(t), μ_a)` at some round `t ≤ n` is at most
  `2 e #S (x log n + 1) exp (-x)`, for rewards dominated by members of exponential families.
* `LMLExplore.measure_exists_mem_exists_subLogInv_le_pullCount_mul_expFamilyRate_le`,
  `LMLExplore.tsum_measure_exists_mem_exists_subLogInv_le_pullCount_mul_expFamilyRate_le`
  [DKM19, Lemma 6]: at the level `h⁻¹((1 + c) log n)`, with `h(u) = u - log u`, the bound
  `2 e #S (log n / n ^ (1 + c) + 1 / n ^ (1 + c))`, and for `c > 0` the sum of these probabilities
  over the horizons `n` is at most `2 e #S (2 + 1 / c + 1 / c²)`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Appendix B (Lemmas 5 and 6), arXiv:1906.10431.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section ExpFamilyStream

variable {α 𝓧 : Type*} [MeasurableSpace α] {m𝓧 : MeasurableSpace 𝓧} {ν : Kernel α ℝ}
  [IsMarkovKernel ν] {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {a : α} {μ x : ℝ}

/-- **Cramér–Chernoff bound in the reward stream, upper tail.** If the rewards of arm `a` are
dominated on `Set.Ici 0` by the member of mean `μ` of the exponential family of `ρ` and `T`, then
for a mean `x ≥ μ` of the family, the sum of the first `s` rewards of `a` in the reward stream
model is at least `s x` with probability at most `exp (-(s d(x, μ)))`. -/
theorem streamMeasure_sum_ge_le_exp_expFamilyDiv
    (hν : MGFDominatedOn id (ν a) T (ρ.expFamily T (ρ.natParam T μ)) (Set.Ici 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hμx : μ ≤ x) (s : ℕ) :
    streamMeasure ν {ω | s * x ≤ ∑ i ∈ range s, ω i a} ≤
      ENNReal.ofReal (exp (-(s * ρ.expFamilyDiv T x μ))) := by
  have h := (iIndepFun_eval_streamMeasure'' ν a).measureReal_sum_ge_le_exp_expFamilyDiv
    (s := range s)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedOn.trans hν) hμ hx hμx
  rw [card_range] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- **Cramér–Chernoff bound in the reward stream, lower tail.** If the rewards of arm `a` are
dominated on `Set.Iic 0` by the member of mean `μ` of the exponential family of `ρ` and `T`, then
for a mean `x ≤ μ` of the family, the sum of the first `s` rewards of `a` in the reward stream
model is at most `s x` with probability at most `exp (-(s d(x, μ)))`. -/
theorem streamMeasure_sum_le_le_exp_expFamilyDiv
    (hν : MGFDominatedOn id (ν a) T (ρ.expFamily T (ρ.natParam T μ)) (Set.Iic 0))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hxμ : x ≤ μ) (s : ℕ) :
    streamMeasure ν {ω | ∑ i ∈ range s, ω i a ≤ s * x} ≤
      ENNReal.ofReal (exp (-(s * ρ.expFamilyDiv T x μ))) := by
  have h := (iIndepFun_eval_streamMeasure'' ν a).measureReal_sum_le_le_exp_expFamilyDiv
    (s := range s)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedOn.trans hν) hμ hx hxμ
  rw [card_range] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

end ExpFamilyStream

section ExpFamilyRuns

variable {α 𝓧 : Type*} [DecidableEq α] [MeasurableSpace α] [Countable α]
  [MeasurableSingletonClass α] {m𝓧 : MeasurableSpace 𝓧} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {alg : Algorithm Unit α ℝ} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {R : ℕ → Ω → ℝ} {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {a : α} {μ l u : ℝ}

/-- **Deviations of the empirical mean of an arm with at least `m` pulls.** In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, let the rewards of arm `a` be
dominated on `Set.univ` by the member of mean `μ` of the exponential family of `ρ` and `T`, with
divergence `d`, and let `l < μ < u` be means of the family. The probability that, at some round, `a`
has at least `m` pulls and an empirical mean outside `(l, u)` is at most
`exp (-m d(u, μ)) / (1 - exp (-d(u, μ))) + exp (-m d(l, μ)) / (1 - exp (-d(l, μ)))`. -/
theorem measure_exists_le_pullCount_and_empMean_notMem_Ioo_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (hν : MGFDominatedOn id (ν a) T (ρ.expFamily T (ρ.natParam T μ)) Set.univ)
    (hμ : μ ∈ ρ.expFamilyMeans T) (hl : l ∈ ρ.expFamilyMeans T) (hu : u ∈ ρ.expFamilyMeans T)
    (hlμ : l < μ) (hμu : μ < u) (m : ℕ) :
    P {ω | ∃ t, m ≤ pullCount A a t ω ∧ empMean A R a t ω ∉ Set.Ioo l u} ≤
      ENNReal.ofReal (exp (-(m * ρ.expFamilyDiv T u μ)) / (1 - exp (-ρ.expFamilyDiv T u μ)) +
        exp (-(m * ρ.expFamilyDiv T l μ)) / (1 - exp (-ρ.expFamilyDiv T l μ))) := by
  have hdu : 0 < ρ.expFamilyDiv T u μ := Measure.expFamilyDiv_pos hu hμ hμu.ne'
  have hdl : 0 < ρ.expFamilyDiv T l μ := Measure.expFamilyDiv_pos hl hμ hlμ.ne
  calc P {ω | ∃ t, m ≤ pullCount A a t ω ∧ empMean A R a t ω ∉ Set.Ioo l u}
  _ ≤ P {ω | ∃ t, m ≤ pullCount A a t ω ∧ (sumRewards A R a t ω ≤ pullCount A a t ω * l ∨
      pullCount A a t ω * u ≤ sumRewards A R a t ω)} :=
    measure_mono fun ω ⟨t, hm, ht⟩ ↦
      ⟨t, hm, sumRewards_le_mul_or_mul_le_sumRewards_of_empMean_notMem_Ioo ht⟩
  _ ≤ streamMeasure ν {ω | ∃ s : ℕ, m ≤ s ∧
      (∑ i ∈ range s, ω i a ≤ s * l ∨ s * u ≤ ∑ i ∈ range s, ω i a)} :=
    measure_exists_pullCount_sumRewards_le h a fun s y ↦ m ≤ s ∧ (y ≤ s * l ∨ s * u ≤ y)
  -- A union bound over the numbers of pulls `s = k + m`, and the Cramér–Chernoff bounds.
  _ ≤ ∑' k : ℕ, streamMeasure ν ({ω | ∑ i ∈ range (k + m), ω i a ≤ (k + m : ℕ) * l} ∪
      {ω | (k + m : ℕ) * u ≤ ∑ i ∈ range (k + m), ω i a}) := by
    refine le_trans (measure_mono fun ω hω ↦ ?_) (measure_iUnion_le _)
    obtain ⟨s, hms, hs⟩ := hω
    refine Set.mem_iUnion.2 ⟨s - m, ?_⟩
    rwa [Nat.sub_add_cancel hms]
  _ ≤ ∑' k : ℕ, (ENNReal.ofReal (exp (-((k + m : ℕ) * ρ.expFamilyDiv T u μ))) +
      ENNReal.ofReal (exp (-((k + m : ℕ) * ρ.expFamilyDiv T l μ)))) := by
    refine tsum_le_tsum fun k ↦ (measure_union_le _ _).trans ?_
    have h_lower := streamMeasure_sum_le_le_exp_expFamilyDiv (hν.mono (Set.subset_univ _)) hμ hl
      hlμ.le (k + m)
    have h_upper := streamMeasure_sum_ge_le_exp_expFamilyDiv (hν.mono (Set.subset_univ _)) hμ hu
      hμu.le (k + m)
    exact (add_le_add h_lower h_upper).trans_eq (add_comm _ _)
  _ = _ := by
    have h_tsum {d : ℝ} (hd : 0 < d) : ∑' k : ℕ, ENNReal.ofReal (exp (-((k + m : ℕ) * d))) =
        ENNReal.ofReal (exp (-(m * d)) / (1 - exp (-d))) := by
      push_cast
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (exp_pos _).le)
        (hasSum_exp_neg_add_mul hd m).summable, (hasSum_exp_neg_add_mul hd m).tsum_eq]
    rw [tsum_add, h_tsum hdu, h_tsum hdl,
      ENNReal.ofReal_add (exp_neg_mul_div_one_sub_exp_neg_nonneg hdu.le m)
        (exp_neg_mul_div_one_sub_exp_neg_nonneg hdl.le m)]

end ExpFamilyRuns

section ExpFamilyRate

variable {α : Type*} [DecidableEq α] [Countable α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {alg : Algorithm Unit α ℝ} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {R : ℕ → Ω → ℝ} {x : ℝ}

omit [Countable α] [MeasurableSingletonClass α] [IsProbabilityMeasure P] in
/-- **From the rate functions to the extended divergences of exponential families.** Let the
rewards of each arm `a ∈ S` be dominated on `Set.univ`, in moment generating function, by the
member of mean `μ a` of the exponential family `(ρ a, T a)`. Any bound, valid for integrable
rewards, on the probability that `θ t ≤ ∑ a ∈ S, N_a(t) I_a(μ̂_a(t))` at some round `t` also
bounds the probability that `θ t ≤ ∑ a ∈ S, N_a(t) dbar_a(μ̂_a(t), μ a)` at some round `t`. -/
private lemma measure_exists_le_sum_pullCount_mul_expFamilyRate_le_of {𝓧 : Type*}
    {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ} (S : Finset α)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (θ : ℕ → ℝ) {B : ENNReal}
    (hB : (∀ a ∈ S, Integrable id (ν a)) → P {ω | ∃ t : ℕ, ENNReal.ofReal (θ t) ≤
      ∑ a ∈ S, pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} ≤ B) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (θ t) ≤
      ∑ a ∈ S, pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤ B := by
  -- the rewards are integrable, and the rate function of each arm is at least `dbar_a(·, μ a)`
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (hB fun a ha ↦ (hν a ha).integrable_of_mem_expFamilyMeans (hμ a ha))
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ht.trans (sum_le_sum fun a ha ↦ ?_)⟩
  gcongr
  exact (hν a ha).expFamilyRate_le_rateFunction _

/-- **Time-uniform deviations of the empirical means along a run, for rewards dominated by
exponential families** ([GK16, Proposition 12], [LS, Lemma 33.7]), for the arms of a set `S`. In a
run of any algorithm against `Environment.bandit ν`, let the rewards of each arm `a ∈ S` be
dominated on `Set.univ`, in moment generating function, by the member of mean `μ a` of the
exponential family `(ρ a, T a)`, with extended divergence `dbar_a`
(`MeasureTheory.Measure.expFamilyRate`). Then for `x ≥ #S`, the probability that at some round
`t`, the pull counts `N_a(t)` and the empirical means `μ̂_a(t)` satisfy
`#S log (2 t (t + 1)) + x ≤ ∑ a ∈ S, N_a(t) dbar_a(μ̂_a(t), μ a)`, is at most
`(x / #S) ^ #S exp (#S - x)`. -/
theorem measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ} (S : Finset α)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hx : #S ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (#S * log (2 * t * (t + 1)) + x) ≤
        ∑ a ∈ S, pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) :=
  measure_exists_le_sum_pullCount_mul_expFamilyRate_le_of S hμ hν
    (fun t : ℕ ↦ #S * log (2 * t * (t + 1)) + x) fun h_int ↦
      measure_exists_card_mul_log_add_le_sum_pullCount_mul_rateFunction_le h S h_int hx

/-- **Peeled time-uniform deviations of the empirical means along a run, for rewards dominated by
exponential families** (the deviation inequality of [GK16, Proposition 12] for the thresholds
`log (C t ^ p / δ)`), for the arms of a set `S`. In a run of any algorithm against
`Environment.bandit ν`, let the rewards of each arm `a ∈ S` be dominated on `Set.univ`, in moment
generating function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, with
extended divergence `dbar_a` (`MeasureTheory.Measure.expFamilyRate`). Then for `η > 0` and
`x ≥ #S`, the probability that at some round `t`, the pull counts `N_a(t)` and the empirical means
`μ̂_a(t)` satisfy
`2 (#S (η log₂ t + log (2 / (1 - exp (-η)))) + x) ≤ ∑ a ∈ S, N_a(t) dbar_a(μ̂_a(t), μ a)`, with
`log₂ t = Nat.log 2 t`, is at most `(x / #S) ^ #S exp (#S - x)`. -/
theorem measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_expFamilyRate_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ} (S : Finset α)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    {η : ℝ} (hη : 0 < η) (hx : #S ≤ x) :
    P {ω | ∃ t : ℕ, ENNReal.ofReal (2 * (#S *
        (η * Nat.log 2 t + log (2 / (1 - exp (-η)))) + x)) ≤
        ∑ a ∈ S, pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) :=
  measure_exists_le_sum_pullCount_mul_expFamilyRate_le_of S hμ hν
    (fun t : ℕ ↦ 2 * (#S * (η * Nat.log 2 t + log (2 / (1 - exp (-η)))) + x)) fun h_int ↦
      measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_rateFunction_le h S h_int hη hx

/-! ### Self-normalized deviations up to a horizon -/

omit [Countable α] [MeasurableSingletonClass α] in
/-- If the rewards of each arm `a ∈ S` are dominated on `Set.univ` by the member of mean `μ a` of
the exponential family `(ρ a, T a)`, then the event that some arm of `S` has
`θ ≤ N_a(t) dbar_a(μ̂_a(t), μ a)` at some round `t ≤ n` is contained in the event that some arm of
`S` has `θ ≤ N_a(t) I_a(μ̂_a(t))` at some round `t ≤ n`. -/
private lemma setOf_exists_mem_exists_le_pullCount_mul_expFamilyRate_subset {𝓧 : Type*}
    {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ} (S : Finset α)
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ) (θ : ENNReal) (n : ℕ) :
    {ω | ∃ a ∈ S, ∃ t ≤ n, θ ≤
        pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ⊆
      {ω | ∃ a ∈ S, ∃ t ≤ n, θ ≤
        pullCount A a t ω * rateFunction id (ν a) (empMean A R a t ω)} :=
  fun _ ⟨a, ha, t, ht, hle⟩ ↦ ⟨a, ha, t, ht,
    hle.trans (by gcongr; exact (hν a ha).expFamilyRate_le_rateFunction _)⟩

/-- **Self-normalized deviations of the arms of a set along a run, up to a horizon, for exponential
families** [DKM19, Lemma 5]. In a run of any algorithm against `Environment.bandit ν`, let the
rewards of each arm `a ∈ S` be dominated on `Set.univ`, in moment generating function, by the
member of mean `μ a` of the exponential family `(ρ a, T a)`, with extended divergence `dbar_a`
(`MeasureTheory.Measure.expFamilyRate`). Then for `x > 0` and every horizon `n`, the probability
that some arm `a ∈ S` has `x ≤ N_a(t) dbar_a(μ̂_a(t), μ a)` at some round `t ≤ n` is at most
`2 e #S (x log n + 1) exp (-x)`. -/
theorem measure_exists_mem_exists_le_pullCount_mul_expFamilyRate_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ} (S : Finset α)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ) (hx : 0 < x) (n : ℕ) :
    P {ω | ∃ a ∈ S, ∃ t ≤ n, ENNReal.ofReal x ≤
        pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤
      ENNReal.ofReal (2 * exp 1 * #S * (x * log n + 1) * exp (-x)) :=
  (measure_mono (setOf_exists_mem_exists_le_pullCount_mul_expFamilyRate_subset S hν _ n)).trans
    (measure_exists_mem_exists_le_pullCount_mul_rateFunction_le h S
      (fun a ha ↦ (hν a ha).integrable_of_mem_expFamilyMeans (hμ a ha)) hx n)

/-- **The concentration events of [DKM19, Lemma 6] for exponential families, at one horizon.** In
a run of any algorithm against `Environment.bandit ν`, let the rewards of each arm `a ∈ S` be
dominated on `Set.univ`, in moment generating function, by the member of mean `μ a` of the
exponential family `(ρ a, T a)`, with extended divergence `dbar_a`
(`MeasureTheory.Measure.expFamilyRate`). Then for every real `c` and every horizon `n`, the
probability that some arm `a ∈ S` has `h⁻¹((1 + c) log n) ≤ N_a(t) dbar_a(μ̂_a(t), μ a)` at some
round `t ≤ n`, with `h(u) = u - log u`, is at most
`2 e #S (log n / n ^ (1 + c) + 1 / n ^ (1 + c))`. -/
theorem measure_exists_mem_exists_subLogInv_le_pullCount_mul_expFamilyRate_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ} (S : Finset α)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ) (c : ℝ) (n : ℕ) :
    P {ω | ∃ a ∈ S, ∃ t ≤ n, ENNReal.ofReal (subLogInv ((1 + c) * log n)) ≤
        pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤
      ENNReal.ofReal (2 * exp 1 * #S * (log n / (n : ℝ) ^ (1 + c) + 1 / (n : ℝ) ^ (1 + c))) :=
  (measure_mono (setOf_exists_mem_exists_le_pullCount_mul_expFamilyRate_subset S hν _ n)).trans
    (measure_exists_mem_exists_subLogInv_le_pullCount_mul_rateFunction_le h S
      (fun a ha ↦ (hν a ha).integrable_of_mem_expFamilyMeans (hμ a ha)) c n)

/-- **The concentration events of [DKM19, Lemma 6] for exponential families are summable.** In a
run of any algorithm against `Environment.bandit ν`, let the rewards of each arm `a ∈ S` be
dominated on `Set.univ`, in moment generating function, by the member of mean `μ a` of the
exponential family `(ρ a, T a)`, with extended divergence `dbar_a`
(`MeasureTheory.Measure.expFamilyRate`). Then for `c > 0`, the probabilities, over the horizons
`n`, that some arm `a ∈ S` has `h⁻¹((1 + c) log n) ≤ N_a(t) dbar_a(μ̂_a(t), μ a)` at some round
`t ≤ n`, with `h(u) = u - log u`, sum to at most `2 e #S (2 + 1 / c + 1 / c²)`. -/
theorem tsum_measure_exists_mem_exists_subLogInv_le_pullCount_mul_expFamilyRate_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ : α → ℝ} (S : Finset α)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ) {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, P {ω | ∃ a ∈ S, ∃ t ≤ n, ENNReal.ofReal (subLogInv ((1 + c) * log n)) ≤
        pullCount A a t ω * (ρ a).expFamilyRate (T a) (empMean A R a t ω) (μ a)} ≤
      ENNReal.ofReal (2 * exp 1 * #S * (2 + 1 / c + 1 / c ^ 2)) :=
  (tsum_le_tsum fun n ↦
    measure_mono (setOf_exists_mem_exists_le_pullCount_mul_expFamilyRate_subset S hν _ n)).trans
    (tsum_measure_exists_mem_exists_subLogInv_le_pullCount_mul_rateFunction_le h S
      (fun a ha ↦ (hν a ha).integrable_of_mem_expFamilyMeans (hμ a ha)) hc)

end ExpFamilyRate

end LMLExplore
