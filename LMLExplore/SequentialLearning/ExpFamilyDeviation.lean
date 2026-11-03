/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.Probability.Distributions.ExponentialFamily.Chernoff
public import LMLExplore.SequentialLearning.SumRewards

/-!
# Deviations of empirical means for rewards dominated by an exponential family

Let the rewards of arm `a` of a stochastic environment `Environment.bandit ν` be dominated above and
below by the member of mean `μ` of the exponential family of a measure `ρ` and a statistic `T`,
with divergence `d` in the mean parametrization. This file bounds the deviations of the empirical
mean of `a`: first for the first `s` rewards in the reward stream model `streamMeasure ν`, by the
Cramér–Chernoff bounds of `ExponentialFamily/Chernoff.lean`, then in a run of any algorithm, at all
rounds simultaneously, through the transfer of `SequentialLearning/SumRewards.lean`. Nothing here
depends on how the algorithm chooses its actions, so the bounds apply to the sampling rules of
identification algorithms as well as to the policies of regret minimization.

## Main statements

* `streamMeasure_sum_ge_le_exp_expFamilyDiv`, `streamMeasure_sum_le_le_exp_expFamilyDiv`: the
  Cramér–Chernoff bounds for the first `s` rewards of an arm in the reward stream model.
* `measure_exists_le_pullCount_and_empMean_notMem_Ioo_le`: in a run of any algorithm, the
  probability that, at some round, arm `a` has at least `m` pulls and an empirical mean outside
  `(l, u)` is at most
  `exp (-m d(u, μ)) / (1 - exp (-d(u, μ))) + exp (-m d(l, μ)) / (1 - exp (-d(l, μ)))`.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section ExpFamilyStream

variable {α 𝓧 : Type*} [MeasurableSpace α] {m𝓧 : MeasurableSpace 𝓧} {ν : Kernel α ℝ}
  [IsMarkovKernel ν] {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {a : α} {μ x : ℝ}

/-- **Cramér–Chernoff bound in the reward stream, upper tail.** If the rewards of arm `a` are
dominated above by the member of mean `μ` of the exponential family of `ρ` and `T`, then for a mean
`x ≥ μ` of the family, the sum of the first `s` rewards of `a` in the reward stream model is at
least `s x` with probability at most `exp (-(s d(x, μ)))`. -/
theorem streamMeasure_sum_ge_le_exp_expFamilyDiv
    (hν : MGFDominatedAbove id (ν a) T (ρ.expFamily T (ρ.natParam T μ)))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hμx : μ ≤ x) (s : ℕ) :
    streamMeasure ν {ω | s * x ≤ ∑ i ∈ range s, ω i a} ≤
      ENNReal.ofReal (exp (-(s * ρ.expFamilyDiv T x μ))) := by
  have h := (iIndepFun_eval_streamMeasure'' ν a).measureReal_sum_ge_le_exp_expFamilyDiv
    (s := range s)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedAbove.trans hν) hμ hx hμx
  rw [card_range] at h
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- **Cramér–Chernoff bound in the reward stream, lower tail.** If the rewards of arm `a` are
dominated below by the member of mean `μ` of the exponential family of `ρ` and `T`, then for a mean
`x ≤ μ` of the family, the sum of the first `s` rewards of `a` in the reward stream model is at
most `s x` with probability at most `exp (-(s d(x, μ)))`. -/
theorem streamMeasure_sum_le_le_exp_expFamilyDiv
    (hν : MGFDominatedBelow id (ν a) T (ρ.expFamily T (ρ.natParam T μ)))
    (hμ : μ ∈ ρ.expFamilyMeans T) (hx : x ∈ ρ.expFamilyMeans T) (hxμ : x ≤ μ) (s : ℕ) :
    streamMeasure ν {ω | ∑ i ∈ range s, ω i a ≤ s * x} ≤
      ENNReal.ofReal (exp (-(s * ρ.expFamilyDiv T x μ))) := by
  have h := (iIndepFun_eval_streamMeasure'' ν a).measureReal_sum_le_le_exp_expFamilyDiv
    (s := range s)
    (fun i _ ↦ (identDistrib_eval_eval_id_streamMeasure ν i a).mgfDominatedBelow.trans hν) hμ hx hxμ
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
dominated above and below by the member of mean `μ` of the exponential family of `ρ` and `T`, with
divergence `d`, and let `l < μ < u` be means of the family. The probability that, at some round, `a`
has at least `m` pulls and an empirical mean outside `(l, u)` is at most
`exp (-m d(u, μ)) / (1 - exp (-d(u, μ))) + exp (-m d(l, μ)) / (1 - exp (-d(l, μ)))`. -/
theorem measure_exists_le_pullCount_and_empMean_notMem_Ioo_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (hν_above : MGFDominatedAbove id (ν a) T (ρ.expFamily T (ρ.natParam T μ)))
    (hν_below : MGFDominatedBelow id (ν a) T (ρ.expFamily T (ρ.natParam T μ)))
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
    exact (add_le_add (streamMeasure_sum_le_le_exp_expFamilyDiv hν_below hμ hl hlμ.le _)
      (streamMeasure_sum_ge_le_exp_expFamilyDiv hν_above hμ hu hμu.le _)).trans_eq (add_comm _ _)
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

end LMLExplore
