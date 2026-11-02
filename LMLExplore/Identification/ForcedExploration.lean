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
# Concentration of the empirical means under forced exploration

A sampling rule *forces exploration* if every arm is pulled a growing number of times, whatever
the observations: the D-tracking rule of Track-and-Stop guarantees `√t - K / 2 - 1 < N_a(t)`
(`LMLExplore.Identification.sqrt_sub_sub_one_lt_pullCount`). Then, after a number `t₀` of rounds
at which every arm has `m` pulls, the empirical means `μ̂_a(t)` of all the arms stay in given
neighbourhoods `(l a, u a)` of the means `μ a` at every round `t ≥ t₀`, except with probability
exponentially small in `m`. This is [GK16, Lemma 19], the concentration step of the asymptotic
optimality of Track-and-Stop: on the events `E_T` that the empirical means are close to `μ` from
round `h(T)` on, the empirical optimal allocations are close to `w*(μ)`, and the events `E_T`
fail with probabilities that sum to a finite value, as the generic reduction
`LMLExplore.Identification.IdentTask.eventually_expectedStoppingTime_glrt_le` requires.

The rewards of each arm `a` are dominated, above and below, by the member of mean `μ a` of an
exponential family `(ρ a, T a)` with divergence `d_a` (for instance their law is that member). The
empirical mean of arm `a` after `s` pulls is at least `u a` with probability at most
`exp (-s d_a(u a, μ a))`, by the Cramér–Chernoff bound, and symmetrically below `l a`. A union
bound over the numbers of pulls `s ≥ m`, through the transfer of the run to LML's i.i.d. reward
stream (`LMLExplore.measure_exists_pullCount_sumRewards_le`), gives the bound
`∑ a, (exp (-m d_a(u a, μ a)) / (1 - exp (-d_a(u a, μ a))) + exp (-m d_a(l a, μ a)) / (1 - …))`.
The bound holds at all rounds `t ≥ t₀` at once, with no upper horizon, which improves on the
`B T exp (-C T^(1/8))` of [GK16, Lemma 19].

## Main statements

* `LMLExplore.streamMeasure_sum_ge_le_exp_expFamilyDiv`,
  `LMLExplore.streamMeasure_sum_le_le_exp_expFamilyDiv`: the Cramér–Chernoff bounds for the first
  `s` rewards of an arm in the reward stream model `streamMeasure ν`, for rewards dominated by a
  member of an exponential family.
* `LMLExplore.Identification.measure_exists_le_pullCount_and_empMean_notMem_Ioo_le`: in a run of
  any algorithm, the probability that, at some round, arm `a` has at least `m` pulls and an
  empirical mean outside `(l, u)` is at most
  `exp (-m d(u, μ)) / (1 - exp (-d(u, μ))) + exp (-m d(l, μ)) / (1 - exp (-d(l, μ)))`.
* `LMLExplore.Identification.measure_exists_ge_empMean_notMem_Ioo_le`: [GK16, Lemma 19] for any
  algorithm whose runs have at least `m` pulls of every arm after `t₀` rounds: the probability that
  the empirical mean of some arm `a` leaves `(l a, u a)` at some round `t ≥ t₀` is at most the sum
  over the arms of the bounds above.
* `LMLExplore.Identification.tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top`: if every arm has
  at least `m T` pulls after `t₀ T` rounds, with `m T / log T → ∞`, the probabilities that the
  empirical means leave the neighbourhoods at some round `t ≥ t₀ T` have a finite sum over `T`.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Lemma 19 and the proof of Theorem 14.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Bandits Real Filter

open scoped ENNReal

/-! ### Cramér–Chernoff bounds in the reward stream -/

namespace LMLExplore

variable {α 𝓧 : Type*} {mα : MeasurableSpace α} {m𝓧 : MeasurableSpace 𝓧} {ν : Kernel α ℝ}
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

end LMLExplore

/-! ### Empirical means along a run -/

namespace LMLExplore.Identification

variable {α 𝓧 Ω : Type*} {mα : MeasurableSpace α} {m𝓧 : MeasurableSpace 𝓧}
  {mΩ : MeasurableSpace Ω} [DecidableEq α] [Countable α] [MeasurableSingletonClass α]
  {ν : Kernel α ℝ} [IsMarkovKernel ν] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}

/-- The terms of the deviation bounds are nonnegative. -/
private lemma exp_neg_mul_div_one_sub_exp_neg_nonneg {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    0 ≤ exp (-(x * d)) / (1 - exp (-d)) :=
  div_nonneg (exp_pos _).le (sub_nonneg.2 (exp_le_one_iff.2 (neg_nonpos.2 hd)))

variable {ρ : Measure 𝓧} {T : 𝓧 → ℝ} {a : α} {μ l u : ℝ}

omit [Countable α] in
/-- An empirical mean outside `(l, u)` after `s` pulls: the sum `y` of the rewards satisfies
`y ≤ s l` or `s u ≤ y`. With no pull, the empirical mean is `0` and the condition holds. -/
private lemma sum_le_mul_or_mul_le_sum_of_empMean_notMem_Ioo {t : ℕ} {ω : Ω}
    (h : empMean A R a t ω ∉ Set.Ioo l u) :
    sumRewards A R a t ω ≤ pullCount A a t ω * l ∨
      pullCount A a t ω * u ≤ sumRewards A R a t ω := by
  rcases Nat.eq_zero_or_pos (pullCount A a t ω) with h0 | hpos
  · simp only [h0, Nat.cast_zero, zero_mul]
    exact le_total _ _
  have hpos' : (0 : ℝ) < pullCount A a t ω := Nat.cast_pos.2 hpos
  rw [empMean, Set.mem_Ioo, not_and_or, not_lt, not_lt, div_le_iff₀ hpos', le_div_iff₀ hpos']
    at h
  rcases h with h | h
  · exact Or.inl (h.trans_eq (mul_comm _ _))
  · exact Or.inr ((mul_comm _ _).trans_le h)

/-- **Deviations of the empirical mean of an arm with at least `m` pulls.** In a run of any
algorithm against the stochastic bandit `stationaryEnv ν`, let the rewards of arm `a` be dominated
above and below by the member of mean `μ` of the exponential family of `ρ` and `T`, with divergence
`d`, and let `l < μ < u` be means of the family. The probability that, at some round, `a` has at
least `m` pulls and an empirical mean outside `(l, u)` is at most
`exp (-m d(u, μ)) / (1 - exp (-d(u, μ))) + exp (-m d(l, μ)) / (1 - exp (-d(l, μ)))`. -/
theorem measure_exists_le_pullCount_and_empMean_notMem_Ioo_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P)
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
    measure_mono fun ω ⟨t, hm, ht⟩ ↦ ⟨t, hm, sum_le_mul_or_mul_le_sum_of_empMean_notMem_Ioo ht⟩
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
    refine ENNReal.tsum_le_tsum fun k ↦ (measure_union_le _ _).trans ?_
    exact (add_le_add (streamMeasure_sum_le_le_exp_expFamilyDiv hν_below hμ hl hlμ.le _)
      (streamMeasure_sum_ge_le_exp_expFamilyDiv hν_above hμ hu hμu.le _)).trans_eq (add_comm _ _)
  _ = _ := by
    have h_tsum {d : ℝ} (hd : 0 < d) : ∑' k : ℕ, ENNReal.ofReal (exp (-((k + m : ℕ) * d))) =
        ENNReal.ofReal (exp (-(m * d)) / (1 - exp (-d))) := by
      push_cast
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (exp_pos _).le)
        (hasSum_exp_neg_add_mul hd m).summable, (hasSum_exp_neg_add_mul hd m).tsum_eq]
    rw [ENNReal.tsum_add, h_tsum hdu, h_tsum hdl,
      ENNReal.ofReal_add (exp_neg_mul_div_one_sub_exp_neg_nonneg hdu.le m)
        (exp_neg_mul_div_one_sub_exp_neg_nonneg hdl.le m)]

/-! ### All the arms after forced exploration -/

variable [Fintype α] {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ} {μ l u : α → ℝ}

/-- **Concentration of the empirical means under forced exploration** [GK16, Lemma 19]. In a run
of any algorithm against the stochastic bandit `stationaryEnv ν`, let the rewards of each arm `a`
be dominated above and below by the member of mean `μ a` of the exponential family of `ρ a` and
`T a`, with divergence `d_a`, and let `l a < μ a < u a` be means of the family. If almost surely
every arm has at least `m` pulls after `t₀` rounds, then the probability that the empirical mean of
some arm `a` is outside `(l a, u a)` at some round `t ≥ t₀` is at most
`∑ a, (exp (-m d_a(u a, μ a)) / (1 - exp (-d_a(u a, μ a))) +
  exp (-m d_a(l a, μ a)) / (1 - exp (-d_a(l a, μ a))))`. -/
theorem measure_exists_ge_empMean_notMem_Ioo_le (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P)
    (hν_above : ∀ a, MGFDominatedAbove id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a)) (hl : ∀ a, l a ∈ (ρ a).expFamilyMeans (T a))
    (hu : ∀ a, u a ∈ (ρ a).expFamilyMeans (T a)) (hlμ : ∀ a, l a < μ a) (hμu : ∀ a, μ a < u a)
    {t₀ m : ℕ} (h_forced : ∀ᵐ ω ∂P, ∀ a, m ≤ pullCount A a t₀ ω) :
    P {ω | ∃ t ≥ t₀, ∃ a, empMean A R a t ω ∉ Set.Ioo (l a) (u a)} ≤
      ENNReal.ofReal (∑ a, (exp (-(m * (ρ a).expFamilyDiv (T a) (u a) (μ a))) /
          (1 - exp (-(ρ a).expFamilyDiv (T a) (u a) (μ a))) +
        exp (-(m * (ρ a).expFamilyDiv (T a) (l a) (μ a))) /
          (1 - exp (-(ρ a).expFamilyDiv (T a) (l a) (μ a))))) := by
  -- From round `t₀` on, every arm has at least `m` pulls.
  calc P {ω | ∃ t ≥ t₀, ∃ a, empMean A R a t ω ∉ Set.Ioo (l a) (u a)}
  _ ≤ P (⋃ a, {ω | ∃ t, m ≤ pullCount A a t ω ∧ empMean A R a t ω ∉ Set.Ioo (l a) (u a)}) := by
    refine measure_mono_ae (h_forced.mono fun ω hω ⟨t, ht, a, ha⟩ ↦ ?_)
    exact Set.mem_iUnion.2 ⟨a, t, (hω a).trans (pullCount_mono a ht ω), ha⟩
  _ ≤ ∑ a, P {ω | ∃ t, m ≤ pullCount A a t ω ∧ empMean A R a t ω ∉ Set.Ioo (l a) (u a)} :=
    measure_iUnion_fintype_le _ _
  _ ≤ _ := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ ↦ add_nonneg
      (exp_neg_mul_div_one_sub_exp_neg_nonneg (Measure.expFamilyDiv_nonneg (hu a) (hμ a)) _)
      (exp_neg_mul_div_one_sub_exp_neg_nonneg (Measure.expFamilyDiv_nonneg (hl a) (hμ a)) _)]
    exact Finset.sum_le_sum fun a _ ↦ measure_exists_le_pullCount_and_empMean_notMem_Ioo_le h
      (hν_above a) (hν_below a) (hμ a) (hl a) (hu a) (hlμ a) (hμu a) m

omit [Fintype α] in
/-- **Summability of the failure probabilities under forced exploration**, the form of
[GK16, Lemma 19] used in the proof of [GK16, Theorem 14]. Under the assumptions of
`measure_exists_ge_empMean_notMem_Ioo_le`, if almost surely every arm has at least `m T` pulls after
`t₀ T` rounds, with `m T / log T → ∞`, then the probabilities that the empirical mean of some arm
`a` is outside `(l a, u a)` at some round `t ≥ t₀ T` have a finite sum over `T`. -/
theorem tsum_measure_exists_ge_empMean_notMem_Ioo_ne_top [Finite α]
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P)
    (hν_above : ∀ a, MGFDominatedAbove id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hν_below : ∀ a, MGFDominatedBelow id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))))
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a)) (hl : ∀ a, l a ∈ (ρ a).expFamilyMeans (T a))
    (hu : ∀ a, u a ∈ (ρ a).expFamilyMeans (T a)) (hlμ : ∀ a, l a < μ a) (hμu : ∀ a, μ a < u a)
    {t₀ m : ℕ → ℕ} (h_forced : ∀ T, ∀ᵐ ω ∂P, ∀ a, m T ≤ pullCount A a (t₀ T) ω)
    (hm : Tendsto (fun T : ℕ ↦ (m T : ℝ) / log T) atTop atTop) :
    ∑' T, P {ω | ∃ t ≥ t₀ T, ∃ a, empMean A R a t ω ∉ Set.Ioo (l a) (u a)} ≠ ∞ := by
  have := Fintype.ofFinite α
  have hdu (a : α) := Measure.expFamilyDiv_pos (hu a) (hμ a) (hμu a).ne'
  have hdl (a : α) := Measure.expFamilyDiv_pos (hl a) (hμ a) (hlμ a).ne
  -- The bound for `m T` pulls is summable in `T`, since `m T` grows faster than `log T`.
  have h_sum {d : ℝ} (hd : 0 < d) : Summable fun T ↦ exp (-(m T * d)) :=
    summable_exp_neg_of_tendsto_div_log <| (hm.atTop_mul_const hd).congr fun T ↦
      div_mul_eq_mul_div _ _ _
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun T ↦
    measure_exists_ge_empMean_notMem_Ioo_le h hν_above hν_below hμ hl hu hlμ hμu (h_forced T))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun T ↦ sum_nonneg fun a _ ↦ add_nonneg
      (exp_neg_mul_div_one_sub_exp_neg_nonneg (hdu a).le _)
      (exp_neg_mul_div_one_sub_exp_neg_nonneg (hdl a).le _))
    (summable_sum fun a _ ↦ ((h_sum (hdu a)).div_const _).add ((h_sum (hdl a)).div_const _))]
  exact ENNReal.ofReal_ne_top

end LMLExplore.Identification
