/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.SequentialLearning.ExpFamilyDeviation

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
exponential family `(ρ a, T a)` with divergence `d_a` (for instance their law is that member). For
one arm, the probability that, at some round, it has at least `m` pulls and an empirical mean
outside `(l a, u a)` is bounded by the Cramér–Chernoff bound and a union bound over the numbers of
pulls `s ≥ m` in LML's i.i.d. reward stream
(`LMLExplore.measure_exists_le_pullCount_and_empMean_notMem_Ioo_le`). Under forced
exploration, a union bound over the arms gives the bound
`∑ a, (exp (-m d_a(u a, μ a)) / (1 - exp (-d_a(u a, μ a))) + exp (-m d_a(l a, μ a)) / (1 - …))`.
The bound holds at all rounds `t ≥ t₀` at once, with no upper horizon, which improves on the
`B T exp (-C T^(1/8))` of [GK16, Lemma 19].

## Main statements

* `LMLExplore.Identification.measure_exists_ge_empMean_notMem_Ioo_le`: [GK16, Lemma 19] for any
  algorithm whose runs have at least `m` pulls of every arm after `t₀` rounds: the probability that
  the empirical mean of some arm `a` leaves `(l a, u a)` at some round `t ≥ t₀` is at most the sum
  over the arms of the one-arm bounds
  `exp (-m d(u, μ)) / (1 - exp (-d(u, μ))) + exp (-m d(l, μ)) / (1 - exp (-d(l, μ)))`.
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

namespace LMLExplore.Identification

variable {α 𝓧 Ω : Type*} {mα : MeasurableSpace α} {m𝓧 : MeasurableSpace 𝓧}
  {mΩ : MeasurableSpace Ω} [DecidableEq α] [Countable α] [MeasurableSingletonClass α]
  {ν : Kernel α ℝ} [IsMarkovKernel ν] {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}

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
    exact Finset.sum_le_sum fun a _ ↦
      measure_exists_le_pullCount_and_empMean_notMem_Ioo_le h (hν_above a) (hν_below a)
        (hμ a) (hl a) (hu a) (hlμ a) (hμu a) m

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
