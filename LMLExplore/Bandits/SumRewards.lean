/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.RewardByCountMeasure
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Add
public import LMLExplore.MeasureTheory.Measure.Prod
public import LMLExplore.SequentialLearning.FiniteActions

/-!
# From a run of a bandit algorithm to the reward stream of one arm

The analysis of an index policy such as UCB, MOSS or KL-UCB bounds the number of rounds at which
arm `a` is pulled while some event about its empirical mean holds. After `s` pulls, the empirical
mean of arm `a` is the mean of its first `s` rewards, and in a run of any algorithm against the
stochastic bandit `stationaryEnv ν` those rewards are i.i.d. with law `ν a`. This file transfers
such counts and events from the run to the i.i.d. stream model `streamMeasure ν` of LML, for all
numbers of pulls `s` simultaneously, without a union bound over the rounds.

For a property `p s x` of a number of pulls `s` and a sum of rewards `x`:

* the expected number of rounds `t < n` at which `a` is pulled and `p` holds for the number of
  previous pulls and the sum of the previous rewards of `a` is at most
  `∑ s < n, P(p s (X₀ + ⋯ + X_{s-1}))` for an i.i.d. sequence `X` with law `ν a`;
* the probability that `p` holds for these quantities at some round `t < n` is at most the
  probability that `p s (X₀ + ⋯ + X_{s-1})` holds for some `s < n`.

The first statement is the step of the proofs of [LS, Theorems 8.1, 9.1 and 10.6] that bounds the
contribution of the rounds at which a suboptimal arm has an overestimated index; the second is the
step that controls an underestimated index of the optimal arm by a maximal inequality.

## Main statements

* `identDistrib_rewardByCount_streamMeasure`: the rewards of arm `a` by count have the law of its
  rewards in the stream model.
* `sum_measure_action_eq_and_pullCount_sumRewards_le`: the bound on the expected number of rounds,
  as a sum of probabilities in `ℝ≥0∞`, and `sum_measureReal_action_eq_and_pullCount_sumRewards_le`,
  its real-valued form.
* `measure_exists_lt_pullCount_sumRewards_le`: the bound on the probability of the event at some
  round.

## Implementation notes

The proofs work on the product of the probability space of the run with `streamMeasure ν`, on which
LML's `rewardByCount A R a (i + 1)` is the reward of the `(i + 1)`-th pull of `a` and the sequence
of these rewards is i.i.d. with law `ν a` (`identDistrib_rewardByCount_streamMeasure`, from LML's
`Bandits.iIndepFun_rewardByCount_add_one_action`). The sum of the rewards of `a` before round `t`
is the sum of the first `pullCount A a t` of them, and the rounds that pull `a` see the pull counts
`0, 1, …` each once (`sum_range_ite_action_eq`).

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Bandits

open scoped ENNReal

namespace LMLExplore.Bandits

variable {α Ω : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [DecidableEq α]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {p : ℕ → ℝ → Prop}

/-- The sum of the rewards of arm `a` before round `t` is the sum of its first `pullCount A a t`
rewards by count. -/
lemma sumRewards_eq_sum_range_rewardByCount (a : α) (t : ℕ) (ω : Ω × (ℕ → α → ℝ)) :
    sumRewards A R a t ω.1 = ∑ i ∈ range (pullCount A a t ω.1), rewardByCount A R a (i + 1) ω := by
  rw [← sum_rewardByCount_eq_sumRewards, range_eq_Ico,
    sum_Ico_add' (fun m ↦ rewardByCount A R a m ω), zero_add,
    Ico_add_one_right_eq_Icc]

variable [Countable α] [MeasurableSingletonClass α]

/-- In a run against `stationaryEnv ν`, extended by the auxiliary stream, the sequence
`(rewardByCount A R a (i + 1))_i` of the rewards of arm `a` by count has the law of the sequence
`(ω i a)_i` of the rewards of `a` in the stream model `streamMeasure ν`: both are i.i.d. with law
`ν a`. -/
lemma identDistrib_rewardByCount_streamMeasure
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α) :
    IdentDistrib (fun ω i ↦ rewardByCount A R a (i + 1) ω) (fun ω i ↦ ω i a)
      (P.prod (streamMeasure ν)) (streamMeasure ν) :=
  have hZ : HasLaw (fun ω i ↦ rewardByCount A R a (i + 1) ω)
      (Measure.infinitePi fun _ ↦ ν a) (P.prod (streamMeasure ν)) :=
    (iIndepFun_rewardByCount_add_one_action h a).hasLaw_infinitePi
      (hasLaw_rewardByCount_add_one h a)
      (Measurable.of_eval fun i ↦ measurable_rewardByCount h.measurable_action
        h.measurable_feedback a (i + 1)).aemeasurable
  have hX : HasLaw (fun ω i ↦ ω i a) (Measure.infinitePi fun _ ↦ ν a) (streamMeasure ν) :=
    (iIndepFun_eval_streamMeasure'' ν a).hasLaw_infinitePi
      (fun i ↦ hasLaw_eval_eval_streamMeasure ν i a)
      (Measurable.of_eval fun i ↦ (measurable_pi_apply a).comp (measurable_pi_apply i)).aemeasurable
  { aemeasurable_fst := hZ.aemeasurable
    aemeasurable_snd := hX.aemeasurable
    map_eq := hZ.map_eq.trans hX.map_eq.symm }

/-- **Counting transfer to the reward stream.** In a run of any algorithm against the stochastic
bandit `stationaryEnv ν`, the expected number of rounds `t < n` at which arm `a` is pulled while
`p` holds for its number of previous pulls and the sum of its previous rewards is at most
`∑ s < n, P(p s (X₀ + ⋯ + X_{s-1}))` for an i.i.d. sequence `X` with law `ν a`, the rewards of `a`
in the stream model `streamMeasure ν`. -/
theorem sum_measure_action_eq_and_pullCount_sumRewards_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α) (n : ℕ)
    (hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2) :
    ∑ t ∈ range n, P {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      ∑ s ∈ range n, streamMeasure ν {ω | p s (∑ i ∈ range s, ω i a)} := by
  classical
  have hA := h.measurable_action
  have hR := h.measurable_feedback
  -- the event of round `t`, and the event about the first `s` rewards of a sequence
  set E : ℕ → Set Ω := fun t ↦ {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)}
  set B : ℕ → Set (ℕ → ℝ) := fun s ↦ {x | p s (∑ i ∈ range s, x i)}
  have hE t : MeasurableSet (E t) :=
    (measurableSet_eq_fun (hA t) measurable_const).inter
      (measurableSet_setOfPred.mpr (hp.comp ((measurable_pullCount hA a t).prodMk
        (measurable_sumRewards hA hR a t))))
  have hB s : MeasurableSet (B s) :=
    measurableSet_setOfPred.mpr (hp.of_uncurry_left.comp (by fun_prop))
  have hZ := identDistrib_rewardByCount_streamMeasure h a
  set Z : Ω × (ℕ → α → ℝ) → ℕ → ℝ := fun ω i ↦ rewardByCount A R a (i + 1) ω
  have hZ_meas : Measurable Z := .of_eval fun i ↦ measurable_rewardByCount hA hR a (i + 1)
  -- pathwise, the rounds that pull `a` see the pull counts `0, 1, …` once each
  have h_path (ω : Ω × (ℕ → α → ℝ)) :
      ∑ t ∈ range n, (Prod.fst ⁻¹' E t).indicator (1 : Ω × (ℕ → α → ℝ) → ℝ≥0∞) ω =
        ∑ s ∈ range (pullCount A a n ω.1), (Z ⁻¹' B s).indicator 1 ω := by
    rw [← sum_range_ite_action_eq]
    refine sum_congr rfl fun t _ ↦ ?_
    by_cases hat : A t ω.1 = a <;>
      simp [Set.indicator_apply, E, B, Z, hat, sumRewards_eq_sum_range_rewardByCount a t ω]
  calc ∑ t ∈ range n, P (E t)
  _ = ∑ t ∈ range n, P.prod (streamMeasure ν) (Prod.fst ⁻¹' E t) := by
    simp
  _ = ∫⁻ ω, ∑ t ∈ range n, (Prod.fst ⁻¹' E t).indicator 1 ω ∂(P.prod (streamMeasure ν)) :=
    (lintegral_finsetSum_indicator_one fun t _ ↦ measurable_fst (hE t)).symm
  _ ≤ ∫⁻ ω, ∑ s ∈ range n, (Z ⁻¹' B s).indicator 1 ω ∂(P.prod (streamMeasure ν)) := by
    refine lintegral_mono fun ω ↦ (h_path ω).trans_le ?_
    exact sum_le_sum_of_subset (range_subset_range.mpr (pullCount_le a n ω.1))
  _ = ∑ s ∈ range n, P.prod (streamMeasure ν) (Z ⁻¹' B s) :=
    lintegral_finsetSum_indicator_one fun s _ ↦ hZ_meas (hB s)
  _ = ∑ s ∈ range n, streamMeasure ν {ω | p s (∑ i ∈ range s, ω i a)} :=
    sum_congr rfl fun s _ ↦ hZ.measure_mem_eq (hB s)

/-- Real-valued form of `sum_measure_action_eq_and_pullCount_sumRewards_le`: in a run against
`stationaryEnv ν`, the expected number of rounds `t < n` at which arm `a` is pulled while `p` holds
for its number of previous pulls and the sum of its previous rewards is at most
`∑ s < n, P(p s (X₀ + ⋯ + X_{s-1}))` for the i.i.d. rewards `X` of `a` in the stream model. -/
theorem sum_measureReal_action_eq_and_pullCount_sumRewards_le
    (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) (a : α) (n : ℕ)
    (hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2) :
    ∑ t ∈ range n, P.real {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      ∑ s ∈ range n, (streamMeasure ν).real {ω | p s (∑ i ∈ range s, ω i a)} := by
  simp_rw [measureReal_def]
  rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _,
    ← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _)
    (sum_measure_action_eq_and_pullCount_sumRewards_le h a n hp)

/-- **Event transfer to the reward stream.** In a run of any algorithm against the stochastic
bandit `stationaryEnv ν`, the probability that `p` holds for the number of previous pulls of arm
`a` and the sum of its previous rewards at some round `t < n` is at most the probability that
`p s (X₀ + ⋯ + X_{s-1})` holds for some `s < n`, for the i.i.d. rewards `X` of `a` in the stream
model `streamMeasure ν`. -/
theorem measure_exists_lt_pullCount_sumRewards_le (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P)
    (a : α) (n : ℕ) (hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2) :
    P {ω | ∃ t < n, p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      streamMeasure ν {ω | ∃ s < n, p s (∑ i ∈ range s, ω i a)} := by
  set Z : Ω × (ℕ → α → ℝ) → ℕ → ℝ := fun ω i ↦ rewardByCount A R a (i + 1) ω
  set B : Set (ℕ → ℝ) := {x | ∃ s < n, p s (∑ i ∈ range s, x i)}
  have hB : MeasurableSet B := measurableSet_setOfPred.mpr
    (Measurable.exists fun s ↦ measurable_const.and (hp.of_uncurry_left.comp (by fun_prop)))
  calc P {ω | ∃ t < n, p (pullCount A a t ω) (sumRewards A R a t ω)}
  _ = P.prod (streamMeasure ν) (Prod.fst ⁻¹' {ω | ∃ t < n,
      p (pullCount A a t ω) (sumRewards A R a t ω)}) := by
    rw [Measure.prod_preimage_fst, measure_univ, one_mul]
  _ ≤ P.prod (streamMeasure ν) (Z ⁻¹' B) := by
    refine measure_mono fun ω ⟨t, ht, hpt⟩ ↦ ?_
    -- at round `t`, arm `a` has been pulled `pullCount A a t ω ≤ t < n` times
    refine ⟨pullCount A a t ω.1, (pullCount_le a t ω.1).trans_lt ht, ?_⟩
    rwa [← sumRewards_eq_sum_range_rewardByCount]
  _ = streamMeasure ν {ω | ∃ s < n, p s (∑ i ∈ range s, ω i a)} :=
    (identDistrib_rewardByCount_streamMeasure h a).measure_mem_eq hB

end LMLExplore.Bandits
