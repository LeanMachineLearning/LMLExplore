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
* the probability that `p` holds for these quantities at some round is at most the probability
  that `p s (X₀ + ⋯ + X_{s-1})` holds for some `s`, and the same holds with rounds `t < n` and
  counts `s < n`.

The first statement is the step of the proofs of [LS, Theorems 8.1, 9.1 and 10.6] that bounds the
contribution of the rounds at which a suboptimal arm has an overestimated index; the second is the
step that controls an underestimated index of the optimal arm by a maximal inequality, and, without
a horizon, the step that turns a maximal inequality for i.i.d. sums into a confidence bound valid
at all rounds of the run.

## Main statements

* `hasLaw_rewardByCount_streamMeasure`: the rewards by count of all arms, arranged as a reward
  stream, have the law `streamMeasure ν` of the stream model.
* `sum_measure_action_eq_and_pullCount_sumRewards_le`: the bound on the expected number of rounds,
  as a sum of probabilities in `ℝ≥0∞`, and `sum_measureReal_action_eq_and_pullCount_sumRewards_le`,
  its real-valued form.
* `measure_exists_pullCount_sumRewards_le`: the bound on the probability of the event at some
  round, and `measure_exists_lt_pullCount_sumRewards_le`, its form up to a horizon `n`.

## Implementation notes

The proofs work on the product of the probability space of the run with `streamMeasure ν`, on which
LML's `rewardByCount A R b (i + 1)` is the reward of the `(i + 1)`-th pull of `b`, and the array
`(i, b) ↦ rewardByCount A R b (i + 1)` has the law of the stream
(`hasLaw_rewardByCount_streamMeasure`, from LML's `Bandits.hasLaw_rewardByCount_infinitePi`). The
sum of the rewards of `a` before round `t` is the sum of the first `pullCount A a t` of them, and
the rounds that pull `a` see the pull counts `0, 1, …` each once (`sum_range_ite_action_eq`).

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
lemma sumRewards_eq_sum_range_rewardByCount {𝓨 : Type*} [AddCommGroup 𝓨] {R : ℕ → Ω → 𝓨}
    (a : α) (t : ℕ) (ω : Ω × (ℕ → α → 𝓨)) :
    sumRewards A R a t ω.1 = ∑ i ∈ range (pullCount A a t ω.1), rewardByCount A R a (i + 1) ω := by
  rw [← sum_rewardByCount_eq_sumRewards, range_eq_Ico,
    sum_Ico_add' (fun m ↦ rewardByCount A R a m ω), zero_add,
    Ico_add_one_right_eq_Icc]

variable [Countable α] [MeasurableSingletonClass α]

/-- In a run against `stationaryEnv ν`, extended by the auxiliary stream, the rewards by count of
all arms, arranged as a reward stream `(i, b) ↦ rewardByCount A R b (i + 1)`, have law
`streamMeasure ν`: the reward of the `(i + 1)`-th pull of arm `b` plays the role of the `i`-th
reward of `b` in the stream model. -/
lemma hasLaw_rewardByCount_streamMeasure (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P) :
    HasLaw (fun ω i b ↦ rewardByCount A R b (i + 1) ω) (streamMeasure ν)
      (P.prod (streamMeasure ν)) := by
  -- indexed by `(arm, count)`, both the rewards by count and the stream have law `⨂ (b, i), ν b`,
  -- and `toStream` arranges such an array as a stream
  let toStream : (α × ℕ → ℝ) → ℕ → α → ℝ := fun x i b ↦ x (b, i)
  have h_toStream : Measurable toStream := by fun_prop
  have h_swap : Measurable fun (x : ℕ → α → ℝ) (q : α × ℕ) ↦ x q.2 q.1 :=
    .of_eval fun _ ↦ by fun_prop
  have h_stream : HasLaw (fun (x : ℕ → α → ℝ) (q : α × ℕ) ↦ x q.2 q.1)
      (Measure.infinitePi fun q : α × ℕ ↦ ν q.1) (streamMeasure ν) :=
    ((iIndepFun_eval_streamMeasure ν).precomp Prod.swap_injective).hasLaw_infinitePi
      (fun q ↦ hasLaw_eval_eval_streamMeasure ν q.2 q.1) h_swap.aemeasurable
  have h_eq : (Measure.infinitePi fun q : α × ℕ ↦ ν q.1).map toStream = streamMeasure ν := by
    rw [← h_stream.map_eq, Measure.map_map h_toStream h_swap]
    exact Measure.map_id
  exact h_eq ▸ (hasLaw_map h_toStream.aemeasurable).comp (hasLaw_rewardByCount_infinitePi h)

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
  -- the event of round `t`, and the event about the first `s` rewards of `a` in a stream
  set E : ℕ → Set Ω := fun t ↦ {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)}
  set B : ℕ → Set (ℕ → α → ℝ) := fun s ↦ {x | p s (∑ i ∈ range s, x i a)}
  have hE t : MeasurableSet (E t) :=
    (measurableSet_eq_fun (hA t) measurable_const).inter
      (measurableSet_setOfPred.mpr (hp.comp ((measurable_pullCount hA a t).prodMk
        (measurable_sumRewards hA hR a t))))
  have hB s : MeasurableSet (B s) :=
    measurableSet_setOfPred.mpr (hp.of_uncurry_left.comp (by fun_prop))
  have hZ := hasLaw_rewardByCount_streamMeasure h
  set Z : Ω × (ℕ → α → ℝ) → ℕ → α → ℝ := fun ω i b ↦ rewardByCount A R b (i + 1) ω
  have hZ_meas : Measurable Z :=
    .of_eval fun i ↦ .of_eval fun b ↦ measurable_rewardByCount hA hR b (i + 1)
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
    sum_congr rfl fun s _ ↦ hZ.measure_eq (hB s)

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
`a` and the sum of its previous rewards at some round is at most the probability that
`p s (X₀ + ⋯ + X_{s-1})` holds for some `s`, for the i.i.d. rewards `X` of `a` in the stream model
`streamMeasure ν`. This is the form used for confidence bounds valid at all rounds at once. -/
theorem measure_exists_pullCount_sumRewards_le (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P)
    (a : α) (hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2) :
    P {ω | ∃ t, p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      streamMeasure ν {ω | ∃ s, p s (∑ i ∈ range s, ω i a)} := by
  set Z : Ω × (ℕ → α → ℝ) → ℕ → α → ℝ := fun ω i b ↦ rewardByCount A R b (i + 1) ω
  set B : Set (ℕ → α → ℝ) := {x | ∃ s, p s (∑ i ∈ range s, x i a)}
  have hB : MeasurableSet B := measurableSet_setOfPred.mpr
    (Measurable.exists fun s ↦ hp.of_uncurry_left.comp (by fun_prop))
  calc P {ω | ∃ t, p (pullCount A a t ω) (sumRewards A R a t ω)}
  _ = P.prod (streamMeasure ν)
      (Prod.fst ⁻¹' {ω | ∃ t, p (pullCount A a t ω) (sumRewards A R a t ω)}) := by
    rw [Measure.prod_preimage_fst, measure_univ, one_mul]
  _ ≤ P.prod (streamMeasure ν) (Z ⁻¹' B) := by
    -- at round `t`, the rewards of `a` so far are its first `pullCount A a t ω` rewards by count
    refine measure_mono fun ω ⟨t, ht⟩ ↦ ⟨pullCount A a t ω.1, ?_⟩
    rwa [← sumRewards_eq_sum_range_rewardByCount]
  _ = streamMeasure ν B := (hasLaw_rewardByCount_streamMeasure h).measure_eq hB

/-- **Event transfer to the reward stream, up to a horizon.** In a run of any algorithm against the
stochastic bandit `stationaryEnv ν`, the probability that `p` holds for the number of previous
pulls of arm `a` and the sum of its previous rewards at some round `t < n` is at most the
probability that `p s (X₀ + ⋯ + X_{s-1})` holds for some `s < n`, for the i.i.d. rewards `X` of `a`
in the stream model `streamMeasure ν`. -/
theorem measure_exists_lt_pullCount_sumRewards_le (h : IsAlgEnvSeq O A R alg (stationaryEnv ν) P)
    (a : α) (n : ℕ) (hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2) :
    P {ω | ∃ t < n, p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      streamMeasure ν {ω | ∃ s < n, p s (∑ i ∈ range s, ω i a)} := by
  calc P {ω | ∃ t < n, p (pullCount A a t ω) (sumRewards A R a t ω)}
  _ ≤ P {ω | ∃ t, pullCount A a t ω < n ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} :=
    -- at round `t < n`, arm `a` has been pulled `pullCount A a t ω ≤ t < n` times
    measure_mono fun ω ⟨t, ht, hpt⟩ ↦ ⟨t, (pullCount_le a t ω).trans_lt ht, hpt⟩
  _ ≤ streamMeasure ν {ω | ∃ s < n, p s (∑ i ∈ range s, ω i a)} :=
    measure_exists_pullCount_sumRewards_le (p := fun s x ↦ s < n ∧ p s x) h a
      ((Measurable.of_discrete (f := (· < n))).comp measurable_fst |>.and hp)

end LMLExplore.Bandits
