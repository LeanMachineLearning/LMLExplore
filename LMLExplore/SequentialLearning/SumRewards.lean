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
public import Mathlib.Probability.StrongLaw

/-!
# From a run of a sequential learning algorithm to the reward stream

The analysis of an index policy such as UCB, MOSS or KL-UCB bounds the number of rounds at which
arm `a` is pulled while some event about its empirical mean holds. After `s` pulls, the empirical
mean of arm `a` is the mean of its first `s` rewards, and in a run of any algorithm against the
stochastic environment `Environment.bandit ν` those rewards are i.i.d. with law `ν a`. This file
transfers such counts and events from the run to the i.i.d. stream model `streamMeasure ν` of LML,
for all numbers of pulls `s` simultaneously, without a union bound over the rounds. Nothing here
depends on how the algorithm chooses its actions, so the statements apply to the sampling rules of
identification algorithms as well as to the policies of regret minimization.

The observations of arm `a` before round `t`, `armObs A R a t ω : Fin (pullCount A a t ω) → ℝ`,
are its rewards in the order of the pulls. For a property `p s y` of `s` observations
`y : Fin s → ℝ`:

* the expected number of rounds `t < n` at which `a` is pulled and `p` holds for the previous
  observations of `a` is at most `∑ s < n, P(p s (X₀, …, X_{s-1}))` for an i.i.d. sequence `X`
  with law `ν a`;
* the probability that `p` holds for these observations at some round is at most the probability
  that `p s (X₀, …, X_{s-1})` holds for some `s`, and the same holds with rounds `t < n` and
  counts `s < n`.

Events about the empirical mean are events about the number of pulls and the sum of the
observations, and the file states both transfers for a property `p s x` of a number of pulls `s`
and a sum of rewards `x` too, as consequences of the transfers for the observations.

The first statement is the step of the proofs of [LS, Theorems 8.1, 9.1 and 10.6] that bounds the
contribution of the rounds at which a suboptimal arm has an overestimated index; the second is the
step that controls an underestimated index of the optimal arm by a maximal inequality, and, without
a horizon, the step that turns a maximal inequality for i.i.d. sums into a confidence bound valid
at all rounds of the run.

The event transfer also holds jointly over the arms: for a property `q s y` of the numbers of
pulls `s : α → ℕ` and the observations `y : (a : α) → Fin (s a) → ℝ` of all arms, the probability
that `q` holds at some round is at most the probability that it holds in the stream model for some
`s`. Events about the counts and the observations of all arms at once, such as the generalized
likelihood ratio statistics and the deviation inequalities of best arm identification, are bounded
this way.

## Main statements

* `hasLaw_rewardByCount_streamMeasure`: the rewards by count of all arms, arranged as a reward
  stream, have the law `streamMeasure ν` of the stream model.
* `iIndepFun_arm_streamMeasure`: in the stream model, the reward sequences of the arms are
  independent.
* `armObs`: the observations of an arm before a round, in the order of the pulls;
  `armObs_eq_rewardByCount` relates them to LML's rewards by count, and `sum_armObs` to the sum of
  rewards.
* `sum_setLIntegral_action_eq_pullCount_armObs_le`: the weighted form of the first statement, for
  measurable weights `g s y ≥ 0` in place of the indicator of `p`, and
  `sum_measure_action_eq_and_pullCount_armObs_le`, the bound on the expected number of rounds.
* `measure_exists_pullCount_armObs_pi_le`: the bound on the probability of an event about the
  observations of all arms at some round, and `measure_exists_lt_pullCount_armObs_pi_le`, its form
  up to a horizon `n`, for finitely many arms.
* `measure_exists_pullCount_armObs_le`: the bound on the probability of an event about the
  observations of one arm at some round, and `measure_exists_lt_pullCount_armObs_le`, its form up
  to a horizon `n`.
* `sum_setLIntegral_action_eq_pullCount_sumRewards_le`,
  `sum_measure_action_eq_and_pullCount_sumRewards_le` and its real-valued form
  `sum_measureReal_action_eq_and_pullCount_sumRewards_le`: the counting transfers for a property
  of the number of pulls and the sum of rewards.
* `measure_exists_pullCount_sumRewards_pi_le`, `measure_exists_lt_pullCount_sumRewards_pi_le`,
  `measure_exists_pullCount_sumRewards_le` and `measure_exists_lt_pullCount_sumRewards_le`: the
  event transfers for properties of the numbers of pulls and the sums of rewards.
* `empMean_mem_Icc`: rewards in `[l, u]` give empirical means in `[l, u]`.
* `sumRewards_le_mul_or_mul_le_sumRewards_of_empMean_notMem_Ioo`: an empirical mean outside
  `(l, u)` is an event `y ≤ s l ∨ s u ≤ y` about the number of pulls `s` and the sum of rewards
  `y`, the form to which the event transfers apply.
* `measureReal_pullCount_sumRewards_le_sum`: in a run of any algorithm against
  `Environment.bandit ν`, the probability that a property `p` of the number of pulls and the sum of
  rewards of an arm, which fails for zero pulls, holds at round `t` is at most the sum over `s < t`
  of the probabilities that `p (s + 1)` holds for the first `s + 1` rewards of the arm in the stream
  model.
* `measureReal_pullCount_ne_zero_and_empMean_le_sum`: its form for a property `q` of the number
  of pulls and the empirical mean of an arm that has been pulled: if `q s` holds for the empirical
  mean of the first `s ≠ 0` rewards in the stream model with probability at most `g s`, then the
  probability at round `t` is at most `∑_{s < t} g (s + 1)`.
* `ae_tendsto_empMean_of_tendsto_pullCount`: the strong law of large numbers for the empirical
  means of a run: almost surely, the empirical mean of every arm whose number of pulls tends to
  infinity converges to the mean of its law.

## Implementation notes

The proofs work on the product of the probability space of the run with `streamMeasure ν`, on which
LML's `rewardByCount A R b (i + 1)` is the reward of the `(i + 1)`-th pull of `b`, and the array
`(i, b) ↦ rewardByCount A R b (i + 1)` has the law of the stream
(`hasLaw_rewardByCount_streamMeasure`, from LML's `Bandits.hasLaw_rewardByCount_infinitePi`). The
observations of `a` before round `t` are the first `pullCount A a t` of them
(`armObs_eq_rewardByCount`), and the rounds that pull `a` see the pull counts `0, 1, …` each once
(`sum_range_ite_action_eq`). The transfers for sums of rewards are the transfers for the
observations applied to properties of their sums (`sum_armObs`).
The event transfers need no measurability of the event: they bound the outer measure of the event
of the run by that of the event in the stream model, through `Measure.le_map_apply`.
The strong law for the empirical means applies Mathlib's `strong_law_ae_real` to the i.i.d.
rewards by count of an arm on the same product space, and the almost sure event depends on the run
only, by `Measure.ae_ae_of_ae_prod`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Bandits Filter

open scoped ENNReal Topology

namespace LMLExplore

variable {α Ω : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [DecidableEq α]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm Unit α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {p : ℕ → ℝ → Prop}

/-- The sum of the rewards of arm `a` before round `t` is the sum of its first `pullCount A a t`
rewards by count. -/
lemma sumRewards_eq_sum_range_rewardByCount {𝓨 : Type*} [AddCommMonoid 𝓨] {R : ℕ → Ω → 𝓨}
    (a : α) (t : ℕ) (ω : Ω × (ℕ → α → 𝓨)) :
    sumRewards A R a t ω.1 = ∑ i ∈ range (pullCount A a t ω.1), rewardByCount A R a (i + 1) ω := by
  rw [← sum_rewardByCount_eq_sumRewards, range_eq_Ico,
    sum_Ico_add' (fun m ↦ rewardByCount A R a m ω), zero_add,
    Ico_add_one_right_eq_Icc]

/-- An empirical mean outside `(l, u)` after `s` pulls: the sum `y` of the rewards satisfies
`y ≤ s l` or `s u ≤ y`. With no pull, the empirical mean is `0` and the condition holds. -/
lemma sumRewards_le_mul_or_mul_le_sumRewards_of_empMean_notMem_Ioo {a : α} {t : ℕ} {ω : Ω}
    {l u : ℝ} (h : empMean A R a t ω ∉ Set.Ioo l u) :
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

/-- If the rewards before round `t` lie in `[l, u]`, then the empirical mean before round `t` of an
arm pulled before round `t` lies in `[l, u]`. -/
lemma empMean_mem_Icc {a : α} {t : ℕ} {ω : Ω} {l u : ℝ} (hR : ∀ s < t, R s ω ∈ Set.Icc l u)
    (h0 : pullCount A a t ω ≠ 0) : empMean A R a t ω ∈ Set.Icc l u := by
  have hpos : (0 : ℝ) < pullCount A a t ω := Nat.cast_pos.2 (Nat.pos_of_ne_zero h0)
  have hR' (s : ℕ) (hs : s ∈ (range t).filter (fun s ↦ A s ω = a)) : R s ω ∈ Set.Icc l u :=
    hR s (mem_range.1 (mem_filter.1 hs).1)
  rw [empMean, sumRewards, ← sum_filter, Set.mem_Icc, le_div_iff₀ hpos, div_le_iff₀ hpos]
  constructor
  · simpa [pullCount, mul_comm] using card_nsmul_le_sum _ (fun s ↦ R s ω) l fun s hs ↦ (hR' s hs).1
  · simpa [pullCount, mul_comm] using sum_le_card_nsmul _ (fun s ↦ R s ω) u fun s hs ↦ (hR' s hs).2

/-- The observations of arm `a` before round `t`, in the order of the pulls: the entry `i` is the
feedback `Y` at the round `stepsUntil A a (i + 1) ω < t` of the `(i + 1)`-th pull of `a`. -/
noncomputable def armObs {𝓨 : Type*} (A : ℕ → Ω → α) (Y : ℕ → Ω → 𝓨) (a : α) (t : ℕ) (ω : Ω) :
    Fin (pullCount A a t ω) → 𝓨 :=
  fun i ↦ Y (stepsUntil A a ((i : ℕ) + 1) ω).toNat ω

/-- The defining formula of `armObs`. -/
lemma armObs_def {𝓨 : Type*} (Y : ℕ → Ω → 𝓨) (a : α) (t : ℕ) (ω : Ω) :
    armObs A Y a t ω = fun i : Fin (pullCount A a t ω) ↦ Y (stepsUntil A a (i + 1) ω).toNat ω :=
  (rfl)

/-- The observation `i` of arm `a` before round `t` is LML's reward by count of the `(i + 1)`-th
pull of `a`, whatever the auxiliary stream. -/
lemma armObs_eq_rewardByCount {𝓨 : Type*} (Y : ℕ → Ω → 𝓨) (a : α) (t : ℕ)
    (ω : Ω × (ℕ → α → 𝓨)) (i : Fin (pullCount A a t ω.1)) :
    armObs A Y a t ω.1 i = rewardByCount A Y a (i + 1) ω := by
  rw [armObs_def, rewardByCount_of_stepsUntil_ne_top (stepsUntil_lt_of_lt_pullCount i.2).ne_top]

/-- The observations of arm `a` before round `t` add up to the sum of its rewards. -/
@[simp]
lemma sum_armObs {𝓨 : Type*} [AddCommMonoid 𝓨] (Y : ℕ → Ω → 𝓨) (a : α) (t : ℕ) (ω : Ω) :
    ∑ i, armObs A Y a t ω i = sumRewards A Y a t ω := by
  rw [sumRewards_eq_sum_range_rewardByCount a t (ω, 0), ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun i _ ↦ armObs_eq_rewardByCount Y a t (ω, 0) i

/-- A measurable function of a number of observations and of that many observations, evaluated at
the number of pulls of arm `a` before round `t` and at its observations, is measurable. -/
lemma measurable_comp_pullCount_armObs [MeasurableSingletonClass α] {𝓨 β : Type*}
    [MeasurableSpace 𝓨] [MeasurableSpace β] {Y : ℕ → Ω → 𝓨} (hA : ∀ n, Measurable (A n))
    (hY : ∀ n, Measurable (Y n)) {g : (s : ℕ) → (Fin s → 𝓨) → β} (hg : ∀ s, Measurable (g s))
    (a : α) (t : ℕ) :
    Measurable fun ω ↦ g (pullCount A a t ω) (armObs A Y a t ω) := by
  -- for a fixed number `s` of pulls, the first `s` observations are measurable
  have hF : Measurable fun q : ℕ × Ω ↦ g q.1 fun i ↦ Y (stepsUntil A a (i + 1) q.2).toNat q.2 :=
    measurable_from_prod_countable_right fun s ↦ (hg s).comp <| .of_eval fun i ↦
      (measurable_from_prod_countable_right (f := fun q : ℕ × Ω ↦ Y q.1 q.2) hY).comp
        ((measurable_stepsUntil hA a (i + 1)).enat_toNat.prodMk measurable_id)
  simpa only [Function.comp_def, id, armObs_def] using
    hF.comp ((measurable_pullCount hA a t).prodMk measurable_id)

variable [Countable α] [MeasurableSingletonClass α]

/-- In a run against `Environment.bandit ν`, extended by the auxiliary stream, the rewards by count
of all arms, arranged as a reward stream `(i, b) ↦ rewardByCount A R b (i + 1)`, have law
`streamMeasure ν`: the reward of the `(i + 1)`-th pull of arm `b` plays the role of the `i`-th
reward of `b` in the stream model. -/
lemma hasLaw_rewardByCount_streamMeasure (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) :
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

omit [DecidableEq α] [Countable α] [MeasurableSingletonClass α] in
/-- In LML's reward stream model, the reward sequences `(ω i a)_i` of the arms `a` are
independent. -/
theorem iIndepFun_arm_streamMeasure {𝓡 : Type*} [MeasurableSpace 𝓡] (ν : Kernel α 𝓡)
    [IsMarkovKernel ν] :
    iIndepFun (fun a (ω : ℕ → α → 𝓡) i ↦ ω i a) (streamMeasure ν) := by
  -- the entries `ω i a`, indexed by `(a, i) : Σ _ : α, ℕ`, are independent with laws `ν a`
  have he : Function.Injective fun p : (_ : α) × ℕ ↦ (p.2, p.1) := by
    rintro ⟨a, i⟩ ⟨b, j⟩ ⟨⟩
    rfl
  have h_entries : HasLaw (fun (ω : ℕ → α → 𝓡) (p : (_ : α) × ℕ) ↦ ω p.2 p.1)
      (Measure.infinitePi fun p : (_ : α) × ℕ ↦ ν p.1) (streamMeasure ν) :=
    ((iIndepFun_eval_streamMeasure ν).precomp he).hasLaw_infinitePi
      (fun p ↦ hasLaw_eval_eval_streamMeasure ν p.2 p.1)
      (Measurable.of_eval fun p ↦
        (measurable_pi_apply p.1).comp (measurable_pi_apply p.2)).aemeasurable
  -- so the array of the reward sequences of the arms has law `⨂ a, ⨂ i, ν a`
  have h_arms : HasLaw (fun (ω : ℕ → α → 𝓡) a i ↦ ω i a)
      (Measure.infinitePi fun a : α ↦ Measure.infinitePi fun _ : ℕ ↦ ν a) (streamMeasure ν) := by
    have h := (hasLaw_map (P := Measure.infinitePi fun p : (_ : α) × ℕ ↦ ν p.1)
      (MeasurableEquiv.piCurry fun (_ : α) (_ : ℕ) ↦ 𝓡).measurable.aemeasurable).comp h_entries
    -- `Sigma.curry` arranges the entries indexed by `Σ _ : α, ℕ` as the array of the arms
    rwa [Measure.infinitePi_map_piCurry (μ := fun a (_ : ℕ) ↦ ν a), MeasurableEquiv.coe_piCurry,
      Function.comp_def] at h
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun a ↦ by fun_prop, h_arms.map_eq]
  congr 1
  ext a : 1
  rw [← (hasLaw_eval_infinitePi _ a).comp h_arms |>.map_eq, Function.comp_def]

/-- **Counting transfer of the observations to the reward stream, weighted form.** In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, for measurable functions
`g s ≥ 0` of `s` observations, the expected sum over the rounds `t < n` that pull arm `a` of `g` at
the previous observations of `a` is at most `∑ s < n, E[g s (X₀, …, X_{s-1})]` for an i.i.d.
sequence `X` with law `ν a`, the rewards of `a` in the stream model `streamMeasure ν`. -/
theorem sum_setLIntegral_action_eq_pullCount_armObs_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (n : ℕ)
    {g : (s : ℕ) → (Fin s → ℝ) → ℝ≥0∞} (hg : ∀ s, Measurable (g s)) :
    ∑ t ∈ range n, ∫⁻ ω in A t ⁻¹' {a}, g (pullCount A a t ω) (armObs A R a t ω) ∂P ≤
      ∑ s ∈ range n, ∫⁻ x, g s (fun i ↦ x i a) ∂(streamMeasure ν) := by
  classical
  have hA := h.measurable_action
  -- the weight of round `t`, and the weight of the first `s` rewards of `a` in a stream
  set f : ℕ → Ω → ℝ≥0∞ := fun t ↦ (A t ⁻¹' {a}).indicator
    fun ω ↦ g (pullCount A a t ω) (armObs A R a t ω)
  set G : ℕ → (ℕ → α → ℝ) → ℝ≥0∞ := fun s x ↦ g s (fun i ↦ x i a)
  have hf t : Measurable (f t) :=
    (measurable_comp_pullCount_armObs hA h.measurable_feedback hg a t).indicator
      (hA t (measurableSet_singleton a))
  have hG s : Measurable (G s) := (hg s).comp (by fun_prop)
  have hZ := hasLaw_rewardByCount_streamMeasure h
  set Z : Ω × (ℕ → α → ℝ) → ℕ → α → ℝ := fun ω i b ↦ rewardByCount A R b (i + 1) ω
  -- pathwise, the rounds that pull `a` see the pull counts `0, 1, …` once each, and their
  -- observations are rewards by count
  have h_path (ω : Ω × (ℕ → α → ℝ)) :
      ∑ t ∈ range n, f t ω.1 = ∑ s ∈ range (pullCount A a n ω.1), G s (Z ω) := by
    rw [← sum_range_ite_action_eq]
    refine sum_congr rfl fun t _ ↦ ?_
    have h_obs : armObs A R a t ω.1 = fun i : Fin _ ↦ Z ω i a :=
      funext (armObs_eq_rewardByCount R a t ω)
    by_cases hat : A t ω.1 = a <;> simp [f, G, hat, h_obs]
  calc ∑ t ∈ range n, ∫⁻ ω in A t ⁻¹' {a}, g (pullCount A a t ω) (armObs A R a t ω) ∂P
  _ = ∑ t ∈ range n, ∫⁻ ω, f t ω.1 ∂(P.prod (streamMeasure ν)) := by
    refine sum_congr rfl fun t _ ↦ ?_
    rw [lintegral_prod (fun ω ↦ f t ω.1) ((hf t).comp measurable_fst).aemeasurable]
    simp [f, lintegral_indicator (hA t (measurableSet_singleton a))]
  _ = ∫⁻ ω, ∑ t ∈ range n, f t ω.1 ∂(P.prod (streamMeasure ν)) :=
    (lintegral_finsetSum _ fun t _ ↦ (hf t).comp measurable_fst).symm
  _ ≤ ∫⁻ ω, ∑ s ∈ range n, G s (Z ω) ∂(P.prod (streamMeasure ν)) := by
    refine lintegral_mono fun ω ↦ (h_path ω).trans_le ?_
    exact sum_le_sum_of_subset (range_subset_range.mpr (pullCount_le a n ω.1))
  _ = ∑ s ∈ range n, ∫⁻ ω, G s (Z ω) ∂(P.prod (streamMeasure ν)) :=
    lintegral_finsetSum' _ fun s _ ↦ (hG s).comp_aemeasurable hZ.aemeasurable
  _ = ∑ s ∈ range n, ∫⁻ x, g s (fun i ↦ x i a) ∂(streamMeasure ν) :=
    sum_congr rfl fun s _ ↦ hZ.lintegral_comp (hG s).aemeasurable

/-- **Counting transfer of the observations to the reward stream.** In a run of any algorithm
against the stochastic bandit `Environment.bandit ν`, for a property `p s` of `s` observations,
measurable for each `s`, the expected number of rounds `t < n` at which arm `a` is pulled while
`p` holds for its previous observations is at most `∑ s < n, P(p s (X₀, …, X_{s-1}))` for an
i.i.d. sequence `X` with law `ν a`, the rewards of `a` in the stream model `streamMeasure ν`. -/
theorem sum_measure_action_eq_and_pullCount_armObs_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (n : ℕ)
    {p : (s : ℕ) → (Fin s → ℝ) → Prop} (hp : ∀ s, Measurable (p s)) :
    ∑ t ∈ range n, P {ω | A t ω = a ∧ p (pullCount A a t ω) (armObs A R a t ω)} ≤
      ∑ s ∈ range n, streamMeasure ν {x | p s (fun i ↦ x i a)} := by
  -- the weighted transfer with the indicator of `p` as the weight
  set B : (s : ℕ) → Set (Fin s → ℝ) := fun s ↦ {y | p s y}
  have hB s : MeasurableSet (B s) := measurableSet_setOfPred.mpr (hp s)
  refine (sum_le_sum fun t _ ↦ ?_).trans ((sum_setLIntegral_action_eq_pullCount_armObs_le h a n
    (g := fun s y ↦ (B s).indicator 1 y) fun s ↦ measurable_one.indicator (hB s)).trans
      (sum_le_sum fun s _ ↦ ?_))
  · have hE : MeasurableSet {ω | p (pullCount A a t ω) (armObs A R a t ω)} :=
      measurableSet_setOfPred.mpr
        (measurable_comp_pullCount_armObs h.measurable_action h.measurable_feedback hp a t)
    calc P {ω | A t ω = a ∧ p (pullCount A a t ω) (armObs A R a t ω)}
    _ = P ({ω | p (pullCount A a t ω) (armObs A R a t ω)} ∩ A t ⁻¹' {a}) := by
      congr 1 with ω
      simp [and_comm]
    _ = ∫⁻ ω in A t ⁻¹' {a}, (B _).indicator 1 (armObs A R a t ω) ∂P := by
      rw [← Measure.restrict_apply hE, ← lintegral_indicator_one hE]
      refine lintegral_congr fun ω ↦ ?_
      by_cases hpt : p (pullCount A a t ω) (armObs A R a t ω) <;> simp [B, hpt]
    _ ≤ _ := le_rfl
  · have hE : MeasurableSet {x : ℕ → α → ℝ | p s (fun i ↦ x i a)} := (hB s).preimage (by fun_prop)
    rw [← lintegral_indicator_one hE]
    refine lintegral_mono fun x ↦ ?_
    by_cases hpx : p s (fun i ↦ x i a) <;> simp [B, hpx]

/-- **Counting transfer to the reward stream, weighted form.** In a run of any algorithm against the
stochastic bandit `Environment.bandit ν`, for a measurable `g ≥ 0` of a number of pulls and a sum of
rewards, the expected sum over the rounds `t < n` that pull arm `a` of `g` at the number of previous
pulls and the sum of the previous rewards of `a` is at most
`∑ s < n, E[g s (X₀ + ⋯ + X_{s-1})]` for an i.i.d. sequence `X` with law `ν a`, the rewards of `a`
in the stream model `streamMeasure ν`. -/
theorem sum_setLIntegral_action_eq_pullCount_sumRewards_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (n : ℕ) {g : ℕ → ℝ → ℝ≥0∞}
    (hg : Measurable fun q : ℕ × ℝ ↦ g q.1 q.2) :
    ∑ t ∈ range n, ∫⁻ ω in A t ⁻¹' {a}, g (pullCount A a t ω) (sumRewards A R a t ω) ∂P ≤
      ∑ s ∈ range n, ∫⁻ x, g s (∑ i ∈ range s, x i a) ∂(streamMeasure ν) := by
  -- the observation form for the weights `g s (y₀ + ⋯ + y_{s-1})`
  have h_obs := sum_setLIntegral_action_eq_pullCount_armObs_le h a n
    (g := fun s y ↦ g s (∑ i, y i)) fun s ↦ hg.of_uncurry_left.comp (by fun_prop)
  simp only [sum_armObs] at h_obs
  refine h_obs.trans_eq (sum_congr rfl fun s _ ↦ lintegral_congr fun x ↦ ?_)
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ x i a)]

/-- **Counting transfer to the reward stream.** In a run of any algorithm against the stochastic
bandit `Environment.bandit ν`, the expected number of rounds `t < n` at which arm `a` is pulled
while `p` holds for its number of previous pulls and the sum of its previous rewards is at most
`∑ s < n, P(p s (X₀ + ⋯ + X_{s-1}))` for an i.i.d. sequence `X` with law `ν a`, the rewards of `a`
in the stream model `streamMeasure ν`. -/
theorem sum_measure_action_eq_and_pullCount_sumRewards_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (n : ℕ)
    (hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2) :
    ∑ t ∈ range n, P {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      ∑ s ∈ range n, streamMeasure ν {ω | p s (∑ i ∈ range s, ω i a)} := by
  -- the observation form for the property `p s (y₀ + ⋯ + y_{s-1})`
  have h_obs := sum_measure_action_eq_and_pullCount_armObs_le h a n
    (p := fun s y ↦ p s (∑ i, y i)) fun s ↦ hp.of_uncurry_left.comp (by fun_prop)
  simp only [sum_armObs] at h_obs
  refine h_obs.trans_eq ?_
  simp only [Finset.sum_range]

/-- Real-valued form of `sum_measure_action_eq_and_pullCount_sumRewards_le`: in a run against
`Environment.bandit ν`, the expected number of rounds `t < n` at which arm `a` is pulled while `p`
holds for its number of previous pulls and the sum of its previous rewards is at most
`∑ s < n, P(p s (X₀ + ⋯ + X_{s-1}))` for the i.i.d. rewards `X` of `a` in the stream model. -/
theorem sum_measureReal_action_eq_and_pullCount_sumRewards_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (n : ℕ)
    (hp : Measurable fun q : ℕ × ℝ ↦ p q.1 q.2) :
    ∑ t ∈ range n, P.real {ω | A t ω = a ∧ p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      ∑ s ∈ range n, (streamMeasure ν).real {ω | p s (∑ i ∈ range s, ω i a)} := by
  simp_rw [measureReal_def]
  rw [← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _,
    ← ENNReal.toReal_sum fun _ _ ↦ measure_ne_top _ _]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _)
    (sum_measure_action_eq_and_pullCount_sumRewards_le h a n hp)

/-- **Joint event transfer of the observations to the reward stream.** In a run of any algorithm
against the stochastic bandit `Environment.bandit ν`, the probability that `q` holds at some round
for the numbers of previous pulls of all arms and their previous observations is at most the
probability that `q s (fun a ↦ (X₀ a, …, X_{s a - 1} a))` holds for some numbers of pulls
`s : α → ℕ`, for the i.i.d. rewards `X` of the stream model `streamMeasure ν`. The predicate `q`
need not be measurable: for a non-measurable event, both sides are outer measures. -/
theorem measure_exists_pullCount_armObs_pi_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (q : (s : α → ℕ) → ((a : α) → Fin (s a) → ℝ) → Prop) :
    P {ω | ∃ t, q (fun a ↦ pullCount A a t ω) (fun a ↦ armObs A R a t ω)} ≤
      streamMeasure ν {x | ∃ s : α → ℕ, q s (fun a i ↦ x i a)} := by
  set Z : Ω × (ℕ → α → ℝ) → ℕ → α → ℝ := fun ω i b ↦ rewardByCount A R b (i + 1) ω
  have hZ : HasLaw Z (streamMeasure ν) (P.prod (streamMeasure ν)) :=
    hasLaw_rewardByCount_streamMeasure h
  calc P {ω | ∃ t, q (fun a ↦ pullCount A a t ω) (fun a ↦ armObs A R a t ω)}
  _ = P.prod (streamMeasure ν) (Prod.fst ⁻¹'
      {ω | ∃ t, q (fun a ↦ pullCount A a t ω) (fun a ↦ armObs A R a t ω)}) := by
    rw [Measure.prod_preimage_fst, measure_univ, one_mul]
  _ ≤ P.prod (streamMeasure ν) (Z ⁻¹' {x | ∃ s : α → ℕ, q s (fun a i ↦ x i a)}) := by
    -- at round `t`, the observations of each arm `a` are its first `pullCount A a t ω` rewards
    -- by count
    refine measure_mono fun ω ⟨t, ht⟩ ↦ ⟨fun a ↦ pullCount A a t ω.1, ?_⟩
    have h_obs : (fun a ↦ armObs A R a t ω.1) = fun a (i : Fin _) ↦ Z ω i a :=
      funext fun a ↦ funext (armObs_eq_rewardByCount R a t ω)
    rwa [h_obs] at ht
  _ ≤ streamMeasure ν {x | ∃ s : α → ℕ, q s (fun a i ↦ x i a)} :=
    (Measure.le_map_apply hZ.aemeasurable _).trans_eq (by rw [hZ.map_eq])

omit [Countable α] in
/-- **Joint event transfer of the observations to the reward stream, up to a horizon.** For
finitely many arms, in a run of any algorithm against the stochastic bandit
`Environment.bandit ν`, the probability that `q` holds at some round `t < n` for the numbers of
previous pulls of all arms and their previous observations is at most the probability that
`q s (fun a ↦ (X₀ a, …, X_{s a - 1} a))` holds for some numbers of pulls `s : α → ℕ` with
`∑ a, s a < n`, for the i.i.d. rewards `X` of the stream model `streamMeasure ν`. -/
theorem measure_exists_lt_pullCount_armObs_pi_le [Fintype α]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (n : ℕ)
    (q : (s : α → ℕ) → ((a : α) → Fin (s a) → ℝ) → Prop) :
    P {ω | ∃ t < n, q (fun a ↦ pullCount A a t ω) (fun a ↦ armObs A R a t ω)} ≤
      streamMeasure ν {x | ∃ s : α → ℕ, ∑ a, s a < n ∧ q s (fun a i ↦ x i a)} := by
  calc P {ω | ∃ t < n, q (fun a ↦ pullCount A a t ω) (fun a ↦ armObs A R a t ω)}
  _ ≤ P {ω | ∃ t, ∑ a, pullCount A a t ω < n ∧
      q (fun a ↦ pullCount A a t ω) (fun a ↦ armObs A R a t ω)} :=
    -- at round `t`, the arms have been pulled `t` times in total
    measure_mono fun ω ⟨t, ht, hqt⟩ ↦ ⟨t, by rwa [sum_pullCount], hqt⟩
  _ ≤ streamMeasure ν {x | ∃ s : α → ℕ, ∑ a, s a < n ∧ q s (fun a i ↦ x i a)} :=
    measure_exists_pullCount_armObs_pi_le h fun s y ↦ ∑ a, s a < n ∧ q s y

/-- **Event transfer of the observations to the reward stream.** In a run of any algorithm against
the stochastic bandit `Environment.bandit ν`, the probability that `p` holds for the previous
observations of arm `a` at some round is at most the probability that `p s (X₀, …, X_{s-1})` holds
for some `s`, for the i.i.d. rewards `X` of `a` in the stream model `streamMeasure ν`. -/
theorem measure_exists_pullCount_armObs_le (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (a : α) (p : (s : ℕ) → (Fin s → ℝ) → Prop) :
    P {ω | ∃ t, p (pullCount A a t ω) (armObs A R a t ω)} ≤
      streamMeasure ν {x | ∃ s, p s (fun i ↦ x i a)} :=
  (measure_exists_pullCount_armObs_pi_le h fun s y ↦ p (s a) (y a)).trans
    (measure_mono fun _ ⟨s, hs⟩ ↦ ⟨s a, hs⟩)

/-- **Event transfer of the observations to the reward stream, up to a horizon.** In a run of any
algorithm against the stochastic bandit `Environment.bandit ν`, the probability that `p` holds for
the previous observations of arm `a` at some round `t < n` is at most the probability that
`p s (X₀, …, X_{s-1})` holds for some `s < n`, for the i.i.d. rewards `X` of `a` in the stream
model `streamMeasure ν`. -/
theorem measure_exists_lt_pullCount_armObs_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (n : ℕ)
    (p : (s : ℕ) → (Fin s → ℝ) → Prop) :
    P {ω | ∃ t < n, p (pullCount A a t ω) (armObs A R a t ω)} ≤
      streamMeasure ν {x | ∃ s < n, p s (fun i ↦ x i a)} := by
  calc P {ω | ∃ t < n, p (pullCount A a t ω) (armObs A R a t ω)}
  _ ≤ P {ω | ∃ t, pullCount A a t ω < n ∧ p (pullCount A a t ω) (armObs A R a t ω)} :=
    -- at round `t < n`, arm `a` has been pulled `pullCount A a t ω ≤ t < n` times
    measure_mono fun ω ⟨t, ht, hpt⟩ ↦ ⟨t, (pullCount_le a t ω).trans_lt ht, hpt⟩
  _ ≤ streamMeasure ν {x | ∃ s < n, p s (fun i ↦ x i a)} :=
    measure_exists_pullCount_armObs_le h a fun s y ↦ s < n ∧ p s y

/-- **Joint event transfer to the reward stream.** In a run of any algorithm against the
stochastic bandit `Environment.bandit ν`, the probability that `q` holds at some round for the
numbers of previous pulls of all arms and the sums of their previous rewards is at most the
probability that `q s (fun a ↦ X₀ a + ⋯ + X_{s a - 1} a)` holds for some numbers of pulls
`s : α → ℕ`, for the i.i.d. rewards `X` of the stream model `streamMeasure ν`. The predicate `q`
need not be measurable: for a non-measurable event, both sides are outer measures. -/
theorem measure_exists_pullCount_sumRewards_pi_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (q : (α → ℕ) → (α → ℝ) → Prop) :
    P {ω | ∃ t, q (fun a ↦ pullCount A a t ω) (fun a ↦ sumRewards A R a t ω)} ≤
      streamMeasure ν {ω | ∃ s : α → ℕ, q s (fun a ↦ ∑ i ∈ range (s a), ω i a)} := by
  -- the observation form for the event `q s (fun a ↦ y a 0 + ⋯ + y a (s a - 1))`
  have h_obs := measure_exists_pullCount_armObs_pi_le h fun s y ↦ q s fun a ↦ ∑ i, y a i
  simp only [sum_armObs] at h_obs
  refine h_obs.trans (measure_mono fun x ⟨s, hs⟩ ↦ ⟨s, ?_⟩)
  simpa only [Finset.sum_range] using hs

omit [Countable α] in
/-- **Joint event transfer to the reward stream, up to a horizon.** For finitely many arms, in a
run of any algorithm against the stochastic bandit `Environment.bandit ν`, the probability that `q`
holds at some round `t < n` for the numbers of previous pulls of all arms and the sums of their
previous rewards is at most the probability that `q s (fun a ↦ X₀ a + ⋯ + X_{s a - 1} a)` holds
for some numbers of pulls `s : α → ℕ` with `∑ a, s a < n`, for the i.i.d. rewards `X` of the stream
model `streamMeasure ν`. -/
theorem measure_exists_lt_pullCount_sumRewards_pi_le [Fintype α]
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (n : ℕ) (q : (α → ℕ) → (α → ℝ) → Prop) :
    P {ω | ∃ t < n, q (fun a ↦ pullCount A a t ω) (fun a ↦ sumRewards A R a t ω)} ≤
      streamMeasure ν
        {ω | ∃ s : α → ℕ, ∑ a, s a < n ∧ q s (fun a ↦ ∑ i ∈ range (s a), ω i a)} := by
  -- the observation form for the event `q s (fun a ↦ y a 0 + ⋯ + y a (s a - 1))`
  have h_obs := measure_exists_lt_pullCount_armObs_pi_le h n fun s y ↦ q s fun a ↦ ∑ i, y a i
  simp only [sum_armObs] at h_obs
  refine h_obs.trans_eq ?_
  simp only [Finset.sum_range]

/-- **Event transfer to the reward stream.** In a run of any algorithm against the stochastic
bandit `Environment.bandit ν`, the probability that `p` holds for the number of previous pulls of
arm `a` and the sum of its previous rewards at some round is at most the probability that
`p s (X₀ + ⋯ + X_{s-1})` holds for some `s`, for the i.i.d. rewards `X` of `a` in the stream model
`streamMeasure ν`. This is the form used for confidence bounds valid at all rounds at once. -/
theorem measure_exists_pullCount_sumRewards_le (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (a : α) (p : ℕ → ℝ → Prop) :
    P {ω | ∃ t, p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      streamMeasure ν {ω | ∃ s, p s (∑ i ∈ range s, ω i a)} := by
  -- the observation form for the event `p s (y₀ + ⋯ + y_{s-1})`
  have h_obs := measure_exists_pullCount_armObs_le h a fun s y ↦ p s (∑ i, y i)
  simp only [sum_armObs] at h_obs
  refine h_obs.trans_eq ?_
  simp only [Finset.sum_range]

/-- **Event transfer to the reward stream, up to a horizon.** In a run of any algorithm against the
stochastic bandit `Environment.bandit ν`, the probability that `p` holds for the number of previous
pulls of arm `a` and the sum of its previous rewards at some round `t < n` is at most the
probability that `p s (X₀ + ⋯ + X_{s-1})` holds for some `s < n`, for the i.i.d. rewards `X` of `a`
in the stream model `streamMeasure ν`. -/
theorem measure_exists_lt_pullCount_sumRewards_le
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (n : ℕ) (p : ℕ → ℝ → Prop) :
    P {ω | ∃ t < n, p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      streamMeasure ν {ω | ∃ s < n, p s (∑ i ∈ range s, ω i a)} := by
  -- the observation form for the event `p s (y₀ + ⋯ + y_{s-1})`
  have h_obs := measure_exists_lt_pullCount_armObs_le h a n fun s y ↦ p s (∑ i, y i)
  simp only [sum_armObs] at h_obs
  refine h_obs.trans_eq ?_
  simp only [Finset.sum_range]

/-- **Union bound over the number of pulls.** In a run of any algorithm against the stochastic
bandit `Environment.bandit ν`, let `p s x` be a property of a number of pulls `s` and a sum
of rewards `x` that fails for `s = 0`. The probability that `p` holds at round `t` for the number
of pulls and the sum of rewards of arm `a` is at most the sum over `s < t` of the probabilities
that `p (s + 1)` holds for the sum of the first `s + 1` rewards of `a` in the i.i.d. reward stream
model. -/
theorem measureReal_pullCount_sumRewards_le_sum (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P)
    (a : α) (p : ℕ → ℝ → Prop) (hp0 : ∀ x, ¬ p 0 x) (t : ℕ) :
    P.real {ω | p (pullCount A a t ω) (sumRewards A R a t ω)} ≤
      ∑ s ∈ range t, (streamMeasure ν).real {ω | p (s + 1) (∑ i ∈ range (s + 1), ω i a)} := by
  -- the event of round `t` is transferred to the reward stream, where a union bound over the
  -- number of pulls applies, and the term of `0` pulls vanishes
  calc P.real {ω | p (pullCount A a t ω) (sumRewards A R a t ω)}
  _ ≤ P.real {ω | ∃ t' < t + 1, p (pullCount A a t' ω) (sumRewards A R a t' ω)} :=
    measureReal_mono fun ω hω ↦ ⟨t, lt_add_one t, hω⟩
  _ ≤ (streamMeasure ν).real {ω | ∃ s < t + 1, p s (∑ i ∈ range s, ω i a)} :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_exists_lt_pullCount_sumRewards_le h a (t + 1) p)
  _ ≤ (streamMeasure ν).real (⋃ s ∈ range (t + 1), {ω | p s (∑ i ∈ range s, ω i a)}) := by
    refine measureReal_mono (fun ω ⟨s, hs, hω⟩ ↦ ?_) (measure_ne_top _ _)
    exact Set.mem_biUnion (mem_range.mpr hs) hω
  _ ≤ ∑ s ∈ range (t + 1), (streamMeasure ν).real {ω | p s (∑ i ∈ range s, ω i a)} :=
    measureReal_biUnion_finset_le _ _
  _ = ∑ s ∈ range t, (streamMeasure ν).real {ω | p (s + 1) (∑ i ∈ range (s + 1), ω i a)} := by
    rw [sum_range_succ']
    simp [hp0]

/-- **Union bound over the number of pulls, for the empirical mean.** In a run of any algorithm
against the stochastic bandit `Environment.bandit ν`, let `q s x` be a property of a number of pulls
`s` and an empirical mean `x`, and let `g s` bound, for every `s ≠ 0`, the probability that `q s`
holds for the empirical mean of the first `s` rewards of arm `a` in the i.i.d. reward stream model.
Then the probability that at round `t` the arm `a` has been pulled and `q` holds for its number of
pulls and its empirical mean is at most `∑_{s < t} g (s + 1)`. -/
theorem measureReal_pullCount_ne_zero_and_empMean_le_sum
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (a : α) (q : ℕ → ℝ → Prop) {g : ℕ → ℝ}
    (hg : ∀ s ≠ 0, (streamMeasure ν).real {ω | q s ((∑ i ∈ range s, ω i a) / s)} ≤ g s)
    (t : ℕ) :
    P.real {ω | pullCount A a t ω ≠ 0 ∧ q (pullCount A a t ω) (empMean A R a t ω)} ≤
      ∑ s ∈ range t, g (s + 1) := by
  -- the empirical mean is the sum of rewards divided by the number of pulls, and the event of
  -- round `t` is transferred to the reward stream with a union bound over the number of pulls
  calc P.real {ω | pullCount A a t ω ≠ 0 ∧ q (pullCount A a t ω) (empMean A R a t ω)}
  _ ≤ ∑ s ∈ range t, (streamMeasure ν).real
      {ω | s + 1 ≠ 0 ∧ q (s + 1) ((∑ i ∈ range (s + 1), ω i a) / (s + 1 : ℕ))} := by
    refine le_trans (measureReal_mono fun ω hω ↦ ?_) (measureReal_pullCount_sumRewards_le_sum h a
      (fun s x ↦ s ≠ 0 ∧ q s (x / s)) (fun _ h0 ↦ h0.1 rfl) t)
    simp only [Set.mem_ofPred_eq, empMean] at hω
    exact hω
  _ ≤ ∑ s ∈ range t, g (s + 1) := by
    refine sum_le_sum fun s _ ↦ le_trans (measureReal_mono fun ω hω ↦ ?_) (hg _ s.succ_ne_zero)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact hω.2

/-- **The strong law of large numbers for the empirical means** of a run of any algorithm against
the stochastic bandit `Environment.bandit ν` with integrable rewards: almost surely, for every arm
`a` whose number of pulls tends to infinity, the empirical mean of `a` converges to the mean of
`ν a`. -/
theorem ae_tendsto_empMean_of_tendsto_pullCount
    (h : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hν : ∀ a, Integrable id (ν a)) :
    ∀ᵐ ω ∂P, ∀ a, Tendsto (fun t ↦ pullCount A a t ω) atTop atTop →
      Tendsto (fun t ↦ empMean A R a t ω) atTop (𝓝 (∫ x, x ∂(ν a))) := by
  rw [ae_all_iff]
  intro a
  -- The rewards by count of `a` are i.i.d. with law `ν a` under `P.prod (streamMeasure ν)`.
  have h_id : IdentDistrib (rewardByCount A R a (0 + 1)) id (P.prod (streamMeasure ν)) (ν a) :=
    identDistrib_rewardByCount_id h a 1 one_ne_zero
  have h_slln := strong_law_ae_real (fun m ↦ rewardByCount A R a (m + 1))
    (h_id.integrable_iff.2 (hν a))
    (fun _ _ hij ↦ (iIndepFun_rewardByCount_add_one_action h a).indepFun hij)
    (fun m ↦ (hasLaw_rewardByCount_add_one h a m).identDistrib (hasLaw_rewardByCount_add_one h a 0))
  rw [h_id.integral_eq] at h_slln
  -- The event depends only on the run, the first coordinate.
  filter_upwards [Measure.ae_ae_of_ae_prod h_slln] with ω hω hN
  obtain ⟨y, hy⟩ := hω.exists
  refine (hy.comp hN).congr fun t ↦ ?_
  rw [Function.comp_apply, empMean, sumRewards_eq_sum_range_rewardByCount a t (ω, y)]

end LMLExplore
