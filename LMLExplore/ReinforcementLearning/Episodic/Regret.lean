/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.EpisodeEnv
public import LMLExplore.MarkovDecisionProcess.Episodic.Optimal
import LMLExplore.Probability.HasCondDistrib
import LMLExplore.SequentialLearning.BanditFeedback

/-!
# The regret of online episodic learning

A learner in an episodic MDP `M` with horizon `H` plays, at each episode `k`, an `H`-step policy
`π_k` chosen from the previous episodes, from an initial state drawn from the initial law `μ`. Its
regret after `K` episodes compares the optimal value `V*_0` with the values `V^{π_k}_0` of the
policies it plays. It comes in two forms:
* the pseudo-regret `∑_{k < K} (∫ V*_0 dμ - ∫ V^{π_k}_0 dμ)`, which averages the gap
  `V*_0 - V^{π_k}_0` of each policy over the initial law (`pseudoRegret`). Along a run, it is a
  random variable through the policies `π_k`, and its expectation is the expected regret
  (`expectedRegret`);
* the regret at the realized initial states `s_k` of the episodes,
  `∑_{k < K} (V*_0 - V^{π_k}_0)(s_k)` (`regret`). This is the form in which the regret bounds of
  optimistic algorithms are proved, since their analysis follows the realized episodes.

Given the previous episodes and the policy `π_k`, the initial state `s_k` has law `μ`, so the
difference of the two forms is a sum of martingale differences. For rewards in `[0, 1]`, each gap
lies in `[0, H]`, and the Azuma–Hoeffding inequality shows that, with probability at least
`1 - δ`, the two forms differ by at most `H √(K log (2 / δ) / 2)`, which is at most the bound
`H √(2 K log (2 / δ))` used in the literature. Their expectations are equal. These statements
transfer regret bounds proved at the realized initial states to the pseudo-regret and to the
expected regret. They hold along every run of the episode-level environments `M.statesEnv H μ`
and `M.episodeEnv H μ`, in which the realized initial state of episode `k` is the first state
`Y k 0` (respectively `(Y k).1 0`) of the feedback of round `k`.

## Main definitions

* `Learning.MDP.Episodic.EpisodicMDP.pseudoRegret M H μ π K`: the pseudo-regret of the policies
  `π k`, `k < K`, from the initial law `μ`.
* `Learning.MDP.Episodic.EpisodicMDP.regret M H π s K`: the regret of the policies `π k` at the
  initial states `s k`.
* `Learning.MDP.Episodic.EpisodicMDP.expectedRegret M H μ P X K`: the expected regret of the
  policies `X k` of a run under `P`, the expectation of the pseudo-regret.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.measureReal_le_abs_regret_sub_pseudoRegret_le_statesEnv`,
  `Learning.MDP.Episodic.EpisodicMDP.measureReal_le_abs_regret_sub_pseudoRegret_le_episodeEnv`:
  the tail bound `P(ε ≤ |regret - pseudoRegret|) ≤ 2 exp (-2 ε ^ 2 / (K H ^ 2))`.
* `Learning.MDP.Episodic.EpisodicMDP.le_measureReal_abs_regret_sub_pseudoRegret_le_statesEnv`,
  `Learning.MDP.Episodic.EpisodicMDP.le_measureReal_abs_regret_sub_pseudoRegret_le_episodeEnv`:
  with probability at least `1 - δ`, `|regret - pseudoRegret| ≤ H √(K log (2 / δ) / 2)`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_regret_statesEnv`,
  `Learning.MDP.Episodic.EpisodicMDP.integral_regret_episodeEnv`: the expectation of the regret at
  the realized initial states is the expected regret.

## References

* [AJKS] A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, version of 31 January 2022, Chapter 7 (episodic regret).
* [JABJ18] C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, *Is Q-learning provably efficient?*,
  NeurIPS 2018, arXiv:1807.03765, Section 2 (the regret at the initial states of the episodes).
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  (M : EpisodicMDP 𝓢 𝓐) (H : ℕ)

/-! ### Definitions -/

section Defs

variable [Countable 𝓢] [MeasurableSingletonClass 𝓢] [Nonempty 𝓐]

/-- The **pseudo-regret** after `K` episodes of the `H`-step policies `π k`, `k < K`, from the
initial law `μ`: `∑_{k < K} (∫ V*_0 dμ - ∫ V^{π_k}_0 dμ)`. -/
noncomputable def pseudoRegret (μ : Measure 𝓢) (π : ℕ → Policy 𝓢 𝓐 H) (K : ℕ) : ℝ :=
  ∑ k ∈ range K, (∫ s, M.optValue H 0 s ∂μ -
    ∫ s, M.value H ((π k).toKernel fun _ ↦ measurable_of_countable _) 0 s ∂μ)

lemma pseudoRegret_def (μ : Measure 𝓢) (π : ℕ → Policy 𝓢 𝓐 H) (K : ℕ) :
    M.pseudoRegret H μ π K = ∑ k ∈ range K, (∫ s, M.optValue H 0 s ∂μ -
      ∫ s, M.value H ((π k).toKernel fun _ ↦ measurable_of_countable _) 0 s ∂μ) :=
  (rfl)

/-- The **regret at the initial states** `s k` after `K` episodes of the `H`-step policies `π k`:
`∑_{k < K} (V*_0 (s k) - V^{π_k}_0 (s k))`. Along a run, `s k` is the realized initial state of
the episode `k`. -/
noncomputable def regret (π : ℕ → Policy 𝓢 𝓐 H) (s : ℕ → 𝓢) (K : ℕ) : ℝ :=
  ∑ k ∈ range K, (M.optValue H 0 (s k) -
    M.value H ((π k).toKernel fun _ ↦ measurable_of_countable _) 0 (s k))

lemma regret_def (π : ℕ → Policy 𝓢 𝓐 H) (s : ℕ → 𝓢) (K : ℕ) :
    M.regret H π s K = ∑ k ∈ range K, (M.optValue H 0 (s k) -
      M.value H ((π k).toKernel fun _ ↦ measurable_of_countable _) 0 (s k)) :=
  (rfl)

/-- The **expected regret** after `K` episodes of a run under `P` whose episode `k` plays the
`H`-step policy `X k`: the expectation of the pseudo-regret of the policies `X k`. -/
noncomputable def expectedRegret {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure 𝓢)
    (P : Measure Ω) (X : ℕ → Ω → Policy 𝓢 𝓐 H) (K : ℕ) : ℝ :=
  ∫ ω, M.pseudoRegret H μ (fun k ↦ X k ω) K ∂P

lemma expectedRegret_def {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure 𝓢) (P : Measure Ω)
    (X : ℕ → Ω → Policy 𝓢 𝓐 H) (K : ℕ) :
    M.expectedRegret H μ P X K = ∫ ω, M.pseudoRegret H μ (fun k ↦ X k ω) K ∂P :=
  (rfl)

variable {M H} {μ : Measure 𝓢} {π : ℕ → Policy 𝓢 𝓐 H} {s : ℕ → 𝓢} {K : ℕ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → Policy 𝓢 𝓐 H}

@[simp]
lemma pseudoRegret_zero : M.pseudoRegret H μ π 0 = 0 := by
  simp [pseudoRegret_def]

lemma pseudoRegret_add_one : M.pseudoRegret H μ π (K + 1) = M.pseudoRegret H μ π K +
    (∫ s, M.optValue H 0 s ∂μ -
      ∫ s, M.value H ((π K).toKernel fun _ ↦ measurable_of_countable _) 0 s ∂μ) := by
  rw [pseudoRegret_def, pseudoRegret_def, sum_range_succ]

@[simp]
lemma regret_zero : M.regret H π s 0 = 0 := by
  simp [regret_def]

lemma regret_add_one : M.regret H π s (K + 1) = M.regret H π s K +
    (M.optValue H 0 (s K) -
      M.value H ((π K).toKernel fun _ ↦ measurable_of_countable _) 0 (s K)) := by
  rw [regret_def, regret_def, sum_range_succ]

@[simp]
lemma expectedRegret_zero : M.expectedRegret H μ P X 0 = 0 := by
  simp [expectedRegret_def]

/-! ### Bounds -/

variable [Countable 𝓐]

/-- For a finite initial law and bounded rewards, the pseudo-regret is the sum of the integrals of
the gaps `V*_0 - V^{π_k}_0`. -/
lemma pseudoRegret_eq_sum_integral_sub {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b))
    [IsFiniteMeasure μ] :
    M.pseudoRegret H μ π K = ∑ k ∈ range K, ∫ s, (M.optValue H 0 s -
      M.value H ((π k).toKernel fun _ ↦ measurable_of_countable _) 0 s) ∂μ := by
  rw [pseudoRegret_def]
  exact sum_congr rfl fun k _ ↦ (integral_sub (integrable_optValue hM 0)
    (integrable_value hM 0)).symm

/-- For bounded rewards, the regret at any initial states is nonnegative. -/
lemma regret_nonneg {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) : 0 ≤ M.regret H π s K :=
  sum_nonneg fun k _ ↦ sub_nonneg.2 (value_le_optValue hM 0 (s k))

/-- For bounded rewards and a finite initial law, the pseudo-regret is nonnegative. -/
lemma pseudoRegret_nonneg {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) [IsFiniteMeasure μ] :
    0 ≤ M.pseudoRegret H μ π K := by
  rw [pseudoRegret_eq_sum_integral_sub hM]
  exact sum_nonneg fun k _ ↦ integral_nonneg fun s ↦ sub_nonneg.2 (value_le_optValue hM 0 s)

/-- For bounded rewards and a finite initial law, the expected regret is nonnegative. -/
lemma expectedRegret_nonneg {a b : ℝ} (hM : M.RewardsIn (Set.Icc a b)) [IsFiniteMeasure μ] :
    0 ≤ M.expectedRegret H μ P X K :=
  integral_nonneg fun _ ↦ pseudoRegret_nonneg hM

variable (hM : M.RewardsIn (Set.Icc 0 1))
include hM

/-- For rewards in `[0, 1]`, the regret at any initial states after `K` episodes is at most
`K H`. -/
lemma regret_le : M.regret H π s K ≤ K * H := by
  refine (sum_le_sum fun k _ ↦ (optValue_sub_value_mem_Icc hM 0 (s k)).2).trans_eq ?_
  simp

/-- For rewards in `[0, 1]` and a probability initial law, the pseudo-regret after `K` episodes is
at most `K H`. -/
lemma pseudoRegret_le [IsProbabilityMeasure μ] : M.pseudoRegret H μ π K ≤ K * H := by
  rw [pseudoRegret_eq_sum_integral_sub hM]
  refine (sum_le_sum fun k _ ↦ ?_).trans_eq (by simp : ∑ _ ∈ range K, (H : ℝ) = K * H)
  refine (integral_mono_of_nonneg (.of_forall fun s ↦ (optValue_sub_value_mem_Icc hM 0 s).1)
    (integrable_const (H : ℝ)) (.of_forall fun s ↦ ?_)).trans_eq (by simp)
  simpa using (optValue_sub_value_mem_Icc hM 0 s).2

/-- For rewards in `[0, 1]` and probability measures `μ` and `P`, the expected regret after `K`
episodes is at most `K H`. -/
lemma expectedRegret_le [IsProbabilityMeasure μ] [IsProbabilityMeasure P] :
    M.expectedRegret H μ P X K ≤ K * H := by
  rw [expectedRegret_def]
  refine (integral_mono_of_nonneg (.of_forall fun _ ↦ pseudoRegret_nonneg hM)
    (integrable_const ((K : ℝ) * H)) (.of_forall fun _ ↦ pseudoRegret_le hM)).trans_eq ?_
  simp

end Defs

/-! ### Along runs of the episode-level environments -/

section Runs

variable [Finite 𝓢] [MeasurableSingletonClass 𝓢] [Countable 𝓐]
  [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] {M H} {μ : Measure 𝓢} [IsProbabilityMeasure μ]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → Policy 𝓢 𝓐 H} {K : ℕ}

section Bandit

/-! The two episode-level environments are stochastic bandits over the `H`-step policies, whose
feedback determines the initial state of the episode through a map `init`. -/

variable {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {κ : Kernel (Policy 𝓢 𝓐 H) 𝓨} [IsMarkovKernel κ]
  {alg : Algorithm Unit (Policy 𝓢 𝓐 H) 𝓨} {Y : ℕ → Ω → 𝓨} {init : 𝓨 → 𝓢}

/-- The gap `V*_0 - V^π_0` at the initial state read from a feedback. -/
private noncomputable def feedbackGap (M : EpisodicMDP 𝓢 𝓐) (H : ℕ) (init : 𝓨 → 𝓢)
    (p : Policy 𝓢 𝓐 H × 𝓨) : ℝ :=
  M.optValue H 0 (init p.2) -
    M.value H (p.1.toKernel fun _ ↦ measurable_of_countable _) 0 (init p.2)

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel κ] in
/-- For rewards in `[0, 1]`, the gap read from a feedback lies in `[0, H]`. -/
private lemma feedbackGap_mem_Icc (hM : M.RewardsIn (Set.Icc 0 1)) (p : Policy 𝓢 𝓐 H × 𝓨) :
    feedbackGap M H init p ∈ Set.Icc 0 (H : ℝ) := by
  rw [feedbackGap]
  simpa using optValue_sub_value_mem_Icc (H := H)
    (π := p.1.toKernel fun _ ↦ measurable_of_countable _) hM 0 (init p.2)

omit [IsMarkovKernel κ] in
private lemma measurable_feedbackGap (hinit : Measurable init) :
    Measurable (feedbackGap M H init) :=
  (measurable_of_countable fun q : Policy 𝓢 𝓐 H × 𝓢 ↦ M.optValue H 0 q.2 -
    M.value H (q.1.toKernel fun _ ↦ measurable_of_countable _) 0 q.2).comp
    (measurable_fst.prodMk (hinit.comp measurable_snd))

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel κ] in
/-- If the initial state read from the feedback has law `μ` under every `κ π`, the mean gap under
`κ π` is the integral of the gap of `π` over `μ`. -/
private lemma integral_feedbackGap (hM : M.RewardsIn (Set.Icc 0 1)) (hinit : Measurable init)
    (hκ : ∀ π, HasLaw init μ (κ π)) (π : Policy 𝓢 𝓐 H) :
    ∫ y, feedbackGap M H init (π, y) ∂(κ π) = ∫ s, M.optValue H 0 s ∂μ -
      ∫ s, M.value H (π.toKernel fun _ ↦ measurable_of_countable _) 0 s ∂μ := by
  rw [← integral_sub (integrable_optValue hM 0) (integrable_value hM 0), ← (hκ π).map_eq,
    integral_map hinit.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  simp only [feedbackGap]

omit [MeasurableSingletonClass 𝓐] [IsMarkovKernel κ] in
private lemma regret_sub_pseudoRegret_eq (hM : M.RewardsIn (Set.Icc 0 1))
    (hinit : Measurable init) (hκ : ∀ π, HasLaw init μ (κ π)) (ω : Ω) :
    M.regret H (X · ω) (fun k ↦ init (Y k ω)) K - M.pseudoRegret H μ (X · ω) K =
      -∑ k ∈ range K, (∫ y, feedbackGap M H init (X k ω, y) ∂(κ (X k ω)) -
        feedbackGap M H init (X k ω, Y k ω)) := by
  simp only [integral_feedbackGap hM hinit hκ]
  simp only [regret_def, pseudoRegret_def, feedbackGap, sum_sub_distrib]
  ring

private lemma measureReal_le_abs_regret_sub_pseudoRegret_le_bandit
    (hM : M.RewardsIn (Set.Icc 0 1)) (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (hinit : Measurable init) (hκ : ∀ π, HasLaw init μ (κ π)) (K : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤
        |M.regret H (X · ω) (fun k ↦ init (Y k ω)) K - M.pseudoRegret H μ (X · ω) K|} ≤
      2 * Real.exp (-2 * ε ^ 2 / (K * H ^ 2)) := by
  have h' := h.measureReal_le_abs_sum_integral_sub_le_bandit (g := fun _ ↦ feedbackGap M H init)
    (fun _ ↦ measurable_feedbackGap hinit) (a := fun _ ↦ 0) (b := fun _ ↦ (H : ℝ))
    (fun _ ↦ feedbackGap_mem_Icc hM) K hε
  simp only [sub_zero, sum_const, card_range, nsmul_eq_mul] at h'
  simpa only [regret_sub_pseudoRegret_eq hM hinit hκ, abs_neg] using h'

/-- With probability at least `1 - δ`, the regret at the realized initial states and the
pseudo-regret differ by at most `H √(K log (2 / δ) / 2)`. -/
private lemma le_measureReal_abs_regret_sub_pseudoRegret_le_bandit
    (hM : M.RewardsIn (Set.Icc 0 1)) (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P)
    (hinit : Measurable init) (hκ : ∀ π, HasLaw init μ (κ π)) (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | |M.regret H (X · ω) (fun k ↦ init (Y k ω)) K -
      M.pseudoRegret H μ (X · ω) K| ≤ H * √(K * Real.log (2 / δ) / 2)} := by
  have h' := h.le_measureReal_abs_sum_integral_sub_le_bandit
    (g := fun _ ↦ feedbackGap M H init) (fun _ ↦ measurable_feedbackGap hinit)
    (a := fun _ ↦ 0) (b := fun _ ↦ (H : ℝ)) (fun _ ↦ feedbackGap_mem_Icc hM) K hδ
  have hsqrt : √(K * H ^ 2 * Real.log (2 / δ) / 2) = H * √(K * Real.log (2 / δ) / 2) := by
    rw [show (K : ℝ) * H ^ 2 * Real.log (2 / δ) / 2 = H ^ 2 * (K * Real.log (2 / δ) / 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  simp only [sub_zero, sum_const, card_range, nsmul_eq_mul, hsqrt] at h'
  simpa only [regret_sub_pseudoRegret_eq hM hinit hκ, abs_neg] using h'

/-- Given the previous episodes, the regret at the realized initial states has the mean of the
pseudo-regret: their expectations are equal. -/
private lemma integral_regret_bandit (hM : M.RewardsIn (Set.Icc 0 1))
    (h : IsAlgEnvSeq O X Y alg (Environment.bandit κ) P) (hinit : Measurable init)
    (hκ : ∀ π, HasLaw init μ (κ π)) (K : ℕ) :
    ∫ ω, M.regret H (X · ω) (fun k ↦ init (Y k ω)) K ∂P = M.expectedRegret H μ P X K := by
  have hg := measurable_feedbackGap (M := M) (H := H) hinit
  have hcd := h.hasCondDistrib_feedback_bandit
  have hint : ∀ k, Integrable (fun ω ↦ feedbackGap M H init (X k ω, Y k ω)) P := fun k ↦
    .of_mem_Icc 0 H (hg.comp ((h.measurable_action k).prodMk
      (h.measurable_feedback k))).aemeasurable (.of_forall fun ω ↦ feedbackGap_mem_Icc hM _)
  have hint' : ∀ k, Integrable
      (fun ω ↦ ∫ y, feedbackGap M H init (X k ω, y) ∂(κ (X k ω))) P := fun k ↦
    (hcd k).integrable_integral_comp_prodMk hg.aestronglyMeasurable (hint k)
  have hreg : ∀ ω, M.regret H (X · ω) (fun k ↦ init (Y k ω)) K =
      ∑ k ∈ range K, feedbackGap M H init (X k ω, Y k ω) := fun ω ↦ by
    simp only [regret_def, feedbackGap]
  have hps : ∀ ω, M.pseudoRegret H μ (X · ω) K =
      ∑ k ∈ range K, ∫ y, feedbackGap M H init (X k ω, y) ∂(κ (X k ω)) := fun ω ↦ by
    simp_rw [integral_feedbackGap hM hinit hκ, pseudoRegret_def]
  simp_rw [expectedRegret_def, hreg, hps]
  rw [integral_finsetSum _ fun k _ ↦ hint k, integral_finsetSum _ fun k _ ↦ hint' k]
  refine sum_congr rfl fun k _ ↦ (hcd k).integral_comp_prodMk_eq_integral_integral ?_
  exact (hcd k |>.integrable_comp_prodMk_iff hg.aestronglyMeasurable).1 (hint k)

end Bandit

/-! ### The environment `statesEnv` -/

section StatesEnv

variable [Nonempty 𝓢] {alg : Algorithm Unit (Policy 𝓢 𝓐 H) (Fin (H + 1) → 𝓢)}
  {Y : ℕ → Ω → Fin (H + 1) → 𝓢}

/-- **Tail bound for the regret at the realized initial states.** For rewards in `[0, 1]`, along
a run of `M.statesEnv H μ`, the regret at the realized initial states `Y k 0` and the
pseudo-regret after `K` episodes satisfy, for `ε ≥ 0`,
`P(ε ≤ |regret - pseudoRegret|) ≤ 2 exp (-2 ε ^ 2 / (K H ^ 2))`. -/
theorem measureReal_le_abs_regret_sub_pseudoRegret_le_statesEnv
    (hM : M.RewardsIn (Set.Icc 0 1)) (h : IsAlgEnvSeq O X Y alg (M.statesEnv H μ) P) (K : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |M.regret H (X · ω) (fun k ↦ Y k ω 0) K - M.pseudoRegret H μ (X · ω) K|} ≤
      2 * Real.exp (-2 * ε ^ 2 / (K * H ^ 2)) :=
  measureReal_le_abs_regret_sub_pseudoRegret_le_bandit hM (statesEnv_def M H μ ▸ h)
    (measurable_pi_apply 0)
    (M.hasLaw_statesKernel_zero H μ) K hε

/-- **The regret at the realized initial states and the pseudo-regret.** For rewards in `[0, 1]`,
along a run of `M.statesEnv H μ`, with probability at least `1 - δ`, the regret at the realized
initial states `Y k 0` and the pseudo-regret after `K` episodes differ by at most
`H √(K log (2 / δ) / 2)`, and so by at most `H √(2 K log (2 / δ))`. -/
theorem le_measureReal_abs_regret_sub_pseudoRegret_le_statesEnv
    (hM : M.RewardsIn (Set.Icc 0 1)) (h : IsAlgEnvSeq O X Y alg (M.statesEnv H μ) P) (K : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | |M.regret H (X · ω) (fun k ↦ Y k ω 0) K -
      M.pseudoRegret H μ (X · ω) K| ≤ H * √(K * Real.log (2 / δ) / 2)} :=
  le_measureReal_abs_regret_sub_pseudoRegret_le_bandit hM (statesEnv_def M H μ ▸ h)
    (measurable_pi_apply 0)
    (M.hasLaw_statesKernel_zero H μ) K hδ

/-- For rewards in `[0, 1]`, along a run of `M.statesEnv H μ`, the expectation of the regret at
the realized initial states `Y k 0` after `K` episodes is the expected regret. -/
theorem integral_regret_statesEnv (hM : M.RewardsIn (Set.Icc 0 1))
    (h : IsAlgEnvSeq O X Y alg (M.statesEnv H μ) P) (K : ℕ) :
    ∫ ω, M.regret H (X · ω) (fun k ↦ Y k ω 0) K ∂P = M.expectedRegret H μ P X K :=
  integral_regret_bandit hM (statesEnv_def M H μ ▸ h) (measurable_pi_apply 0)
    (M.hasLaw_statesKernel_zero H μ) K

end StatesEnv

/-! ### The environment `episodeEnv` -/

section EpisodeEnv

variable [Nonempty 𝓢] {alg : Algorithm Unit (Policy 𝓢 𝓐 H) ((Fin (H + 1) → 𝓢) × (Fin H → ℝ))}
  {Y : ℕ → Ω → (Fin (H + 1) → 𝓢) × (Fin H → ℝ)}

/-- **Tail bound for the regret at the realized initial states.** For rewards in `[0, 1]`, along
a run of `M.episodeEnv H μ`, the regret at the realized initial states `(Y k).1 0` and the
pseudo-regret after `K` episodes satisfy, for `ε ≥ 0`,
`P(ε ≤ |regret - pseudoRegret|) ≤ 2 exp (-2 ε ^ 2 / (K H ^ 2))`. -/
theorem measureReal_le_abs_regret_sub_pseudoRegret_le_episodeEnv
    (hM : M.RewardsIn (Set.Icc 0 1)) (h : IsAlgEnvSeq O X Y alg (M.episodeEnv H μ) P) (K : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤
        |M.regret H (X · ω) (fun k ↦ (Y k ω).1 0) K - M.pseudoRegret H μ (X · ω) K|} ≤
      2 * Real.exp (-2 * ε ^ 2 / (K * H ^ 2)) :=
  measureReal_le_abs_regret_sub_pseudoRegret_le_bandit hM (episodeEnv_def M H μ ▸ h)
    ((measurable_pi_apply 0).comp measurable_fst) (M.hasLaw_episodeKernel_zero H μ) K hε

/-- **The regret at the realized initial states and the pseudo-regret.** For rewards in `[0, 1]`,
along a run of `M.episodeEnv H μ`, with probability at least `1 - δ`, the regret at the realized
initial states `(Y k).1 0` and the pseudo-regret after `K` episodes differ by at most
`H √(K log (2 / δ) / 2)`, and so by at most `H √(2 K log (2 / δ))`. -/
theorem le_measureReal_abs_regret_sub_pseudoRegret_le_episodeEnv
    (hM : M.RewardsIn (Set.Icc 0 1)) (h : IsAlgEnvSeq O X Y alg (M.episodeEnv H μ) P) (K : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | |M.regret H (X · ω) (fun k ↦ (Y k ω).1 0) K -
      M.pseudoRegret H μ (X · ω) K| ≤ H * √(K * Real.log (2 / δ) / 2)} :=
  le_measureReal_abs_regret_sub_pseudoRegret_le_bandit hM (episodeEnv_def M H μ ▸ h)
    ((measurable_pi_apply 0).comp measurable_fst) (M.hasLaw_episodeKernel_zero H μ) K hδ

/-- For rewards in `[0, 1]`, along a run of `M.episodeEnv H μ`, the expectation of the regret at
the realized initial states `(Y k).1 0` after `K` episodes is the expected regret. -/
theorem integral_regret_episodeEnv (hM : M.RewardsIn (Set.Icc 0 1))
    (h : IsAlgEnvSeq O X Y alg (M.episodeEnv H μ) P) (K : ℕ) :
    ∫ ω, M.regret H (X · ω) (fun k ↦ (Y k ω).1 0) K ∂P = M.expectedRegret H μ P X K :=
  integral_regret_bandit hM (episodeEnv_def M H μ ▸ h)
    ((measurable_pi_apply 0).comp measurable_fst)
    (M.hasLaw_episodeKernel_zero H μ) K

end EpisodeEnv

end Runs

end Learning.MDP.Episodic.EpisodicMDP
