/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Basic
import Mathlib.Analysis.Convex.Integral

/-!
# Episodic Markov decision processes and the time-augmented MDP

An episodic (finite-horizon) MDP `M : EpisodicMDP 𝓢 𝓐` on measurable state and action spaces is
given by a transition kernel `M.trans h : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel
`M.reward h : Kernel (𝓢 × 𝓐) ℝ` at every step `h : ℕ`, all Markov. The horizon `H` of the
episodes is not part of the model: a problem with horizon `H` only uses the kernels of the steps
`h < H`, and every quantity that depends on the horizon takes it as an argument.

The episodic MDP is embedded in the stationary MDP `M.augmented : MDP (𝓢 × ℕ) 𝓐 ℝ` on the
time-augmented state space: from the augmented state `(s, h)`, the action `a` yields a reward of
law `M.reward h (s, a)` and the next augmented state `(s', h + 1)` with `s' ∼ M.trans h (s, a)`.
The runs of the episodic MDP are the runs of LML's interaction protocol in the environment
`M.augmented.env μ`, so that all the run lemmas of stationary MDPs apply to them. This file proves
that along such a run started at the step `h₀`, the step counter of round `n` is `h₀ + n`, and
deduces the step-dependent laws of the states and rewards.

The definitions `EpisodicMDP`, `ofDet`, `meanReward`, `RewardsIn`, `HasRewardFn` and
`augmented` are adapted, with their names and namespace, from the formalization entropy-mdp
(`github.com/RemyDegenne/entropy-mdp`, file
`Essakine2026Tight/LeanMachineLearning/ReinforcementLearning/MDP/Episodic.lean`, by Rémy Degenne,
Apache 2.0) of [EV26].

## Main definitions

* `Learning.MDP.Episodic.EpisodicMDP 𝓢 𝓐`: an episodic MDP.
* `Learning.MDP.Episodic.EpisodicMDP.ofDet trans r hr`: the episodic MDP with transition kernels
  `trans` and the deterministic reward function `r`.
* `Learning.MDP.Episodic.EpisodicMDP.meanReward M h s a`: the mean reward `r_h(s, a)`.
* `Learning.MDP.Episodic.EpisodicMDP.RewardsIn M I`: the rewards lie almost surely in `I`.
* `Learning.MDP.Episodic.EpisodicMDP.HasRewardFn M r`: the rewards are the deterministic
  function `r`.
* `Learning.MDP.Episodic.EpisodicMDP.augmented M`: the time-augmented stationary MDP.

## Main statements

For every run `IsAlgEnvSeq O A Y alg (M.augmented.env μ) P` from an initial law `μ` concentrated
on the step `h₀`:
* `Learning.MDP.Episodic.EpisodicMDP.ae_obs_snd_eq`: almost surely, the step of round `n` is
  `h₀ + n`;
* `Learning.MDP.Episodic.EpisodicMDP.hasCondDistrib_obs_fst_add_one`: the state of round `n + 1`
  has conditional law `M.trans (h₀ + n)` given the state and action of round `n`;
* `Learning.MDP.Episodic.EpisodicMDP.hasCondDistrib_feedback`: the reward of round `n` has
  conditional law `M.reward (h₀ + n)` given the state and action of round `n`;
* `Learning.MDP.Episodic.EpisodicMDP.integral_feedback`: for bounded rewards, the expected reward
  of round `n` is the integral of the mean reward `M.meanReward (h₀ + n)` against the law of the
  state-action pair of round `n`.

## References

* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717.
-/

public section

open MeasureTheory ProbabilityTheory Learning

namespace Learning.MDP.Episodic

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-- An episodic (finite-horizon) MDP with state space `𝓢` and action space `𝓐`: a transition
kernel `trans h : Kernel (𝓢 × 𝓐) 𝓢` and a real reward kernel `reward h : Kernel (𝓢 × 𝓐) ℝ` at
every step `h : ℕ`, all Markov. See `EpisodicMDP.augmented` for its runs. -/
@[ext]
structure EpisodicMDP (𝓢 𝓐 : Type*) [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] where
  /-- The transition kernel of step `h`: the law of the next state given the current state and
  action. -/
  trans : ℕ → Kernel (𝓢 × 𝓐) 𝓢
  /-- The transition kernels are Markov kernels. -/
  [isMarkovKernel_trans : ∀ h, IsMarkovKernel (trans h)]
  /-- The reward kernel of step `h`: the law of the reward given the current state and
  action. -/
  reward : ℕ → Kernel (𝓢 × 𝓐) ℝ
  /-- The reward kernels are Markov kernels. -/
  [isMarkovKernel_reward : ∀ h, IsMarkovKernel (reward h)]

namespace EpisodicMDP

variable (M : EpisodicMDP 𝓢 𝓐)

instance (h : ℕ) : IsMarkovKernel (M.trans h) := M.isMarkovKernel_trans h

instance (h : ℕ) : IsMarkovKernel (M.reward h) := M.isMarkovKernel_reward h

/-! ### Deterministic rewards -/

/-- The episodic MDP with transition kernels `trans h` and the deterministic reward function `r`,
measurable in the state-action pair at every step. -/
noncomputable def ofDet (trans : ℕ → Kernel (𝓢 × 𝓐) 𝓢) [∀ h, IsMarkovKernel (trans h)]
    (r : ℕ → 𝓢 → 𝓐 → ℝ) (hr : ∀ h, Measurable fun p : 𝓢 × 𝓐 ↦ r h p.1 p.2) :
    EpisodicMDP 𝓢 𝓐 where
  trans := trans
  reward h := Kernel.deterministic (fun p ↦ r h p.1 p.2) (hr h)

@[simp]
lemma ofDet_trans (trans : ℕ → Kernel (𝓢 × 𝓐) 𝓢) [∀ h, IsMarkovKernel (trans h)]
    (r : ℕ → 𝓢 → 𝓐 → ℝ) (hr : ∀ h, Measurable fun p : 𝓢 × 𝓐 ↦ r h p.1 p.2) :
    (ofDet trans r hr).trans = trans :=
  (rfl)

@[simp]
lemma ofDet_reward (trans : ℕ → Kernel (𝓢 × 𝓐) 𝓢) [∀ h, IsMarkovKernel (trans h)]
    (r : ℕ → 𝓢 → 𝓐 → ℝ) (hr : ∀ h, Measurable fun p : 𝓢 × 𝓐 ↦ r h p.1 p.2) (h : ℕ) :
    (ofDet trans r hr).reward h = Kernel.deterministic (fun p ↦ r h p.1 p.2) (hr h) :=
  (rfl)

/-! ### Mean rewards and conditions on the rewards -/

/-- The mean reward `r_h(s, a) = 𝔼[R]` of the state-action pair `(s, a)` at step `h`. -/
noncomputable def meanReward (h : ℕ) (s : 𝓢) (a : 𝓐) : ℝ := MDP.meanReward (M.reward h) (s, a)

lemma meanReward_def (h : ℕ) (s : 𝓢) (a : 𝓐) :
    M.meanReward h s a = ∫ x, x ∂(M.reward h (s, a)) :=
  MDP.meanReward_def _ _

/-- The mean reward of each step is a measurable function of the state-action pair. -/
lemma measurable_meanReward (h : ℕ) : Measurable fun p : 𝓢 × 𝓐 ↦ M.meanReward h p.1 p.2 :=
  MDP.measurable_meanReward (M.reward h)

/-- The rewards of `M` lie almost surely in the set `I`, at every step and state-action pair. -/
def RewardsIn (I : Set ℝ) : Prop := ∀ h s a, ∀ᵐ x ∂(M.reward h (s, a)), x ∈ I

lemma rewardsIn_def (I : Set ℝ) :
    M.RewardsIn I ↔ ∀ h s a, ∀ᵐ x ∂(M.reward h (s, a)), x ∈ I :=
  .rfl

variable {M} in
/-- Rewards in `I` are rewards in every superset of `I`. -/
lemma RewardsIn.mono {I J : Set ℝ} (hM : M.RewardsIn I) (hIJ : I ⊆ J) : M.RewardsIn J :=
  fun h s a ↦ (hM h s a).mono fun _ hx ↦ hIJ hx

variable {M} in
/-- Rewards almost surely in `[c, d]` have a mean in `[c, d]`. -/
lemma meanReward_mem_Icc {c d : ℝ} (hM : M.RewardsIn (Set.Icc c d)) (h : ℕ) (s : 𝓢) (a : 𝓐) :
    M.meanReward h s a ∈ Set.Icc c d := by
  rw [meanReward_def]
  exact (convex_Icc c d).integral_mem isClosed_Icc (hM h s a)
    (.of_mem_Icc c d measurable_id.aemeasurable (hM h s a))

variable {M} in
/-- For rewards almost surely in `[c, d]`, the mean reward of each step is integrable with respect
to every finite measure on the state-action pairs. -/
lemma integrable_meanReward {c d : ℝ} (hM : M.RewardsIn (Set.Icc c d)) (h : ℕ)
    {ν : Measure (𝓢 × 𝓐)} [IsFiniteMeasure ν] :
    Integrable (fun p : 𝓢 × 𝓐 ↦ M.meanReward h p.1 p.2) ν :=
  .of_mem_Icc c d (M.measurable_meanReward h).aemeasurable
    (.of_forall fun p ↦ meanReward_mem_Icc hM h p.1 p.2)

/-- The rewards of `M` are the deterministic function `r`: the reward of the pair `(s, a)` at
step `h` is `r h s a`. -/
def HasRewardFn (r : ℕ → 𝓢 → 𝓐 → ℝ) : Prop :=
  ∀ h s a, M.reward h (s, a) = Measure.dirac (r h s a)

lemma hasRewardFn_def (r : ℕ → 𝓢 → 𝓐 → ℝ) :
    M.HasRewardFn r ↔ ∀ h s a, M.reward h (s, a) = Measure.dirac (r h s a) :=
  .rfl

lemma hasRewardFn_ofDet (trans : ℕ → Kernel (𝓢 × 𝓐) 𝓢) [∀ h, IsMarkovKernel (trans h)]
    (r : ℕ → 𝓢 → 𝓐 → ℝ) (hr : ∀ h, Measurable fun p : 𝓢 × 𝓐 ↦ r h p.1 p.2) :
    (ofDet trans r hr).HasRewardFn r :=
  fun h s a ↦ by simp [Kernel.deterministic_apply]

variable {M} in
/-- The mean of deterministic rewards is the reward function. -/
lemma meanReward_eq_of_hasRewardFn {r : ℕ → 𝓢 → 𝓐 → ℝ} (hM : M.HasRewardFn r) (h : ℕ) (s : 𝓢)
    (a : 𝓐) : M.meanReward h s a = r h s a := by
  simp [meanReward_def, hM h s a]

variable {M} in
/-- Deterministic rewards with values in `I` lie in `I`. -/
lemma HasRewardFn.rewardsIn {r : ℕ → 𝓢 → 𝓐 → ℝ} (hM : M.HasRewardFn r) {I : Set ℝ}
    (hr : ∀ h s a, r h s a ∈ I) : M.RewardsIn I :=
  fun h s a ↦ by rw [hM h s a, ae_dirac_eq]; exact hr h s a

/-! ### The time-augmented MDP -/

/-- A step-indexed family of kernels on `𝓢 × 𝓐`, read at the step of an augmented state, is a
measurable function of the augmented state-action pair. -/
private lemma measurable_kernel_step {β : Type*} {mβ : MeasurableSpace β}
    (κ : ℕ → Kernel (𝓢 × 𝓐) β) :
    Measurable fun p : (𝓢 × ℕ) × 𝓐 ↦ κ p.1.2 (p.1.1, p.2) := by
  have h : Measurable fun q : (𝓢 × 𝓐) × ℕ ↦ κ q.2 q.1 :=
    measurable_from_prod_countable_left fun h ↦ (κ h).measurable
  exact h.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)

/-- The stationary MDP on the time-augmented state space `𝓢 × ℕ` which embeds the episodic MDP
`M`: from the augmented state `(s, h)`, the action `a` yields a reward of law
`M.reward h (s, a)` and the next augmented state `(s', h + 1)` with `s' ∼ M.trans h (s, a)`. -/
noncomputable def augmented : MDP (𝓢 × ℕ) 𝓐 ℝ where
  P := ⟨fun p ↦ (M.trans p.1.2).map (fun s' ↦ (s', p.1.2 + 1)) (p.1.1, p.2),
    measurable_kernel_step fun h ↦ (M.trans h).map fun s' ↦ (s', h + 1)⟩
  hP := ⟨fun p ↦
    (Kernel.IsMarkovKernel.map (M.trans p.1.2) measurable_prodMk_right).isProbabilityMeasure _⟩
  R := ⟨fun p ↦ M.reward p.1.2 (p.1.1, p.2), measurable_kernel_step M.reward⟩
  hR := ⟨fun p ↦ inferInstanceAs (IsProbabilityMeasure (M.reward p.1.2 (p.1.1, p.2)))⟩

@[simp]
lemma augmented_P_apply (s : 𝓢) (h : ℕ) (a : 𝓐) :
    M.augmented.P ((s, h), a) = (M.trans h (s, a)).map fun s' ↦ (s', h + 1) :=
  Kernel.map_apply _ measurable_prodMk_right _

@[simp]
lemma augmented_R_apply (s : 𝓢) (h : ℕ) (a : 𝓐) :
    M.augmented.R ((s, h), a) = M.reward h (s, a) :=
  (rfl)

/-- The mean reward of the augmented MDP at `((s, h), a)` is the mean reward of `M` at
step `h`. -/
@[simp]
lemma meanReward_augmented (s : 𝓢) (h : ℕ) (a : 𝓐) :
    MDP.meanReward M.augmented.R ((s, h), a) = M.meanReward h s a := by
  rw [MDP.meanReward_def, augmented_R_apply, meanReward_def]

variable {M} in
/-- Rewards of `M` in `I` are rewards of the augmented MDP in `I`. -/
lemma RewardsIn.ae_mem_augmented_R {I : Set ℝ} (hM : M.RewardsIn I) (p : (𝓢 × ℕ) × 𝓐) :
    ∀ᵐ x ∂(M.augmented.R p), x ∈ I :=
  hM p.1.2 p.1.1 p.2

variable {M} in
/-- Rewards of `M` in `[-C, C]` give the reward bound which the value theory of the augmented MDP
assumes. -/
lemma RewardsIn.ae_abs_augmented_R_le {C : ℝ} (hM : M.RewardsIn (Set.Icc (-C) C))
    (p : (𝓢 × ℕ) × 𝓐) : ∀ᵐ x ∂(M.augmented.R p), |x| ≤ C :=
  (hM.ae_mem_augmented_R p).mono fun _ hx ↦ abs_le.2 hx

/-- The embedding of `𝓢 × 𝓐` in the augmented state-action pairs at the step `k`. -/
private lemma measurableEmbedding_augment (k : ℕ) :
    MeasurableEmbedding fun q : 𝓢 × 𝓐 ↦ ((q.1, k), q.2) :=
  (measurableEmbedding_prod_mk_right k).prodMap MeasurableEmbedding.id

/-! ### Runs of the time-augmented MDP -/

section Runs

variable [Nonempty 𝓢] {M : EpisodicMDP 𝓢 𝓐} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓢 × ℕ} {A : ℕ → Ω → 𝓐}
  {Y : ℕ → Ω → ℝ} {alg : Algorithm (𝓢 × ℕ) 𝓐 ℝ} {μ : Measure (𝓢 × ℕ)} [IsProbabilityMeasure μ]
  {h₀ : ℕ}

/-- Along a run of the augmented MDP started at the step `h₀`, the step of round `n` is almost
surely `h₀ + n`. -/
theorem ae_obs_snd_eq (hμ : ∀ᵐ p ∂μ, p.2 = h₀) (h : IsAlgEnvSeq O A Y alg (M.augmented.env μ) P)
    (n : ℕ) : ∀ᵐ ω ∂P, (O n ω).2 = h₀ + n := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have h_meas (k : ℕ) : MeasurableSet {q : 𝓢 × ℕ | q.2 = k} :=
    measurable_snd (measurableSet_singleton k)
  induction n with
  | zero =>
    rw [← (MDP.hasLaw_obs_zero h).map_eq] at hμ
    simpa using ae_of_ae_map (hO 0).aemeasurable hμ
  | succ n ih =>
    have h_law := (MDP.hasLaw_obs_add_one h n).map_eq
    have h_pair : ∀ᵐ p ∂(P.map fun ω ↦ (O n ω, A n ω)), p.1.2 = h₀ + n :=
      (ae_map_iff ((hO n).prodMk (hA n)).aemeasurable
        ((h_meas _).preimage measurable_fst)).2 ih
    have h_next : ∀ᵐ q ∂(P.map (O (n + 1))), q.2 = h₀ + (n + 1) := by
      rw [h_law]
      refine Measure.ae_comp_of_ae_ae (h_meas _) (h_pair.mono fun p hp ↦ ?_)
      obtain ⟨⟨s, k⟩, a⟩ := p
      rw [augmented_P_apply, ae_map_iff measurable_prodMk_right.aemeasurable (h_meas _)]
      exact .of_forall fun _ ↦ by simp only at hp ⊢; omega
    exact ae_of_ae_map (hO (n + 1)).aemeasurable h_next

/-- Along a run of the augmented MDP started at the step `h₀`, the augmented state-action pair of
round `n` is almost surely the state-action pair at the step `h₀ + n`. -/
private lemma obs_action_ae_eq (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y alg (M.augmented.env μ) P) (n : ℕ) :
    (fun ω ↦ (O n ω, A n ω)) =ᵐ[P]
      (fun q : 𝓢 × 𝓐 ↦ ((q.1, h₀ + n), q.2)) ∘ fun ω ↦ ((O n ω).1, A n ω) := by
  filter_upwards [ae_obs_snd_eq hμ h n] with ω hω
  simp [← hω]

/-- Along a run of the augmented MDP started at the step `h₀`, the state of round `n + 1` has
conditional law `M.trans (h₀ + n)` given the state and action of round `n`. -/
theorem hasCondDistrib_obs_fst_add_one (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y alg (M.augmented.env μ) P) (n : ℕ) :
    HasCondDistrib (fun ω ↦ (O (n + 1) ω).1) (fun ω ↦ ((O n ω).1, A n ω))
      (M.trans (h₀ + n)) P := by
  have h_cond := ((MDP.hasCondDistrib_obs_add_one h n).fst.congr
    (obs_action_ae_eq hμ h n).symm .rfl).of_measurableEmbedding_comp_right
      (measurableEmbedding_augment (h₀ + n))
  convert h_cond using 1
  ext q : 1
  simp [Kernel.fst_apply, Measure.map_map measurable_fst measurable_prodMk_right, Function.comp_def]

/-- Along a run of the augmented MDP started at the step `h₀`, the reward of round `n` has
conditional law `M.reward (h₀ + n)` given the state and action of round `n`. -/
theorem hasCondDistrib_feedback (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y alg (M.augmented.env μ) P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ ((O n ω).1, A n ω)) (M.reward (h₀ + n)) P := by
  have h_cond := ((MDP.hasCondDistrib_feedback h n).congr (obs_action_ae_eq hμ h n).symm
    .rfl).of_measurableEmbedding_comp_right (measurableEmbedding_augment (h₀ + n))
  convert h_cond using 1
  ext q : 1
  rw [Kernel.comap_apply, augmented_R_apply]

/-- Along a run of the augmented MDP started at the step `h₀`, with rewards bounded by `C`, the
expected reward of round `n` is the integral of the mean reward of the step `h₀ + n` against the
law of the state-action pair of round `n`. -/
theorem integral_feedback {C : ℝ} (hR : M.RewardsIn (Set.Icc (-C) C)) (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y alg (M.augmented.env μ) P) (n : ℕ) :
    ∫ ω, Y n ω ∂P =
      ∫ q, M.meanReward (h₀ + n) q.1 q.2 ∂(P.map fun ω ↦ ((O n ω).1, A n ω)) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  rw [MDP.integral_feedback h hR.ae_abs_augmented_R_le n,
    Measure.map_congr (obs_action_ae_eq hμ h n),
    ← Measure.map_map (measurableEmbedding_augment (h₀ + n)).measurable
      ((hO n).fst.prodMk (hA n)),
    integral_map (measurableEmbedding_augment (h₀ + n)).measurable.aemeasurable
      ((MDP.measurable_meanReward _).aestronglyMeasurable)]
  simp

end Runs

end EpisodicMDP

end Learning.MDP.Episodic
