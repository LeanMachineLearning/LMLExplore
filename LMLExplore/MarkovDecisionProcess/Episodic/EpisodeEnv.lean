/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Policy
public import LeanMachineLearning.SequentialLearning.IdentificationAlg
public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# Episodes as rounds

In online episodic learning, each round of the interaction is a whole episode of an episodic MDP
`M : EpisodicMDP 𝓢 𝓐` with horizon `H`: at the start of every episode, the learner chooses an
`H`-step policy from the previous episodes, plays it from an initial state drawn from the initial
law `μ`, and observes the episode. This file builds the corresponding environments of LML's
interaction protocol.

An episode played with the Markov policy `π : ℕ → Kernel 𝓢 𝓐` is the run of `augMarkovPolicy π`
in the time-augmented MDP `M.augmented`, started from `μ` at the step `0`. Its law is a measure on
trajectories of `M.augmented`; the states `s_0, …, s_H` of an episode are `episodeStates H` of the
trajectory and its rewards `r_0, …, r_{H-1}` are `episodeRewards H`. The law of the state sequence
of an episode is `M.statesLaw H μ π`, and the joint law of the state sequence and the reward
sequence is `M.episodeLaw H μ π`.

Under `M.statesLaw H μ π`, the first state has law `μ`, and the state of the step `h + 1` has
conditional law `∫ P_h(· | s_h, a) dπ_h(a | s_h)` given the states `s_0, …, s_h`
(`hasCondDistrib_statesLaw`). This comes from the same property along every run of `π`
(`hasCondDistrib_obs_fst_add_one_states`). Under `M.episodeLaw H μ π`, the expected sum of the
rewards is the value `∫ V^π_0 dμ` of `π` (`integral_sum_episodeLaw`).

For a finite state space and a countable action space, the `H`-step policies form a countable
discrete type. The episode-level environments are then the stationary environments, without
observations, of the kernels from `H`-step policies to the laws of an episode:
* `M.statesEnv H μ`: the feedback of a round is the state sequence of the episode. It models
  learners that know the rewards, as when the rewards are deterministic;
* `M.episodeEnv H μ`: the feedback of a round is the pair of the state sequence and the reward
  sequence. A learner in it also learns unknown stochastic rewards.

Forgetting the rewards maps the episode laws of `M.episodeEnv H μ` to those of `M.statesEnv H μ`
(`map_fst_episodeKernel`). A best policy identification algorithm is an LML identification
algorithm in `M.statesEnv H μ` with an `H`-step policy as output (`BPIAlg`).

The definitions `statesLaw`, `statesKernel`, `statesEnv` and `BPIAlg` are adapted, with their
names and namespace, from the formalization entropy-mdp (`github.com/RemyDegenne/entropy-mdp`,
file `Essakine2026Tight/ForLMLExplore/MarkovDecisionProcess/Episodic/Basic.lean`, by Rémy
Degenne, Apache 2.0) of [EV26], from a fixed initial state to an initial law, and from
deterministic to Markov policies for `statesLaw`. The statements of `hasCondDistrib_statesLaw`
and `hasCondDistrib_feedback_statesEnv` are adapted, with their names, from the file
`Essakine2026Tight/ForLMLExplore/MarkovDecisionProcess/Episodic/StepLaw.lean` of entropy-mdp,
with the same generalizations; here `hasCondDistrib_statesLaw` is proved directly from the run
lemmas instead of the source's iterated Markov property along an episode.

## Main definitions

* `Learning.MDP.Episodic.episodeStates H`, `Learning.MDP.Episodic.episodeRewards H`: the state
  and reward sequences of an episode of horizon `H`.
* `Learning.MDP.Episodic.EpisodicMDP.statesLaw M H μ π`: the law of the state sequence of an
  episode of the Markov policy `π`.
* `Learning.MDP.Episodic.EpisodicMDP.episodeLaw M H μ π`: the joint law of the state and reward
  sequences of an episode of `π`.
* `Learning.MDP.Episodic.EpisodicMDP.statesKernel M H μ`,
  `Learning.MDP.Episodic.EpisodicMDP.episodeKernel M H μ`: the same laws as kernels from
  `H`-step policies.
* `Learning.MDP.Episodic.EpisodicMDP.statesEnv M H μ`,
  `Learning.MDP.Episodic.EpisodicMDP.episodeEnv M H μ`: the episode-level environments.
* `Learning.MDP.Episodic.BPIAlg 𝓢 𝓐 H`: the best policy identification algorithms.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.hasCondDistrib_obs_fst_add_one_states`: along a run of the
  Markov policy `π` in `M.augmented` started at the step `h₀`, the state of round `n + 1` has
  conditional law `∫ P_{h₀+n}(· | s_n, a) dπ_{h₀+n}(a | s_n)` given the states of the rounds
  `0, …, n`.
* `Learning.MDP.Episodic.EpisodicMDP.hasLaw_statesLaw`,
  `Learning.MDP.Episodic.EpisodicMDP.hasLaw_episodeLaw`: the episodes of every run have these
  laws.
* `Learning.MDP.Episodic.EpisodicMDP.hasLaw_statesLaw_zero`,
  `Learning.MDP.Episodic.EpisodicMDP.hasCondDistrib_statesLaw`: the law of the first state and
  the conditional law of each next state under `M.statesLaw H μ π`.
* `Learning.MDP.Episodic.EpisodicMDP.integral_sum_episodeLaw`: the expected return of an episode
  is the value `∫ V^π_0 dμ`.
* `Learning.MDP.Episodic.EpisodicMDP.map_fst_episodeKernel`: forgetting the rewards maps the
  episode laws of `M.episodeEnv H μ` to those of `M.statesEnv H μ`.
* `Learning.MDP.Episodic.EpisodicMDP.hasCondDistrib_feedback_statesEnv`,
  `Learning.MDP.Episodic.EpisodicMDP.hasCondDistrib_feedback_episodeEnv`: in a run of these
  environments, the episode of round `t` has the law of an episode of the policy of round `t`.

## References

* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset

namespace Learning.MDP.Episodic

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-! ### The states and rewards of an episode -/

/-- The states `s_0, …, s_H` of the first `H + 1` rounds of a trajectory of the time-augmented
MDP. -/
def episodeStates (H : ℕ) (x : ℕ → Round (𝓢 × ℕ) 𝓐 ℝ) : Fin (H + 1) → 𝓢 :=
  fun h ↦ (IT.obs h x).1

@[simp]
lemma episodeStates_apply (H : ℕ) (x : ℕ → Round (𝓢 × ℕ) 𝓐 ℝ) (h : Fin (H + 1)) :
    episodeStates H x h = (IT.obs h x).1 :=
  (rfl)

@[fun_prop]
lemma measurable_episodeStates (H : ℕ) : Measurable (episodeStates (𝓢 := 𝓢) (𝓐 := 𝓐) H) :=
  Measurable.of_eval fun h ↦ (IT.measurable_obs h).fst

/-- The rewards `r_0, …, r_{H-1}` of the first `H` rounds of a trajectory of the time-augmented
MDP. -/
def episodeRewards (H : ℕ) (x : ℕ → Round (𝓢 × ℕ) 𝓐 ℝ) : Fin H → ℝ :=
  fun h ↦ IT.feedback h x

@[simp]
lemma episodeRewards_apply (H : ℕ) (x : ℕ → Round (𝓢 × ℕ) 𝓐 ℝ) (h : Fin H) :
    episodeRewards H x h = IT.feedback h x :=
  (rfl)

@[fun_prop]
lemma measurable_episodeRewards (H : ℕ) : Measurable (episodeRewards (𝓢 := 𝓢) (𝓐 := 𝓐) H) :=
  Measurable.of_eval fun h ↦ IT.measurable_feedback h

namespace EpisodicMDP

/-! ### The next state given the past states, along a run -/

/-- The states of a history of `n` rounds followed by the state `s` of round `n`. -/
private def snocStates {n : ℕ} (p : Hist (𝓢 × ℕ) 𝓐 ℝ n × 𝓢) : Fin (n + 1) → 𝓢 :=
  Fin.snoc (α := fun _ ↦ 𝓢) (fun i ↦ (p.1 i).obs.1) p.2

private lemma measurable_snocStates (n : ℕ) :
    Measurable (snocStates (𝓢 := 𝓢) (𝓐 := 𝓐) (n := n)) := by
  refine Measurable.of_eval fun i ↦ ?_
  induction i using Fin.lastCases with
  | last => simpa [snocStates] using measurable_snd
  | cast i => simp only [snocStates, Fin.snoc_castSucc]; fun_prop

/-- The kernel of the next augmented state given the past and the action of round `n`, composed
with the policy and restricted to the states at the step `k`, is the kernel of the next state
given the past states. -/
private lemma comap_map_fst_snd_compProd_augmented (M : EpisodicMDP 𝓢 𝓐) (π : ℕ → Kernel 𝓢 𝓐)
    [∀ h, IsMarkovKernel (π h)] (n k : ℕ) :
    ((Kernel.prodMkLeft (Hist (𝓢 × ℕ) 𝓐 ℝ n) (augMarkovPolicy π) ⊗ₖ
      M.augmented.P.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)).snd.map Prod.fst).comap
        (fun p : Hist (𝓢 × ℕ) 𝓐 ℝ n × 𝓢 ↦ (p.1, (p.2, k))) (by fun_prop) =
      ((M.trans k ∘ₖ (Kernel.id ×ₖ π k)).comap (fun τ ↦ τ (Fin.last n))
        (measurable_pi_apply _)).comap (snocStates (𝓐 := 𝓐)) (measurable_snocStates n) := by
  ext p t ht
  -- unfold the composite kernels at `p`, then integrate against the Dirac mass at `p.2`
  have := (M.trans k).measurable_coe ht
  simp (disch := measurability) [Kernel.map_apply', Kernel.snd_apply', Kernel.compProd_apply,
    Kernel.comp_apply', Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod, lintegral_map,
    snocStates, Set.preimage_preimage]

section Runs

variable [Nonempty 𝓢] {M : EpisodicMDP 𝓢 𝓐} {π : ℕ → Kernel 𝓢 𝓐} [∀ h, IsMarkovKernel (π h)]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝓢 × ℕ} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}

/-- **Markov property of the states**: along a run of the Markov policy `π` in the augmented MDP
started at the step `h₀`, the state of round `n + 1` has conditional law
`∫ P_{h₀+n}(· | s_n, a) dπ_{h₀+n}(a | s_n)` given the states `s_0, …, s_n` of the rounds
`0, …, n`. -/
theorem hasCondDistrib_obs_fst_add_one_states {μ : Measure (𝓢 × ℕ)} [IsProbabilityMeasure μ]
    {h₀ : ℕ} (hμ : ∀ᵐ p ∂μ, p.2 = h₀)
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π) (M.augmented.env μ) P)
    (n : ℕ) :
    HasCondDistrib (fun ω ↦ (O (n + 1) ω).1) (fun ω (i : Fin (n + 1)) ↦ (O i ω).1)
      ((M.trans (h₀ + n) ∘ₖ (Kernel.id ×ₖ π (h₀ + n))).comap (fun τ ↦ τ (Fin.last n))
        (measurable_pi_apply _)) P := by
  -- the next augmented state given the history, the state and the action of round `n`
  have hf : Measurable fun x : Hist (𝓢 × ℕ) 𝓐 ℝ (n + 1) ↦
      ((fun i : Fin n ↦ x i.castSucc, (x (Fin.last n)).obs), (x (Fin.last n)).action) := by
    fun_prop
  have hO : HasCondDistrib (O (n + 1)) (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      (M.augmented.P.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)) P :=
    HasCondDistrib.comp_right (Z := history O A Y (n + 1))
      (κ := M.augmented.P.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)) (hf := hf)
      (MDP.hasCondDistrib_obs_add_one_history h n)
  -- integrate out the action, drawn from `π` given the history and the state of round `n`
  have hS := ((h.hasCondDistrib_action_history_obs_markov n).compProd hO).snd.comp_left
    (f := Prod.fst) measurable_fst
  -- the step of round `n` is almost surely `h₀ + n`
  have hae : (fun ω ↦ (history O A Y n ω, O n ω)) =ᵐ[P]
      (fun p : Hist (𝓢 × ℕ) 𝓐 ℝ n × 𝓢 ↦ (p.1, (p.2, h₀ + n))) ∘
        fun ω ↦ (history O A Y n ω, (O n ω).1) := by
    filter_upwards [ae_obs_snd_eq hμ h n] with ω hω
    simp [← hω]
  have he : MeasurableEmbedding fun p : Hist (𝓢 × ℕ) 𝓐 ℝ n × 𝓢 ↦ (p.1, (p.2, h₀ + n)) :=
    MeasurableEmbedding.id.prodMap (measurableEmbedding_prod_mk_right (h₀ + n))
  have hS' := (hS.congr hae.symm .rfl).of_measurableEmbedding_comp_right he
  rw [comap_map_fst_snd_compProd_augmented] at hS'
  -- the resulting kernel only depends on the states of the rounds `0, …, n`
  refine (HasCondDistrib.comp_right hS').congr (.of_forall fun ω ↦ ?_) .rfl
  funext i
  induction i using Fin.lastCases with
  | last => simp [snocStates]
  | cast i => simp [snocStates, history_apply]

end Runs

/-! ### The laws of an episode -/

variable (M : EpisodicMDP 𝓢 𝓐) (H : ℕ) (μ : Measure 𝓢)

/-- Under the initial law `μ` placed at the step `0`, the step is almost surely `0`. -/
private lemma ae_snd_map_prodMk_zero : ∀ᵐ p ∂(μ.map fun s ↦ (s, 0)), p.2 = 0 :=
  (ae_map_iff measurable_prodMk_right.aemeasurable
    (measurable_snd (measurableSet_singleton 0))).2 (.of_forall fun _ ↦ rfl)

section Laws

variable [Nonempty 𝓢] (π : ℕ → Kernel 𝓢 𝓐) [∀ h, IsMarkovKernel (π h)]

/-- The trajectories of the episodes of `π` from `μ` form a run of `π` in the augmented MDP. -/
private lemma isAlgEnvSeq_episode :
    IsAlgEnvSeq IT.obs IT.action IT.feedback (Algorithm.markov fun _ ↦ augMarkovPolicy π)
      (M.augmented.env (μ.map fun s ↦ (s, 0)))
      (trajMeasure (Algorithm.markov fun _ ↦ augMarkovPolicy π)
        (M.augmented.env (μ.map fun s ↦ (s, 0)))) :=
  IT.isAlgEnvSeq_trajMeasure _ _

/-- The law of the state sequence `s_0, …, s_H` of an episode of horizon `H` played with the
Markov policy `π` from the initial law `μ`. -/
noncomputable def statesLaw : Measure (Fin (H + 1) → 𝓢) :=
  (trajMeasure (Algorithm.markov fun _ ↦ augMarkovPolicy π)
    (M.augmented.env (μ.map fun s ↦ (s, 0)))).map (episodeStates H)

/-- The joint law of the state sequence `s_0, …, s_H` and the reward sequence
`r_0, …, r_{H-1}` of an episode of horizon `H` played with the Markov policy `π` from the initial
law `μ`. -/
noncomputable def episodeLaw : Measure ((Fin (H + 1) → 𝓢) × (Fin H → ℝ)) :=
  (trajMeasure (Algorithm.markov fun _ ↦ augMarkovPolicy π)
    (M.augmented.env (μ.map fun s ↦ (s, 0)))).map fun x ↦ (episodeStates H x, episodeRewards H x)

instance : IsProbabilityMeasure (M.statesLaw H μ π) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_episodeStates H).aemeasurable).2 inferInstance

instance : IsProbabilityMeasure (M.episodeLaw H μ π) :=
  (Measure.isProbabilityMeasure_map_iff
    ((measurable_episodeStates H).prodMk (measurable_episodeRewards H)).aemeasurable).2
    inferInstance

/-- Forgetting the rewards maps the law of an episode to the law of its state sequence. -/
@[simp]
lemma map_fst_episodeLaw : (M.episodeLaw H μ π).map Prod.fst = M.statesLaw H μ π := by
  rw [episodeLaw, Measure.map_map measurable_fst (by fun_prop), statesLaw]
  simp [Function.comp_def]

variable {M H μ π}

/-- Along every run of the Markov policy `π` in the augmented MDP started from `μ` at the step
`0`, the states of the rounds `0, …, H` have law `M.statesLaw H μ π`. -/
lemma hasLaw_statesLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓢 × ℕ} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π)
      (M.augmented.env (μ.map fun s ↦ (s, 0))) P) :
    HasLaw (fun ω (i : Fin (H + 1)) ↦ (O i ω).1) (M.statesLaw H μ π) P :=
  -- `episodeStates H ∘ trajectory O A Y` is the function of the statement by definition
  HasLaw.comp ⟨(measurable_episodeStates H).aemeasurable, rfl⟩ h.hasLaw_trajectory

/-- Along every run of the Markov policy `π` in the augmented MDP started from `μ` at the step
`0`, the states of the rounds `0, …, H` and the rewards of the rounds `0, …, H - 1` have law
`M.episodeLaw H μ π`. -/
lemma hasLaw_episodeLaw {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓢 × ℕ} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ augMarkovPolicy π)
      (M.augmented.env (μ.map fun s ↦ (s, 0))) P) :
    HasLaw (fun ω ↦ (fun i : Fin (H + 1) ↦ (O i ω).1, fun i : Fin H ↦ Y i ω))
      (M.episodeLaw H μ π) P :=
  -- the composite with `trajectory O A Y` is the function of the statement by definition
  HasLaw.comp ⟨((measurable_episodeStates H).prodMk (measurable_episodeRewards H)).aemeasurable,
    rfl⟩ h.hasLaw_trajectory

variable [IsProbabilityMeasure μ]

/-- Under the law of the state sequence of an episode, the first state has law `μ`. -/
lemma hasLaw_statesLaw_zero : HasLaw (fun τ ↦ τ 0) μ (M.statesLaw H μ π) := by
  have h0 := MDP.hasLaw_obs_zero (isAlgEnvSeq_episode M μ π)
  refine ⟨(measurable_pi_apply 0).aemeasurable, ?_⟩
  have he : (fun τ : Fin (H + 1) → 𝓢 ↦ τ 0) ∘ episodeStates (𝓐 := 𝓐) H = Prod.fst ∘ IT.obs 0 := by
    funext x
    simp
  rw [statesLaw, Measure.map_map (measurable_pi_apply 0) (measurable_episodeStates H), he,
    ← Measure.map_map measurable_fst (IT.measurable_obs 0), h0.map_eq,
    Measure.map_map measurable_fst measurable_prodMk_right]
  exact Measure.map_id

/-- **Markov property of the states of an episode**: under the law of the state sequence of an
episode of the Markov policy `π`, the state of the step `h + 1` has conditional law
`∫ P_h(· | s_h, a) dπ_h(a | s_h)` given the states `s_0, …, s_h`. -/
theorem hasCondDistrib_statesLaw (h : Fin H) :
    HasCondDistrib (fun τ : Fin (H + 1) → 𝓢 ↦ τ h.succ)
      (fun τ (i : Fin (h + 1)) ↦ τ (Fin.castLE (Nat.succ_le_succ h.isLt.le) i))
      ((M.trans h ∘ₖ (Kernel.id ×ₖ π h)).comap (fun τ ↦ τ (Fin.last h))
        (measurable_pi_apply _)) (M.statesLaw H μ π) := by
  have hc := hasCondDistrib_obs_fst_add_one_states (ae_snd_map_prodMk_zero μ)
    (isAlgEnvSeq_episode M μ π) h
  rw [zero_add] at hc
  have hX : Measurable fun (τ : Fin (H + 1) → 𝓢) (i : Fin (h + 1)) ↦
      τ (Fin.castLE (Nat.succ_le_succ h.isLt.le) i) :=
    Measurable.of_eval fun _ ↦ measurable_pi_apply _
  -- transfer the conditional law from the trajectories to their state sequences
  refine ⟨(hX.prodMk (measurable_pi_apply _)).aemeasurable, ?_⟩
  rw [statesLaw, Measure.map_map hX (measurable_episodeStates H),
    Measure.map_map (hX.prodMk (measurable_pi_apply _)) (measurable_episodeStates H)]
  convert hc.map_eq using 3 <;> simp [Function.comp_def]

/-- **The expected return of an episode** is the value `∫ V^π_0 dμ` of the Markov policy `π`,
for rewards bounded by `C`. -/
theorem integral_sum_episodeLaw {C : ℝ} (hM : M.RewardsIn (Set.Icc (-C) C)) :
    ∫ e, ∑ h, e.2 h ∂(M.episodeLaw H μ π) = ∫ s, M.value H π 0 s ∂μ := by
  have hv := integral_sum_feedback_eq_integral_value (H := H) hM (ae_snd_map_prodMk_zero μ)
    (isAlgEnvSeq_episode M μ π)
  have hmap : ∫ p : 𝓢 × ℕ, M.value H π 0 p.1 ∂(μ.map fun s ↦ (s, 0)) =
      ∫ s, M.value H π 0 s ∂μ :=
    integral_map measurable_prodMk_right.aemeasurable
      ((measurable_value 0).comp measurable_fst).aestronglyMeasurable
  rw [Nat.sub_zero, hmap] at hv
  rw [episodeLaw, integral_map (by fun_prop) (by fun_prop), ← hv]
  congr 1 with x
  exact Fin.sum_univ_eq_sum_range (fun n ↦ IT.feedback n x) H

end Laws

/-! ### The episode-level environments -/

section EpisodeEnv

variable [Nonempty 𝓢] [Finite 𝓢] [Countable 𝓐] [MeasurableSingletonClass 𝓢]
  [MeasurableSingletonClass 𝓐] [Nonempty 𝓐]

/-- The kernel from `H`-step policies to the law of the state sequence of an episode played with
the policy from the initial law `μ`. -/
noncomputable def statesKernel : Kernel (Policy 𝓢 𝓐 H) (Fin (H + 1) → 𝓢) where
  toFun π := M.statesLaw H μ (π.toKernel fun _ ↦ measurable_of_countable _)
  measurable' := measurable_of_countable _

@[simp]
lemma statesKernel_apply (π : Policy 𝓢 𝓐 H) :
    M.statesKernel H μ π = M.statesLaw H μ (π.toKernel fun _ ↦ measurable_of_countable _) :=
  (rfl)

instance : IsMarkovKernel (M.statesKernel H μ) :=
  ⟨fun π ↦ by rw [statesKernel_apply]; infer_instance⟩

/-- The kernel from `H`-step policies to the joint law of the state sequence and the reward
sequence of an episode played with the policy from the initial law `μ`. -/
noncomputable def episodeKernel :
    Kernel (Policy 𝓢 𝓐 H) ((Fin (H + 1) → 𝓢) × (Fin H → ℝ)) where
  toFun π := M.episodeLaw H μ (π.toKernel fun _ ↦ measurable_of_countable _)
  measurable' := measurable_of_countable _

@[simp]
lemma episodeKernel_apply (π : Policy 𝓢 𝓐 H) :
    M.episodeKernel H μ π = M.episodeLaw H μ (π.toKernel fun _ ↦ measurable_of_countable _) :=
  (rfl)

instance : IsMarkovKernel (M.episodeKernel H μ) :=
  ⟨fun π ↦ by rw [episodeKernel_apply]; infer_instance⟩

/-- Forgetting the rewards maps the episode laws of `M.episodeEnv H μ` to those of
`M.statesEnv H μ`. -/
@[simp]
lemma map_fst_episodeKernel : (M.episodeKernel H μ).map Prod.fst = M.statesKernel H μ := by
  ext π : 1
  rw [Kernel.map_apply _ measurable_fst, episodeKernel_apply, map_fst_episodeLaw,
    statesKernel_apply]

/-- The episode-level environment of the episodic MDP `M` with horizon `H` and initial law `μ`,
in which the learner observes the state sequences only, the rewards being known: at each round,
the learner plays an `H`-step policy and observes the state sequence of the episode. -/
noncomputable def statesEnv : Environment Unit (Policy 𝓢 𝓐 H) (Fin (H + 1) → 𝓢) :=
  Environment.bandit (M.statesKernel H μ)

/-- The episode-level environment of the episodic MDP `M` with horizon `H` and initial law `μ`,
in which the learner observes the state sequences and the reward sequences: at each round, the
learner plays an `H`-step policy and observes the states and the rewards of the episode. -/
noncomputable def episodeEnv :
    Environment Unit (Policy 𝓢 𝓐 H) ((Fin (H + 1) → 𝓢) × (Fin H → ℝ)) :=
  Environment.bandit (M.episodeKernel H μ)

lemma statesEnv_def : M.statesEnv H μ = Environment.bandit (M.statesKernel H μ) :=
  (rfl)

lemma episodeEnv_def : M.episodeEnv H μ = Environment.bandit (M.episodeKernel H μ) :=
  (rfl)

variable {M H μ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → Policy 𝓢 𝓐 H}

/-- In a run of the episode-level environment `M.statesEnv H μ`, the state sequence of the
episode `t` has the law of an episode of the policy `X t` of the episode `t`. -/
lemma hasCondDistrib_feedback_statesEnv {Y : ℕ → Ω → Fin (H + 1) → 𝓢}
    {alg : Algorithm Unit (Policy 𝓢 𝓐 H) (Fin (H + 1) → 𝓢)}
    (h : IsAlgEnvSeq O X Y alg (M.statesEnv H μ) P) (t : ℕ) :
    HasCondDistrib (Y t) (X t) (M.statesKernel H μ) P :=
  h.hasCondDistrib_feedback_bandit t

/-- In a run of the episode-level environment `M.episodeEnv H μ`, the state and reward sequences
of the episode `t` have the law of an episode of the policy `X t` of the episode `t`. -/
lemma hasCondDistrib_feedback_episodeEnv {Y : ℕ → Ω → (Fin (H + 1) → 𝓢) × (Fin H → ℝ)}
    {alg : Algorithm Unit (Policy 𝓢 𝓐 H) ((Fin (H + 1) → 𝓢) × (Fin H → ℝ))}
    (h : IsAlgEnvSeq O X Y alg (M.episodeEnv H μ) P) (t : ℕ) :
    HasCondDistrib (Y t) (X t) (M.episodeKernel H μ) P :=
  h.hasCondDistrib_feedback_bandit t

end EpisodeEnv

end EpisodicMDP

/-- A best policy identification algorithm with horizon `H`: an identification algorithm that
plays an `H`-step policy at each episode, observes the state sequence of the episode, and
outputs an `H`-step policy. -/
abbrev BPIAlg (𝓢 𝓐 : Type*) [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] (H : ℕ) :=
  IdentAlg Unit (Policy 𝓢 𝓐 H) (Fin (H + 1) → 𝓢) (Policy 𝓢 𝓐 H)

end Learning.MDP.Episodic
