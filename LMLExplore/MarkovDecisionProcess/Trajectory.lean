/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.MarkovPolicy
public import LMLExplore.Probability.MarkovChain.MarkovProperty

/-!
# The trajectory of a stationary policy is a Markov chain

Let `π : Kernel 𝓢 𝓐` be a stationary policy of the MDP `M`, run as `Algorithm.markov fun _ ↦ π`
in the environment `M.env μ` from a probability measure `μ`. A round `(s, a, r)` of a run is a
state `s`, an action `a` drawn from `π s` and a reward `r` drawn from `M.R (s, a)`
(`stateRoundKernel M π s`), and the state of the next round is drawn from `M.P (s, a)`. The law
of the next round therefore depends on the past only through the current round: it is
`roundKernel M π r`. This file proves that the rounds of every run form a homogeneous Markov chain
with transition kernel `roundKernel M π`, in the sense of Tau Ceti's `markovChainLaw`, and derives
the Markov property of runs and the Markov chains of the states and of the state-action pairs.

The law of the trajectory of `π` from a state `s` is `trajKernel M π s`, a kernel in `s`; it is
the trajectory law `trajMeasure` of the run started from `Measure.dirac s`
(`trajKernel_apply_eq_trajMeasure`). For a deterministic stationary policy, it is LMLExplore's
`MDP.policyMeasure` (`policyMeasure_eq_trajKernel`), which is therefore measurable in the initial
state.

## Main definitions

* `Learning.MDP.stateRoundKernel M π`: the law of a round from its state.
* `Learning.MDP.roundKernel M π`: the law of the next round given the current round.
* `Learning.MDP.trajKernel M π`: the law of the trajectory from a state.

## Main statements

For every run `IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P` from a probability
measure `μ`:
* `Learning.MDP.hasLaw_trajectory_markovChainLaw`: the rounds form a Markov chain, with initial
  law `stateRoundKernel M π ∘ₘ μ` and transition kernel `roundKernel M π`; equivalently, the
  trajectory has law `trajKernel M π ∘ₘ μ` (`hasLaw_trajectory_trajKernel`,
  `trajMeasure_markov_env`).
* `Learning.MDP.hasCondDistrib_processShift_history`, the **Markov property**: given the rounds
  before `n`, the rounds from `n` on have the law of the trajectory of `π` started from the law
  `(M.env μ).obs n` of the state of round `n`;
  `Learning.MDP.hasCondDistrib_processShift_history_obs`: given in addition the state `s` of
  round `n`, they have law `trajKernel M π s`.
* `Learning.MDP.hasLaw_obs_markovChainLaw`: the states form a Markov chain with initial law `μ` and
  transition kernel `M.stateKernel π`.
* `Learning.MDP.hasLaw_obs_action_markovChainLaw`: the state-action pairs form a Markov chain with
  initial law `μ ⊗ₘ π` and transition kernel `M.saKernel π`.

The Markov property is adapted from the Essakine2026Tight project (`RemyDegenne/Essakine2026Tight`,
Apache 2.0, `ForLMLExplore/MarkovDecisionProcess/Markov.lean`), where it is proved for
deterministic stationary policies by the uniqueness of the Ionescu-Tulcea trajectory law; here it
is derived from the Markov property of Tau Ceti's `markovChainLaw`
(`ProbabilityTheory.HasLaw.prefix_processShift_markovChainLaw`).

## References

* [P] M. L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*,
  Wiley, 1994, Chapter 2.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability Learning

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡}

section Kernels

variable (M : MDP 𝓢 𝓐 𝓡) (π : Kernel 𝓢 𝓐)

/-- The law of a round of the stationary policy `π` from its state `s`: the state `s`, an action
`a` drawn from `π s` and a reward drawn from `M.R (s, a)`. -/
noncomputable def stateRoundKernel : Kernel 𝓢 (Round 𝓢 𝓐 𝓡) :=
  Kernel.id ×ₖ (π ⊗ₖ M.R)

lemma stateRoundKernel_def : M.stateRoundKernel π = Kernel.id ×ₖ (π ⊗ₖ M.R) :=
  (rfl)

/-- The law of the next round given the current round `r` under the stationary policy `π`: the
next state is drawn from `M.P (r.obs, r.action)`, then the rest of the round from
`stateRoundKernel`. -/
noncomputable def roundKernel : Kernel (Round 𝓢 𝓐 𝓡) (Round 𝓢 𝓐 𝓡) :=
  (M.stateRoundKernel π ∘ₖ M.P).comap (fun r ↦ (r.obs, r.action)) (by fun_prop)

lemma roundKernel_def :
    M.roundKernel π =
      (M.stateRoundKernel π ∘ₖ M.P).comap (fun r ↦ (r.obs, r.action)) (by fun_prop) :=
  (rfl)

/-- Drawing a state from `μ`, then the rest of the round from `stateRoundKernel`, is drawing the
state from `μ`, then the action and the reward from `π ⊗ₖ M.R`. -/
lemma stateRoundKernel_comp (μ : Measure 𝓢) [SFinite μ] :
    M.stateRoundKernel π ∘ₘ μ = μ ⊗ₘ (π ⊗ₖ M.R) := by
  rw [stateRoundKernel_def, Measure.compProd_eq_comp_prod]

/-- From the round `r`, the next state is drawn from `M.P (r.obs, r.action)`, then the action and
the reward from `π ⊗ₖ M.R`. -/
@[simp]
lemma roundKernel_apply (r : Round 𝓢 𝓐 𝓡) :
    M.roundKernel π r = M.P (r.obs, r.action) ⊗ₘ (π ⊗ₖ M.R) := by
  rw [roundKernel_def, Kernel.comap_apply, Kernel.comp_apply, stateRoundKernel_comp]

lemma stateRoundKernel_apply (s : 𝓢) :
    M.stateRoundKernel π s = Measure.dirac s ⊗ₘ (π ⊗ₖ M.R) := by
  rw [← stateRoundKernel_comp, Measure.dirac_bind (Kernel.measurable _)]

variable [IsMarkovKernel π]

instance : IsMarkovKernel (M.stateRoundKernel π) := by
  rw [stateRoundKernel_def]
  infer_instance

/-- The state and the action of a round drawn from `stateRoundKernel` have law `Kernel.id ×ₖ π`. -/
lemma stateRoundKernel_map_obs_action :
    (M.stateRoundKernel π).map (fun r ↦ (r.obs, r.action)) = Kernel.id ×ₖ π := by
  ext s : 1
  rw [Kernel.map_apply _ (by fun_prop), stateRoundKernel_def, Kernel.prod_apply, Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  have : (fun r : Round 𝓢 𝓐 𝓡 ↦ (r.obs, r.action)) ∘ Prod.mk s = Prod.mk s ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map measurable_prodMk_left measurable_fst,
    ← Kernel.map_apply _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_compProd]

instance : IsMarkovKernel (M.roundKernel π) := by
  rw [roundKernel_def]
  infer_instance

/-- The law of the trajectory of the stationary policy `π` from the state `s`: the path law of the
Markov chain of the rounds, with transition kernel `roundKernel` and initial law
`stateRoundKernel`. -/
noncomputable def trajKernel : Kernel 𝓢 (ℕ → Round 𝓢 𝓐 𝓡) :=
  (M.roundKernel π).markovChainKernel ∘ₖ M.stateRoundKernel π

lemma trajKernel_def :
    M.trajKernel π = (M.roundKernel π).markovChainKernel ∘ₖ M.stateRoundKernel π :=
  (rfl)

instance : IsMarkovKernel (M.trajKernel π) := by
  rw [trajKernel_def]
  infer_instance

/-- The trajectory of `π` from a state drawn from `μ` is the Markov chain of the rounds started
from `stateRoundKernel M π ∘ₘ μ`. -/
lemma trajKernel_comp (μ : Measure 𝓢) :
    M.trajKernel π ∘ₘ μ = markovChainLaw (M.stateRoundKernel π ∘ₘ μ) (M.roundKernel π) := by
  rw [Measure.markovChainLaw_eq_comp, trajKernel_def, Measure.comp_assoc]

/-- The trajectory of `π` from `s` is the Markov chain of the rounds started from
`stateRoundKernel M π s`. -/
lemma trajKernel_apply (s : 𝓢) :
    M.trajKernel π s = markovChainLaw (M.stateRoundKernel π s) (M.roundKernel π) := by
  rw [trajKernel_def, Kernel.comp_apply, Measure.markovChainLaw_eq_comp]

/-- The first round of a trajectory drawn from `trajKernel` has law `stateRoundKernel`. -/
lemma trajKernel_map_eval_zero : (M.trajKernel π).map (fun z ↦ z 0) = M.stateRoundKernel π := by
  ext s : 1
  rw [Kernel.map_apply _ (measurable_pi_apply 0), trajKernel_apply, markovChainLaw_map_eval_zero]

/-- The state and the action of the first round of a trajectory drawn from `trajKernel` have law
`Kernel.id ×ₖ π`. -/
lemma trajKernel_map_obs_action_zero :
    (M.trajKernel π).map (fun z ↦ ((z 0).obs, (z 0).action)) = Kernel.id ×ₖ π := by
  rw [← stateRoundKernel_map_obs_action M π, ← trajKernel_map_eval_zero M π]
  exact Kernel.map_comp_right (M.trajKernel π) (measurable_pi_apply 0)
    (g := fun r : Round 𝓢 𝓐 𝓡 ↦ (r.obs, r.action)) (by fun_prop)

/-- The state of the second round of a trajectory drawn from `trajKernel` has law
`M.stateKernel π`. -/
lemma trajKernel_map_obs_one :
    (M.trajKernel π).map (fun z ↦ (z 1).obs) = M.stateKernel π := by
  have h1 : (M.trajKernel π).map (fun z ↦ z 1) = M.roundKernel π ∘ₖ M.stateRoundKernel π := by
    rw [trajKernel_def, Kernel.map_comp, Kernel.markovChainKernel_map_eval, pow_one]
  have h2 : (M.roundKernel π).map Round.obs =
      M.P.comap (fun r : Round 𝓢 𝓐 𝓡 ↦ (r.obs, r.action)) (by fun_prop) := by
    ext r : 1
    rw [Kernel.map_apply _ (by fun_prop), roundKernel_apply, Kernel.comap_apply]
    exact Measure.fst_compProd _ _
  rw [show (fun z : ℕ → Round 𝓢 𝓐 𝓡 ↦ (z 1).obs) = Round.obs ∘ fun z ↦ z 1 from rfl,
    Kernel.map_comp_right _ (measurable_pi_apply 1) (by fun_prop), h1, Kernel.map_comp, h2,
    ← Kernel.comp_map _ _ (by fun_prop), stateRoundKernel_map_obs_action, stateKernel_def]

/-- Under `trajKernel π s`, the state of the first round is `s`: reading it off the trajectory
gives the product `Kernel.id ×ₖ M.trajKernel π`. -/
lemma trajKernel_map_prodMk_obs_zero :
    (M.trajKernel π).map (fun z ↦ ((z 0).obs, z)) = Kernel.id ×ₖ M.trajKernel π := by
  set K := (M.roundKernel π).markovChainKernel
  have hK : ∀ r : Round 𝓢 𝓐 𝓡,
      (K r).map (fun z ↦ ((z 0).obs, z)) = (K r).map (Prod.mk r.obs) := by
    intro r
    have h := congrArg (fun κ : Kernel _ _ ↦ (κ r).map (Prod.map Round.obs id))
      (Kernel.markovChainKernel_map_prodMk_eval_zero (κ := M.roundKernel π))
    rwa [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)] at h
  ext s : 1
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    trajKernel_def, Kernel.comp_apply, stateRoundKernel_def, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.bind_map measurable_prodMk_left.aemeasurable
      (Kernel.aemeasurable _)]
  have hF : AEMeasurable (fun ar ↦ K (s, ar)) ((π ⊗ₖ M.R) s) :=
    (K.measurable.comp measurable_prodMk_left).aemeasurable
  rw [Measure.map_bind hF (by fun_prop), Measure.map_bind hF (by fun_prop)]
  exact Measure.bind_congr_right (.of_forall fun ar ↦ hK (s, ar))

end Kernels

/-! ### The step kernels of a stationary Markov policy in the environment of an MDP -/

section StepKernel

variable [Nonempty 𝓢] (M : MDP 𝓢 𝓐 𝓡) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (μ : Measure 𝓢)

/-- The first round of a run of the stationary policy `π` from `μ` has law
`stateRoundKernel M π ∘ₘ μ`. -/
lemma stepKernel_markov_env_zero [IsProbabilityMeasure μ] (h : Hist 𝓢 𝓐 𝓡 0) :
    stepKernel (Algorithm.markov fun _ ↦ π) (M.env μ) 0 h = M.stateRoundKernel π ∘ₘ μ := by
  rw [stepKernel_zero, obsZero_env, Algorithm.policyZero_markov, feedbackZero_env,
    stateRoundKernel_comp]

/-- The round `n + 1` of a run of the stationary policy `π` has law `roundKernel M π` at the round
`n`, whatever the earlier rounds. -/
lemma stepKernel_markov_env_add_one (n : ℕ) :
    stepKernel (Algorithm.markov fun _ ↦ π) (M.env μ) (n + 1) =
      (M.roundKernel π).comap (fun h ↦ h (Fin.last n)) (measurable_pi_apply _) := by
  ext h : 1
  rw [stepKernel_def, Kernel.compProd_apply_eq_compProd_sectR, env_obs_add_one_apply,
    Kernel.comap_apply, roundKernel_apply]
  congr 1
  ext s : 1
  rw [Kernel.sectR_apply, Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.compProd_apply_eq_compProd_sectR, Algorithm.policy_markov, Kernel.prodMkLeft_apply]
  congr 1
  ext a : 1
  rw [Kernel.sectR_apply, Kernel.sectR_apply, env_feedback_apply]

end StepKernel

/-! ### The rounds of a run form a Markov chain -/

section Runs

variable [Nonempty 𝓢] {M : MDP 𝓢 𝓐 𝓡} {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] {μ : Measure 𝓢}
  [IsProbabilityMeasure μ] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓡}

/-- **The rounds of a run of a stationary policy form a Markov chain**, with initial law
`stateRoundKernel M π ∘ₘ μ` and transition kernel `roundKernel M π`. -/
theorem hasLaw_trajectory_markovChainLaw
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) :
    HasLaw (trajectory O A Y) (markovChainLaw (M.stateRoundKernel π ∘ₘ μ) (M.roundKernel π)) P := by
  refine (hasLaw_markovChainLaw_iff (X := step O A Y) _ _
    fun n ↦ (h.measurable_step n).aemeasurable).2 ⟨?_, fun n ↦ ?_⟩
  · rw [h.hasLaw_step_zero.map_eq, ← stepKernel_zero _ _ default,
      stepKernel_markov_env_zero]
  · have hc := (h.hasCondDistrib_step (n + 1)).map_eq
    rw [stepKernel_markov_env_add_one] at hc
    -- `history O A Y (n + 1)` is by definition the prefix `fun ω i ↦ step O A Y i ω`.
    rw [prefixLaw_def, blockLaw_def]
    exact hc

/-- The trajectory of a run of the stationary policy `π` from `μ` has law
`trajKernel M π ∘ₘ μ`. -/
theorem hasLaw_trajectory_trajKernel
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) :
    HasLaw (trajectory O A Y) (M.trajKernel π ∘ₘ μ) P := by
  rw [trajKernel_comp]
  exact hasLaw_trajectory_markovChainLaw h

/-- The trajectory law of the stationary policy `π` from `μ` is `trajKernel M π ∘ₘ μ`. -/
theorem trajMeasure_markov_env :
    trajMeasure (Algorithm.markov fun _ ↦ π) (M.env μ) = M.trajKernel π ∘ₘ μ := by
  have h := (hasLaw_trajectory_trajKernel (IT.isAlgEnvSeq_trajMeasure
    (Algorithm.markov fun _ ↦ π) (M.env μ))).map_eq
  -- On the trajectory space, the coordinate processes reassemble every round.
  rwa [show trajectory IT.obs IT.action IT.feedback = id from rfl, Measure.map_id] at h

/-- **Markov property** of the runs of a stationary policy: given the rounds before `n`, the
rounds from `n` on (`processShift (step O A Y) n`) have the law of the trajectory of `π` started
from the law `(M.env μ).obs n` of the state of round `n`, which is `μ` for `n = 0` and
`M.P (s, a)` at the state `s` and action `a` of round `n - 1` otherwise. -/
theorem hasCondDistrib_processShift_history
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) (n : ℕ) :
    HasCondDistrib (processShift (step O A Y) n) (history O A Y n)
      (M.trajKernel π ∘ₖ (M.env μ).obs n) P := by
  have hstep := h.measurable_step
  cases n with
  | zero =>
    rw [history_zero, hasCondDistrib_const_iff, Kernel.comp_apply, ← Environment.obsZero_def,
      obsZero_env, processShift_eq_shift_iterate, Function.iterate_zero, Function.id_comp]
    exact hasLaw_trajectory_trajKernel h
  | succ n =>
    have h1 := (hasLaw_trajectory_markovChainLaw h).prefix_processShift_markovChainLaw
      (X := step O A Y) n
    have hhist := measurable_history h.measurable_obs h.measurable_action h.measurable_feedback
    refine ⟨((hhist (n + 1)).prodMk (measurable_processShift fun _ ↦ hstep _)).aemeasurable, ?_⟩
    have hshift : processShift (step O A Y) (n + 1) = shift _ ∘ processShift (step O A Y) n := by
      simp only [processShift_eq_shift_iterate, Function.iterate_succ', Function.comp_assoc]
    calc P.map (fun ω ↦ (history O A Y (n + 1) ω, processShift (step O A Y) (n + 1) ω))
        = (P.map fun ω ↦ ((fun i : Fin (n + 1) ↦ step O A Y i ω),
            processShift (step O A Y) n ω)).map (Prod.map id (shift _)) := by
          rw [Measure.map_map (measurable_id.prodMap measurable_shift)
            ((measurable_pi_iff.2 fun i : Fin (n + 1) ↦ hstep i).prodMk
              (measurable_processShift fun _ ↦ hstep _)), hshift]
          -- `history O A Y (n + 1)` is by definition the prefix `fun ω i ↦ step O A Y i ω`.
          rfl
      _ = _ := by
          rw [h1.map_eq, ← Measure.compProd_map measurable_shift, prefixLaw_def, blockLaw_def]
          congr 1
          ext hist : 1
          rw [Kernel.map_apply _ measurable_shift, Kernel.comap_apply, ← Kernel.map_apply _
            measurable_shift, Kernel.markovChainKernel_map_shift, Kernel.comp_apply,
            Kernel.comp_apply, env_obs_add_one_apply, trajKernel_def, ← Measure.comp_assoc,
            roundKernel_apply, stateRoundKernel_comp]

/-- **Markov property** of the runs of a stationary policy: given the rounds before `n` and the
state `s` of round `n`, the rounds from `n` on have law `trajKernel M π s`. -/
theorem hasCondDistrib_processShift_history_obs
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) (n : ℕ) :
    HasCondDistrib (processShift (step O A Y) n) (fun ω ↦ (history O A Y n ω, O n ω))
      (Kernel.prodMkLeft (Hist 𝓢 𝓐 𝓡 n) (M.trajKernel π)) P := by
  have h1 := (hasCondDistrib_processShift_history h n).prodMkLeft_of_comp
    (f := fun z ↦ (z 0).obs) (by fun_prop) (trajKernel_map_prodMk_obs_zero M π)
  convert h1 using 3 with ω
  rw [processShift_apply, add_zero, obs_step]

/-- **The states of a run of a stationary policy form a Markov chain**, with initial law `μ` and
transition kernel `M.stateKernel π`. -/
theorem hasLaw_obs_markovChainLaw
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) :
    HasLaw (fun ω n ↦ O n ω) (markovChainLaw μ (M.stateKernel π)) P := by
  refine (hasLaw_markovChainLaw_iff _ _ fun n ↦ (h.measurable_obs n).aemeasurable).2
    ⟨(hasLaw_obs_zero h).map_eq, fun n ↦ ?_⟩
  have h1 := (hasCondDistrib_processShift_history_obs h n).comp_left
    (f := fun z ↦ (z 1).obs) (by fun_prop)
  rw [Kernel.map_prodMkLeft, trajKernel_map_obs_one] at h1
  have hsnoc : Measurable fun p : Hist 𝓢 𝓐 𝓡 n × 𝓢 ↦
      (Fin.snoc (fun i ↦ (p.1 i).obs) p.2 : Fin (n + 1) → 𝓢) := by
    convert (MeasurableEquiv.finSuccProd 𝓢 n).symm.measurable.comp
      (f := fun p : Hist 𝓢 𝓐 𝓡 n × 𝓢 ↦ ((fun i ↦ (p.1 i).obs), p.2)) (by fun_prop) using 1
    funext p
    simp [MeasurableEquiv.finSuccProd_symm_apply]
  have h2 : HasCondDistrib (O (n + 1)) (fun ω ↦ (history O A Y n ω, O n ω))
      ((M.stateKernel π).comap (fun w : Fin (n + 1) → 𝓢 ↦ w (Fin.last n))
        (measurable_pi_apply _) |>.comap _ hsnoc) P := by
    convert h1 using 2
    · funext ω
      rw [Function.comp_apply, processShift_apply, obs_step]
    · ext p : 1
      rw [Kernel.prodMkLeft_apply, Kernel.comap_apply, Kernel.comap_apply, Fin.snoc_last]
  have h3 := h2.comp_right
  have hfun : ((fun p : Hist 𝓢 𝓐 𝓡 n × 𝓢 ↦ (Fin.snoc (fun i ↦ (p.1 i).obs) p.2 :
      Fin (n + 1) → 𝓢)) ∘ fun ω ↦ (history O A Y n ω, O n ω)) =
      fun ω (i : Fin (n + 1)) ↦ O i ω := by
    funext ω i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp [history_apply]
  rw [hfun] at h3
  rw [prefixLaw_def, blockLaw_def]
  exact h3.map_eq

/-- **The state-action pairs of a run of a stationary policy form a Markov chain**, with initial
law `μ ⊗ₘ π` and transition kernel `M.saKernel π`. -/
theorem hasLaw_obs_action_markovChainLaw
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) :
    HasLaw (fun ω n ↦ (O n ω, A n ω)) (markovChainLaw (μ ⊗ₘ π) (M.saKernel π)) P := by
  refine (hasLaw_markovChainLaw_iff _ _ fun n ↦ ((h.measurable_obs n).prodMk
    (h.measurable_action n)).aemeasurable).2 ⟨?_, fun n ↦ ?_⟩
  · have h0 := (hasLaw_obs_action_markov h 0).map_eq
    rwa [stateMarginal_zero] at h0
  have h1 := (hasCondDistrib_processShift_history h (n + 1)).comp_left
    (f := fun z ↦ ((z 0).obs, (z 0).action)) (by fun_prop)
  rw [Kernel.map_comp, trajKernel_map_obs_action_zero] at h1
  have h2 : HasCondDistrib (fun ω ↦ (O (n + 1) ω, A (n + 1) ω)) (history O A Y (n + 1))
      ((M.saKernel π).comap (fun w : Fin (n + 1) → 𝓢 × 𝓐 ↦ w (Fin.last n))
        (measurable_pi_apply _) |>.comap (fun hist i ↦ ((hist i).obs, (hist i).action))
        (by fun_prop)) P := by
    convert h1 using 2 with ω
    · simp only [Function.comp_apply, processShift_apply, add_zero, obs_step, action_step]
    · ext hist : 1
      rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.comp_apply, env_obs_add_one_apply,
        saKernel_def, Kernel.comp_apply]
  -- the prefix of the state-action pairs is by definition a function of `history O A Y (n + 1)`
  rw [prefixLaw_def, blockLaw_def]
  exact h2.comp_right.map_eq

end Runs

section Deterministic

variable [Nonempty 𝓢] (M : MDP 𝓢 𝓐 𝓡)

/-- The trajectory of `π` from `s` is the trajectory law of the run of `π` from `Measure.dirac s`.
-/
lemma trajKernel_apply_eq_trajMeasure (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (s : 𝓢) :
    M.trajKernel π s =
      trajMeasure (Algorithm.markov fun _ ↦ π) (M.env (Measure.dirac s)) := by
  rw [trajMeasure_markov_env, Measure.dirac_bind (Kernel.measurable _)]

/-- The trajectory law `policyMeasure` of a deterministic stationary policy is the trajectory
kernel of its deterministic kernel. -/
lemma policyMeasure_eq_trajKernel (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    M.policyMeasure π hπ s = M.trajKernel (Kernel.deterministic π hπ) s := by
  rw [policyMeasure_def, policyAlg_eq_markov, trajKernel_apply_eq_trajMeasure]

/-- The trajectory law of a deterministic stationary policy depends measurably on the initial
state. -/
lemma measurable_policyMeasure (π : 𝓢 → 𝓐) (hπ : Measurable π) :
    Measurable (M.policyMeasure π hπ) := by
  simp_rw [funext (policyMeasure_eq_trajKernel M π hπ)]
  exact Kernel.measurable _

end Deterministic

end Learning.MDP
