/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import LeanMachineLearning.SequentialLearning.Deterministic
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import LMLExplore.Probability.HasCondDistrib
public import LMLExplore.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Independence.Conditional
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Markov decision processes and their environments

A Markov decision process (MDP) with state space `𝓢`, action space `𝓐` and reward space `𝓡` is
given by a transition kernel `P : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel `R : Kernel (𝓢 × 𝓐) 𝓡`,
both Markov. It defines an environment of LML's interaction protocol: the observation of each
round is the current state and the feedback is the reward. From an initial law `μ₀` of the
first state,
* the first state has law `μ₀`;
* the state of round `n + 1` has law `P (s, a)`, where `s` and `a` are the state and action of
  round `n`;
* the reward of round `n` has law `R (s, a)`, where `s` and `a` are the state and action of
  round `n`.

Every algorithm of the interaction protocol, run in this environment, is a history-dependent
policy of the MDP, and the laws of its runs are those of the MDP controlled by that policy.

The definitions of `MDP`, `env`, `measurable_env`, `policyAlg`, `policyMeasure`, `stateLaw` and
`meanReward` are adapted from the `mdp` branch of LML
(`LeanMachineLearning/ReinforcementLearning/MDP/Basic.lean`, by Rémy Degenne), with its names and
namespaces: the structure is the root `MDP` and its API lives in `Learning.MDP`, which provides
the dot notation `M.env` when the namespace `Learning` is open.

## Main definitions

* `MDP 𝓢 𝓐 𝓡`: a Markov decision process.
* `Learning.MDP.env M μ₀`: the environment of `M` started from the initial law `μ₀`.
* `Learning.MDP.policyAlg π hπ`: the algorithm playing the deterministic stationary policy `π`.
* `Learning.MDP.policyMeasure M π hπ s`: the law of the trajectory of `π` started at `s`.
* `Learning.MDP.stateLaw M π hπ s`: the law of the state-action trajectory of `π` from `s`.
* `Learning.MDP.meanReward R p`: the mean reward of the state-action pair `p`.

## Main statements

For every algorithm-environment sequence `IsAlgEnvSeq O A Y alg (M.env μ) P`:
* `Learning.MDP.hasLaw_obs_zero`: the first state `O 0` has law `μ`, for a probability measure
  `μ`;
* `Learning.MDP.hasCondDistrib_obs_add_one_history`: the state `O (n + 1)` has conditional law
  `M.P (O n, A n)` given the history up to round `n`;
* `Learning.MDP.hasLaw_obs_add_one`: the state `O (n + 1)` has law `M.P ∘ₘ L`, where `L` is the
  law of the state-action pair `(O n, A n)`;
* `Learning.MDP.hasCondDistrib_feedback_history`: the reward `Y n` has conditional law
  `M.R (O n, A n)` given the history before round `n`, `O n` and `A n`;
* `Learning.MDP.ae_abs_feedback_le`, `Learning.MDP.integral_feedback`: for real rewards bounded
  by `C`, the reward `Y n` is almost surely bounded by `C`, and its expectation is the integral of
  the mean reward against the law of `(O n, A n)`;
* `Learning.MDP.hasCondDistrib_feedback_obs_add_one`: given the history before round `n`, `O n`
  and `A n`, the pair `(Y n, O (n + 1))` has conditional law `M.R (O n, A n) ⊗ M.P (O n, A n)`;
* `Learning.MDP.condIndepFun_feedback_obs_add_one`: hence `Y n` and `O (n + 1)` are
  conditionally independent given the history before round `n`, `O n` and `A n`.
-/

public section

open MeasureTheory ProbabilityTheory Learning

/-- A Markov decision process with state space `𝓢`, action space `𝓐` and reward space `𝓡`,
described by a transition kernel `P : Kernel (𝓢 × 𝓐) 𝓢` and a reward kernel
`R : Kernel (𝓢 × 𝓐) 𝓡`, both Markov. See `Learning.MDP.env` for its environment. -/
structure MDP (𝓢 𝓐 𝓡 : Type*) [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] [MeasurableSpace 𝓡] where
  /-- The transition kernel: the law of the next state given the current state and action. -/
  P : Kernel (𝓢 × 𝓐) 𝓢
  /-- The transition kernel is a Markov kernel. -/
  [hP : IsMarkovKernel P]
  /-- The reward kernel: the law of the reward given the current state and action. -/
  R : Kernel (𝓢 × 𝓐) 𝓡
  /-- The reward kernel is a Markov kernel. -/
  [hR : IsMarkovKernel R]

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡}

instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.P := M.hP
instance (M : MDP 𝓢 𝓐 𝓡) : IsMarkovKernel M.R := M.hR

/-! ### Mean rewards -/

section MeanReward

variable [NormedAddCommGroup 𝓡] [NormedSpace ℝ 𝓡]

/-- The mean reward `r (s, a) = 𝔼[R (s, a)]` of a state-action pair, for a reward kernel `R`. -/
noncomputable def meanReward (R : Kernel (𝓢 × 𝓐) 𝓡) (p : 𝓢 × 𝓐) : 𝓡 := (R p)[id]

lemma meanReward_def (R : Kernel (𝓢 × 𝓐) 𝓡) (p : 𝓢 × 𝓐) :
    meanReward R p = ∫ y, y ∂(R p) :=
  (rfl)

/-- The mean reward is a measurable function of the state-action pair. -/
lemma measurable_meanReward [SecondCountableTopology 𝓡] [BorelSpace 𝓡]
    (R : Kernel (𝓢 × 𝓐) 𝓡) : Measurable (meanReward R) :=
  (stronglyMeasurable_id.integral_kernel (κ := R)).measurable

/-- Rewards bounded by `C` have a mean bounded by `C`. -/
lemma norm_meanReward_le (R : Kernel (𝓢 × 𝓐) 𝓡) [IsMarkovKernel R] {p : 𝓢 × 𝓐} {C : ℝ}
    (hR : ∀ᵐ y ∂(R p), ‖y‖ ≤ C) : ‖meanReward R p‖ ≤ C := by
  simpa [meanReward_def] using norm_integral_le_of_norm_le_const hR

end MeanReward

/-! ### Deterministic stationary policies and their trajectory laws -/

/-- The deterministic stationary policy `π` as an algorithm: it plays `π s` in the current
state `s`. -/
noncomputable def policyAlg (π : 𝓢 → 𝓐) (hπ : Measurable π) : Algorithm 𝓢 𝓐 𝓡 :=
  Algorithm.deterministic (fun _ p ↦ π p.2) fun _ ↦ hπ.comp measurable_snd

/-- The policy of `policyAlg π hπ` at every round is the deterministic kernel playing `π` in the
current state. -/
@[simp]
lemma policyAlg_policy (π : 𝓢 → 𝓐) (hπ : Measurable π) (n : ℕ) :
    (policyAlg π hπ : Algorithm 𝓢 𝓐 𝓡).policy n =
      Kernel.deterministic (fun p : Hist 𝓢 𝓐 𝓡 n × 𝓢 ↦ π p.2) (hπ.comp measurable_snd) :=
  (rfl)

instance (π : 𝓢 → 𝓐) (hπ : Measurable π) :
    (policyAlg π hπ : Algorithm 𝓢 𝓐 𝓡).IsDeterministic := by
  unfold policyAlg
  infer_instance

/-! ### The environment of an MDP -/

open Classical in
/-- The environment of the MDP `M` started from the initial law `μ₀`: the observation of a round
is the current state and its feedback is the reward.
* The state of round `0` has law `μ₀`, or the Dirac mass at an arbitrary state if `μ₀` is not a
  probability measure.
* The state of round `n + 1` has law `M.P (s, a)`, where `s` and `a` are the state and action of
  round `n`.
* The reward of round `n` has law `M.R (s, a)`, where `s` and `a` are the state and action of
  round `n`. -/
protected noncomputable def env [h𝓢 : Nonempty 𝓢] (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) :
    Environment 𝓢 𝓐 𝓡 where
  obs
  | 0 => Kernel.const _ (if IsProbabilityMeasure μ₀ then μ₀ else Measure.dirac h𝓢.some)
  | n + 1 => M.P.comap (fun h ↦ ((h (Fin.last n)).obs, (h (Fin.last n)).action)) (by fun_prop)
  feedback := fun _ ↦ M.R.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop)
  isMarkovKernel_obs n := by
    cases n
    · split_ifs <;> infer_instance
    · infer_instance

variable [Nonempty 𝓢] {M : MDP 𝓢 𝓐 𝓡} {μ₀ : Measure 𝓢}

open Classical in
/-- The observation kernel of round `0` of the environment of `M` is the constant kernel `μ₀`, or
the Dirac mass at an arbitrary state if `μ₀` is not a probability measure. -/
lemma env_obs_zero (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) :
    (M.env μ₀).obs 0 = Kernel.const _
      (if IsProbabilityMeasure μ₀ then μ₀ else Measure.dirac (Classical.arbitrary 𝓢)) :=
  (rfl)

/-- The first state of the environment of `M` has law `μ₀` when `μ₀` is a probability measure. -/
@[simp]
lemma obsZero_env (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) [hμ₀ : IsProbabilityMeasure μ₀] :
    (M.env μ₀).obsZero = μ₀ := by
  simp [Environment.obsZero_def, env_obs_zero, hμ₀]

/-- If `μ₀` is not a probability measure, the first state of the environment of `M` is an
arbitrary fixed state. -/
lemma obsZero_env_of_not_isProbabilityMeasure (M : MDP 𝓢 𝓐 𝓡) (h : ¬IsProbabilityMeasure μ₀) :
    (M.env μ₀).obsZero = Measure.dirac (Classical.arbitrary 𝓢) := by
  simp [Environment.obsZero_def, env_obs_zero, h]

/-- The observation kernel of round `n + 1` of the environment of `M` is the transition kernel,
applied to the state and action of round `n`. -/
lemma env_obs_add_one (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) :
    (M.env μ₀).obs (n + 1) = M.P.comap
      (fun h : Hist 𝓢 𝓐 𝓡 (n + 1) ↦ ((h (Fin.last n)).obs, (h (Fin.last n)).action))
      (by fun_prop) :=
  (rfl)

@[simp]
lemma env_obs_add_one_apply (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) (h : Hist 𝓢 𝓐 𝓡 (n + 1)) :
    (M.env μ₀).obs (n + 1) h = M.P ((h (Fin.last n)).obs, (h (Fin.last n)).action) := by
  rw [env_obs_add_one, Kernel.comap_apply]

/-- The feedback kernel of every round of the environment of `M` is the reward kernel, applied to
the current state and action. -/
lemma env_feedback (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ) :
    (M.env μ₀).feedback n =
      M.R.comap (fun p : (Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐 ↦ (p.1.2, p.2)) (by fun_prop) :=
  (rfl)

@[simp]
lemma env_feedback_apply (M : MDP 𝓢 𝓐 𝓡) (μ₀ : Measure 𝓢) (n : ℕ)
    (p : (Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) :
    (M.env μ₀).feedback n p = M.R (p.1.2, p.2) := by
  rw [env_feedback, Kernel.comap_apply]

/-- The environment of an MDP depends measurably on the initial law. -/
lemma measurable_env (M : MDP 𝓢 𝓐 𝓡) : Measurable M.env := by
  rw [measurable_environment_iff]
  refine fun n ↦ ⟨?_, by simp_rw [env_feedback]; fun_prop⟩
  cases n with
  | zero =>
    simp_rw [env_obs_zero]
    exact Kernel.measurable_const.comp <| Measurable.ite
      ProbabilityMeasure.measurableSet_isProbabilityMeasure (by fun_prop) (by fun_prop)
  | succ n => simp_rw [env_obs_add_one]; fun_prop

/-! ### Trajectory laws of deterministic stationary policies -/

/-- The law of the trajectory of the deterministic stationary policy `π` started at the
state `s`. -/
noncomputable def policyMeasure (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    Measure (ℕ → Round 𝓢 𝓐 𝓡) :=
  trajMeasure (policyAlg π hπ) (M.env (Measure.dirac s))

lemma policyMeasure_def (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    M.policyMeasure π hπ s = trajMeasure (policyAlg π hπ) (M.env (Measure.dirac s)) :=
  (rfl)

instance (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    IsProbabilityMeasure (M.policyMeasure π hπ s) := by
  rw [policyMeasure_def]
  infer_instance

/-- The law of the state-action trajectory of the deterministic stationary policy `π` started
at the state `s`: the trajectory law `policyMeasure` with the rewards forgotten. -/
noncomputable def stateLaw (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    Measure (ℕ → 𝓢 × 𝓐) :=
  (M.policyMeasure π hπ s).map (fun h n ↦ ((h n).obs, (h n).action))

lemma stateLaw_def (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    M.stateLaw π hπ s = (M.policyMeasure π hπ s).map (fun h n ↦ ((h n).obs, (h n).action)) :=
  (rfl)

instance (M : MDP 𝓢 𝓐 𝓡) (π : 𝓢 → 𝓐) (hπ : Measurable π) (s : 𝓢) :
    IsProbabilityMeasure (M.stateLaw π hπ s) := by
  rw [stateLaw_def]
  infer_instance

/-! ### Runs in the environment of an MDP -/

section Runs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {O : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓡} {alg : Algorithm 𝓢 𝓐 𝓡} {μ : Measure 𝓢}

/-- In a run in the environment of an MDP started from the probability measure `μ`, the first
state has law `μ`. -/
lemma hasLaw_obs_zero [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P) :
    HasLaw (O 0) μ P := by
  simpa using h.hasLaw_obs_zero

/-- In a run in the environment of an MDP, the state of round `n + 1` has conditional law
`M.P (s, a)` given the history of the rounds up to `n`, where `s` and `a` are the state and
action of round `n`. -/
lemma hasCondDistrib_obs_add_one_history (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (O (n + 1)) (history O A Y (n + 1))
      (M.P.comap (fun h ↦ ((h (Fin.last n)).obs, (h (Fin.last n)).action)) (by fun_prop) :
        Kernel (Hist 𝓢 𝓐 𝓡 (n + 1)) 𝓢) P := by
  rw [← env_obs_add_one M μ]
  exact h.hasCondDistrib_obs (n + 1)

/-- Markov property of the states: in a run in the environment of an MDP, the state of
round `n + 1` has conditional law `M.P` given the state and action of round `n`. -/
lemma hasCondDistrib_obs_add_one [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (O (n + 1)) (fun ω ↦ (O n ω, A n ω)) M.P P :=
  (hasCondDistrib_obs_add_one_history h n).comp_right

/-- In a run in the environment of an MDP, the law of the state of round `n + 1` is the law of
the state-action pair of round `n` composed with the transition kernel `M.P`. -/
lemma hasLaw_obs_add_one [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasLaw (O (n + 1)) (M.P ∘ₘ P.map (fun ω ↦ (O n ω, A n ω))) P :=
  (hasCondDistrib_obs_add_one h n).hasLaw_comp

/-- In a run in the environment of an MDP, the reward of round `n` has conditional law
`M.R (s, a)` given the history before round `n`, the state `s` and the action `a` of
round `n`. -/
lemma hasCondDistrib_feedback_history (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      (M.R.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop) : Kernel ((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) 𝓡)
      P := by
  rw [← env_feedback M μ n]
  exact h.hasCondDistrib_feedback n

/-- In a run in the environment of an MDP, the reward of round `n` has conditional law `M.R`
given the state and action of round `n`. -/
lemma hasCondDistrib_feedback [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    HasCondDistrib (Y n) (fun ω ↦ (O n ω, A n ω)) M.R P :=
  (hasCondDistrib_feedback_history h n).comp_right

/-- Along a run in an MDP with rewards bounded by `C`, the reward of every round is almost surely
bounded by `C`. -/
lemma ae_abs_feedback_le [SFinite P] {M : MDP 𝓢 𝓐 ℝ} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓢 𝓐 ℝ} {C : ℝ}
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (n : ℕ) :
    ∀ᵐ ω ∂P, |Y n ω| ≤ C :=
  HasCondDistrib.ae_mem (hasCondDistrib_feedback h n) (t := {x | |x| ≤ C})
    (measurableSet_le (by fun_prop) measurable_const) hR

/-- Along a run in an MDP with bounded rewards, the expected reward of round `n` is the integral
of the mean reward against the law of the state-action pair of round `n`. -/
theorem integral_feedback [IsFiniteMeasure P] {M : MDP 𝓢 𝓐 ℝ} {Y : ℕ → Ω → ℝ}
    {alg : Algorithm 𝓢 𝓐 ℝ} {C : ℝ}
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (n : ℕ) :
    ∫ ω, Y n ω ∂P = ∫ p, meanReward M.R p ∂(P.map fun ω ↦ (O n ω, A n ω)) := by
  have h_law := hasCondDistrib_feedback h n
  have h_int : Integrable (fun q : (𝓢 × 𝓐) × ℝ ↦ q.2)
      (P.map (fun ω ↦ (O n ω, A n ω)) ⊗ₘ M.R) :=
    .of_bound measurable_snd.aestronglyMeasurable C <|
      Measure.ae_compProd_of_ae_ae (measurableSet_le (by fun_prop) measurable_const)
        (.of_forall hR)
  have h_eq := h_law.integral_comp (f := Prod.snd) measurable_snd.aestronglyMeasurable
  simp only [Function.comp_def] at h_eq
  rw [h_eq, Measure.integral_compProd h_int]
  simp_rw [meanReward_def]

/-- The measurable equivalence between `((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) × 𝓡` and the histories of
`n + 1` rounds, appending the round `(s, a, y)` to a history of `n` rounds. -/
private def snocEquiv (n : ℕ) : ((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) × 𝓡 ≃ᵐ Hist 𝓢 𝓐 𝓡 (n + 1) :=
  (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodAssoc).trans
    (MeasurableEquiv.finSuccProd (Round 𝓢 𝓐 𝓡) n).symm

omit [Nonempty 𝓢] in
/-- `snocEquiv n` appends the round `(s, a, y)` to the history `h`. -/
@[simp]
private lemma snocEquiv_apply (n : ℕ) (h : Hist 𝓢 𝓐 𝓡 n) (s : 𝓢) (a : 𝓐) (y : 𝓡) :
    (snocEquiv n : ((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) × 𝓡 ≃ᵐ Hist 𝓢 𝓐 𝓡 (n + 1)) (((h, s), a), y) =
      Fin.snoc (α := fun _ ↦ Round 𝓢 𝓐 𝓡) h (s, a, y) := by
  simp only [snocEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.finSuccProd_symm_apply]
  rfl

/-- In a run in the environment of an MDP, given the history before round `n`, the state `s` and
the action `a` of round `n`, the pair formed by the reward of round `n` and the state of
round `n + 1` has conditional law `M.R (s, a) ⊗ M.P (s, a)`: the reward and the next state are
drawn independently. -/
lemma hasCondDistrib_feedback_obs_add_one [SFinite P] (h : IsAlgEnvSeq O A Y alg (M.env μ) P)
    (n : ℕ) :
    HasCondDistrib (fun ω ↦ (Y n ω, O (n + 1) ω))
      (fun ω ↦ ((history O A Y n ω, O n ω), A n ω))
      ((M.R ×ₖ M.P).comap (fun p ↦ (p.1.2, p.2)) (by fun_prop) :
        Kernel ((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) (𝓡 × 𝓢)) P := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  -- the next state, given the history of the rounds up to `n` in the form `(((h, s), a), y)`
  have h_obs : HasCondDistrib (O (n + 1))
      (fun ω ↦ (((history O A Y n ω, O n ω), A n ω), Y n ω))
      ((M.P.comap (fun p ↦ (p.1.2, p.2)) (by fun_prop) :
        Kernel ((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) 𝓢).prodMkRight 𝓡) P := by
    have h_hist : history O A Y (n + 1) =
        (snocEquiv n : ((Hist 𝓢 𝓐 𝓡 n × 𝓢) × 𝓐) × 𝓡 ≃ᵐ Hist 𝓢 𝓐 𝓡 (n + 1)) ∘
          fun ω ↦ (((history O A Y n ω, O n ω), A n ω), Y n ω) := by
      ext ω : 1
      simp only [history_succ, Function.comp_apply, snocEquiv_apply,
        MeasurableEquiv.finSuccProd_symm_apply]
      rw [← Round.mk_obs_action_feedback (step O A Y n ω), obs_step, action_step, feedback_step]
    have h' := hasCondDistrib_obs_add_one_history h n
    rw [h_hist, hasCondDistrib_measurableEquiv_comp_right_iff] at h'
    convert h' using 1
    ext ⟨⟨⟨h, s⟩, a⟩, y⟩ : 1
    simp
  have h_prod := (hasCondDistrib_feedback_history h n).compProd h_obs
  rwa [Kernel.compProd_prodMkRight_eq_prod, ← Kernel.comap_prod] at h_prod

/-- In a run in the environment of an MDP, the reward of round `n` and the state of round `n + 1`
are conditionally independent given the history before round `n`, the state and the action of
round `n`. -/
lemma condIndepFun_feedback_obs_add_one [IsFiniteMeasure P] [StandardBorelSpace Ω]
    [StandardBorelSpace 𝓢] [StandardBorelSpace 𝓡] [Nonempty 𝓡]
    (h : IsAlgEnvSeq O A Y alg (M.env μ) P) (n : ℕ) :
    Y n ⟂ᵢ[fun ω ↦ ((history O A Y n ω, O n ω), A n ω),
      ((h.measurable_history n).prodMk (h.measurable_obs n)).prodMk (h.measurable_action n); P]
      O (n + 1) := by
  have hO := h.measurable_obs
  have hA := h.measurable_action
  have hY := h.measurable_feedback
  have h_pair := hasCondDistrib_feedback_obs_add_one h n
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib (by fun_prop) (by fun_prop)
    (by fun_prop)]
  have h_fst := h_pair.fst.condDistrib_ae_eq
  have h_snd := h_pair.snd.condDistrib_ae_eq
  simp only [Kernel.comap_prod, Kernel.fst_prod, Kernel.snd_prod] at h_fst h_snd
  rw [h_pair.map_eq, Measure.compProd_eq_comp_prod]
  refine Measure.bind_congr_right ?_
  filter_upwards [h_fst, h_snd] with p h1 h2
  simp only [Kernel.prod_apply, Kernel.comap_apply] at h1 h2 ⊢
  rw [h1, h2]

end Runs

end Learning.MDP
