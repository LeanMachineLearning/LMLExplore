/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Basic
public import LMLExplore.Probability.Kernel.Composition.Comp
public import LMLExplore.SequentialLearning.Algorithms.Markov

/-!
# Markov policies of a Markov decision process and their state-action marginals

A Markov policy `π : ℕ → Kernel 𝓢 𝓐` of an MDP `M` chooses the action of round `n` from `π n s`,
where `s` is the current state; it is run as `Algorithm.markov π`. A stationary policy is a Markov
kernel `π : Kernel 𝓢 𝓐`, run as the constant Markov policy.

Under a Markov policy, the laws of the state-action pairs `(S n, A n)` of every run are determined
by the initial law `μ`: the law of `S n` is the measure `M.stateMarginal π μ n` defined by
`μ₀ = μ` and `μₙ₊₁ = M.P ∘ₘ (μₙ ⊗ₘ π n)`, and the law of `(S n, A n)` is `μₙ ⊗ₘ π n`. In
particular the expected mean reward of every round depends only on `π` and `μ`. Under a stationary
policy `π`, these marginals are given by powers of two kernels:
* the state kernel `M.stateKernel π = M.P ∘ₖ (Kernel.id ×ₖ π)`, which draws an action from `π s`
  and then a next state from `M.P (s, a)`; the state of round `n` has law
  `(M.stateKernel π ^ n) ∘ₘ μ`;
* the state-action kernel `M.saKernel π = (Kernel.id ×ₖ π) ∘ₖ M.P`, which draws a next state from
  `M.P (s, a)` and then an action from `π`; the state-action pair of round `n` has law
  `(M.saKernel π ^ n) ∘ₘ (μ ⊗ₘ π)`.

Integrating a function against `M.stateKernel π s` averages over the actions `a` of `π s` its
integral against `M.P (s, a)` (`integral_stateKernel`).

The deterministic stationary policies `policyAlg π hπ` are Markov policies
(`policyAlg_eq_markov`).

## Main definitions

* `Learning.MDP.stateKernel M π`: the transition kernel of the states under the stationary policy
  `π`.
* `Learning.MDP.saKernel M π`: the transition kernel of the state-action pairs under the
  stationary policy `π`.
* `Learning.MDP.stateMarginal M π μ n`: the law of the state of round `n` under the Markov policy
  `π` from the initial law `μ`.

## Main statements

For every run `IsAlgEnvSeq O A Y (Algorithm.markov π) (M.env μ) P` from a probability measure `μ`:
* `Learning.MDP.hasLaw_obs_markov`: the state `O n` has law `M.stateMarginal π μ n`;
* `Learning.MDP.hasLaw_obs_action_markov`: the pair `(O n, A n)` has law
  `M.stateMarginal π μ n ⊗ₘ π n`;
* `Learning.MDP.hasLaw_obs_markov_const`, `Learning.MDP.hasLaw_obs_action_markov_const`: for a
  stationary policy, these laws are `(M.stateKernel π ^ n) ∘ₘ μ` and
  `(M.saKernel π ^ n) ∘ₘ (μ ⊗ₘ π)`.

## References

* [P] M. L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*,
  Wiley, 1994, Chapter 2.
-/

public section

open MeasureTheory ProbabilityTheory Learning

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡}

/-- The deterministic stationary policy `π` is the Markov policy playing the deterministic kernel
of `π` at every round. -/
lemma policyAlg_eq_markov (π : 𝓢 → 𝓐) (hπ : Measurable π) :
    (policyAlg π hπ : Algorithm 𝓢 𝓐 𝓡) = Algorithm.markov fun _ ↦ Kernel.deterministic π hπ := by
  ext n : 2
  ext p : 1
  simp [Kernel.deterministic_apply]

/-! ### The state and state-action kernels of a stationary policy -/

section Kernels

variable (M : MDP 𝓢 𝓐 𝓡) (π : Kernel 𝓢 𝓐)

/-- The transition kernel of the states under the stationary policy `π`: from the state `s`, draw
an action `a` from `π s`, then the next state from `M.P (s, a)`. -/
noncomputable def stateKernel : Kernel 𝓢 𝓢 :=
  M.P ∘ₖ (Kernel.id ×ₖ π)

lemma stateKernel_def : M.stateKernel π = M.P ∘ₖ (Kernel.id ×ₖ π) :=
  (rfl)

instance [IsMarkovKernel π] : IsMarkovKernel (M.stateKernel π) := by
  rw [stateKernel_def]
  infer_instance

/-- The transition kernel of the state-action pairs under the stationary policy `π`: from the
pair `p`, draw the next state `s` from `M.P p`, then the next action from `π s`. -/
noncomputable def saKernel : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐) :=
  (Kernel.id ×ₖ π) ∘ₖ M.P

lemma saKernel_def : M.saKernel π = (Kernel.id ×ₖ π) ∘ₖ M.P :=
  (rfl)

instance [IsMarkovKernel π] : IsMarkovKernel (M.saKernel π) := by
  rw [saKernel_def]
  infer_instance

variable [IsSFiniteKernel π]

/-- Composing a measure `μ` with the state kernel of `π` draws a state from `μ`, an action from
`π`, and a next state from `M.P`. -/
lemma stateKernel_comp_eq_comp_compProd (μ : Measure 𝓢) [SFinite μ] :
    M.stateKernel π ∘ₘ μ = M.P ∘ₘ (μ ⊗ₘ π) := by
  rw [stateKernel_def, ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod]

lemma stateKernel_apply (s : 𝓢) : M.stateKernel π s = M.P ∘ₘ (Measure.dirac s ⊗ₘ π) := by
  rw [← stateKernel_comp_eq_comp_compProd, Measure.dirac_bind (Kernel.measurable _)]

/-- Composing a measure `ν` on state-action pairs with the state-action kernel of `π` draws a
next state from `M.P ∘ₘ ν`, then an action from `π`. -/
lemma saKernel_comp_eq_compProd (ν : Measure (𝓢 × 𝓐)) [SFinite ν] :
    M.saKernel π ∘ₘ ν = (M.P ∘ₘ ν) ⊗ₘ π := by
  rw [saKernel_def, ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod]

variable {M π} in
/-- Integrating against the state kernel of `π` from `s` averages over the actions `a` of `π s`
the integral against `M.P (s, a)`. -/
lemma integral_stateKernel {s : 𝓢} {v : 𝓢 → ℝ} (hv : Integrable v (M.stateKernel π s)) :
    ∫ s', v s' ∂(M.stateKernel π s) = ∫ a, ∫ s', v s' ∂(M.P (s, a)) ∂(π s) := by
  rw [stateKernel_def] at hv ⊢
  have h := hv.integral_comp.aestronglyMeasurable
  rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod] at h
  rw [Kernel.integral_comp hv, Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    integral_map measurable_prodMk_left.aemeasurable h]

@[simp]
lemma saKernel_apply (p : 𝓢 × 𝓐) : M.saKernel π p = M.P p ⊗ₘ π := by
  rw [saKernel_def, Kernel.comp_apply, Measure.compProd_eq_comp_prod]

end Kernels

/-! ### State marginals of a Markov policy -/

section StateMarginal

variable (M : MDP 𝓢 𝓐 𝓡) (π : ℕ → Kernel 𝓢 𝓐) (μ : Measure 𝓢)

/-- The law of the state of round `n` under the Markov policy `π`, from the initial law `μ`:
`μ₀ = μ` and `μₙ₊₁ = M.P ∘ₘ (μₙ ⊗ₘ π n)`. -/
noncomputable def stateMarginal : ℕ → Measure 𝓢
  | 0 => μ
  | n + 1 => M.P ∘ₘ (stateMarginal n ⊗ₘ π n)

@[simp]
lemma stateMarginal_zero : M.stateMarginal π μ 0 = μ :=
  (rfl)

lemma stateMarginal_add_one (n : ℕ) :
    M.stateMarginal π μ (n + 1) = M.P ∘ₘ (M.stateMarginal π μ n ⊗ₘ π n) :=
  (rfl)

instance [SFinite μ] (n : ℕ) : SFinite (M.stateMarginal π μ n) := by
  induction n with
  | zero => rwa [stateMarginal_zero]
  | succ n ih => rw [stateMarginal_add_one]; infer_instance

instance [IsProbabilityMeasure μ] [∀ n, IsMarkovKernel (π n)] (n : ℕ) :
    IsProbabilityMeasure (M.stateMarginal π μ n) := by
  induction n with
  | zero => rwa [stateMarginal_zero]
  | succ n ih => rw [stateMarginal_add_one]; infer_instance

/-- Under a stationary policy `π`, the law of the state of round `n` is
`(M.stateKernel π ^ n) ∘ₘ μ`. -/
lemma stateMarginal_const (π : Kernel 𝓢 𝓐) [IsSFiniteKernel π] [SFinite μ] (n : ℕ) :
    M.stateMarginal (fun _ ↦ π) μ n = (M.stateKernel π ^ n) ∘ₘ μ := by
  induction n with
  | zero => rw [stateMarginal_zero, pow_zero, Kernel.one_eq_id, Measure.id_comp]
  | succ n ih =>
    rw [stateMarginal_add_one, ← stateKernel_comp_eq_comp_compProd, ih, Measure.comp_assoc,
      pow_succ', Kernel.mul_eq_comp]

/-- Under a stationary policy `π`, the law of the state-action pair of round `n` is
`(M.saKernel π ^ n) ∘ₘ (μ ⊗ₘ π)`. -/
lemma stateMarginal_const_compProd (π : Kernel 𝓢 𝓐) [IsSFiniteKernel π] (n : ℕ) :
    M.stateMarginal (fun _ ↦ π) μ n ⊗ₘ π = (M.saKernel π ^ n) ∘ₘ (μ ⊗ₘ π) := by
  induction n with
  | zero => rw [stateMarginal_zero, pow_zero, Kernel.one_eq_id, Measure.id_comp]
  | succ n ih =>
    rw [stateMarginal_add_one, ← saKernel_comp_eq_compProd, ih, Measure.comp_assoc, pow_succ',
      Kernel.mul_eq_comp]

end StateMarginal

/-! ### Laws of the runs of a Markov policy -/

section Runs

variable [Nonempty 𝓢] {M : MDP 𝓢 𝓐 𝓡} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {O : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓡} {μ : Measure 𝓢}
  [IsProbabilityMeasure μ]

section Markov

variable {π : ℕ → Kernel 𝓢 𝓐} [∀ n, IsMarkovKernel (π n)]

/-- In a run of the Markov policy `π` in the environment of an MDP started from the probability
measure `μ`, the state of round `n` has law `M.stateMarginal π μ n`. -/
theorem hasLaw_obs_markov (h : IsAlgEnvSeq O A Y (Algorithm.markov π) (M.env μ) P) (n : ℕ) :
    HasLaw (O n) (M.stateMarginal π μ n) P := by
  induction n with
  | zero => rw [stateMarginal_zero]; exact hasLaw_obs_zero h
  | succ n ih =>
    rw [stateMarginal_add_one, ← (ih.prod_of_hasCondDistrib
      (h.hasCondDistrib_action_markov n)).map_eq]
    exact hasLaw_obs_add_one h n

/-- In a run of the Markov policy `π` in the environment of an MDP started from the probability
measure `μ`, the state-action pair of round `n` has law `M.stateMarginal π μ n ⊗ₘ π n`. -/
theorem hasLaw_obs_action_markov (h : IsAlgEnvSeq O A Y (Algorithm.markov π) (M.env μ) P)
    (n : ℕ) :
    HasLaw (fun ω ↦ (O n ω, A n ω)) (M.stateMarginal π μ n ⊗ₘ π n) P :=
  (hasLaw_obs_markov h n).prod_of_hasCondDistrib (h.hasCondDistrib_action_markov n)

end Markov

variable {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

/-- In a run of the stationary policy `π` in the environment of an MDP started from the
probability measure `μ`, the state of round `n` has law `(M.stateKernel π ^ n) ∘ₘ μ`. -/
theorem hasLaw_obs_markov_const
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) (n : ℕ) :
    HasLaw (O n) ((M.stateKernel π ^ n : Kernel 𝓢 𝓢) ∘ₘ μ) P := by
  rw [← stateMarginal_const]
  exact hasLaw_obs_markov h n

/-- In a run of the stationary policy `π` in the environment of an MDP started from the
probability measure `μ`, the state-action pair of round `n` has law
`(M.saKernel π ^ n) ∘ₘ (μ ⊗ₘ π)`. -/
theorem hasLaw_obs_action_markov_const
    (h : IsAlgEnvSeq O A Y (Algorithm.markov fun _ ↦ π) (M.env μ) P) (n : ℕ) :
    HasLaw (fun ω ↦ (O n ω, A n ω))
      ((M.saKernel π ^ n : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)) ∘ₘ (μ ⊗ₘ π)) P := by
  rw [← stateMarginal_const_compProd]
  exact hasLaw_obs_action_markov h n

end Runs

end Learning.MDP
