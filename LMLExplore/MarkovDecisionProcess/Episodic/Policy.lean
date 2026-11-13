/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Value

/-!
# Deterministic `H`-step policies of an episodic MDP

A deterministic `H`-step policy `π : Policy 𝓢 𝓐 H = Fin H → 𝓢 → 𝓐` plays the action `π h s` at
the step `h < H` in the state `s`. As for stochastic processes, it is not bundled with its
measurability: the statements that need it take the hypothesis `hπ : ∀ h, Measurable (π h)`,
which holds for every policy when the state space is countable and discrete.

When the action space is nonempty, `Policy.extend π : ℕ → 𝓢 → 𝓐` extends `π` to all steps by a
fixed action beyond the horizon, and `Policy.toKernel π hπ : ℕ → Kernel 𝓢 𝓐` is the
corresponding deterministic Markov policy, to which the values of
`LMLExplore/MarkovDecisionProcess/Episodic/Value.lean` apply. The steps `h ≥ H` never matter for
an episode of horizon `H`.

The definitions `Policy` and `Policy.extend` are adapted, with their names and namespace, from
the formalization entropy-mdp (`github.com/RemyDegenne/entropy-mdp`, file
`Essakine2026Tight/ForLMLExplore/MarkovDecisionProcess/Episodic/Basic.lean`, by Rémy Degenne,
Apache 2.0) of [EV26].

## Main definitions

* `Learning.MDP.Episodic.Policy 𝓢 𝓐 H`: the deterministic `H`-step policies.
* `Learning.MDP.Episodic.Policy.extend π`: the policy `π` extended beyond the horizon.
* `Learning.MDP.Episodic.Policy.toKernel π hπ`: the deterministic Markov policy of `π`.

## Main statements

* `Learning.MDP.Episodic.Policy.extend_injective`: extension beyond the horizon is injective.
* `Learning.MDP.Episodic.Policy.measurable_extend`: the extension of a measurable policy is
  measurable at every step.
* `Learning.MDP.Episodic.EpisodicMDP.value_toKernel_fin`: before the horizon, the value of
  `π` is its action value at the action it plays.

## References

* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning.MDP.Episodic

variable {𝓢 𝓐 : Type*} {H : ℕ}

/-- A deterministic `H`-step policy: the action `π h s` played at the step `h : Fin H` in the
state `s`. -/
abbrev Policy (𝓢 𝓐 : Type*) (H : ℕ) := Fin H → 𝓢 → 𝓐

namespace Policy

variable [Nonempty 𝓐]

/-- The `H`-step policy `π` extended to all steps by a fixed action beyond the horizon. -/
noncomputable def extend (π : Policy 𝓢 𝓐 H) (h : ℕ) (s : 𝓢) : 𝓐 :=
  if hh : h < H then π ⟨h, hh⟩ s else Classical.arbitrary 𝓐

@[simp]
lemma extend_of_lt (π : Policy 𝓢 𝓐 H) {h : ℕ} (hh : h < H) (s : 𝓢) :
    π.extend h s = π ⟨h, hh⟩ s := by
  simp [extend, hh]

lemma extend_fin (π : Policy 𝓢 𝓐 H) (h : Fin H) (s : 𝓢) : π.extend h s = π h s :=
  π.extend_of_lt h.2 s

lemma extend_of_le (π : Policy 𝓢 𝓐 H) {h : ℕ} (hh : H ≤ h) (s : 𝓢) :
    π.extend h s = Classical.arbitrary 𝓐 := by
  simp [extend, not_lt.2 hh]

lemma extend_injective : Function.Injective (extend : Policy 𝓢 𝓐 H → ℕ → 𝓢 → 𝓐) := by
  intro π π' h
  funext k s
  rw [← π.extend_fin k s, ← π'.extend_fin k s, h]

variable [MeasurableSpace 𝓢] [MeasurableSpace 𝓐]

/-- The extension of a policy that is measurable at every step is measurable at every step. -/
lemma measurable_extend {π : Policy 𝓢 𝓐 H} (hπ : ∀ h, Measurable (π h)) (h : ℕ) :
    Measurable (π.extend h) := by
  by_cases hh : h < H
  · rw [show π.extend h = π ⟨h, hh⟩ from funext (π.extend_of_lt hh)]
    exact hπ ⟨h, hh⟩
  · rw [show π.extend h = fun _ ↦ Classical.arbitrary 𝓐 from funext (π.extend_of_le (not_lt.1 hh))]
    exact measurable_const

/-- The deterministic Markov policy of the `H`-step policy `π`, measurable at every step: at the
step `h`, the Dirac mass at the action `π.extend h s`. -/
noncomputable def toKernel (π : Policy 𝓢 𝓐 H) (hπ : ∀ h, Measurable (π h)) (h : ℕ) :
    Kernel 𝓢 𝓐 :=
  Kernel.deterministic (π.extend h) (measurable_extend hπ h)

@[simp]
lemma toKernel_apply (π : Policy 𝓢 𝓐 H) (hπ : ∀ h, Measurable (π h)) (h : ℕ) (s : 𝓢) :
    π.toKernel hπ h s = Measure.dirac (π.extend h s) :=
  Kernel.deterministic_apply _ _

instance (π : Policy 𝓢 𝓐 H) (hπ : ∀ h, Measurable (π h)) (h : ℕ) :
    IsMarkovKernel (π.toKernel hπ h) := by
  unfold toKernel; infer_instance

end Policy

namespace EpisodicMDP

variable [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] [Nonempty 𝓐] (M : EpisodicMDP 𝓢 𝓐)

/-- Before the horizon, the value of the `H`-step policy `π` is its action value at the action
`π h s` it plays. -/
theorem value_toKernel_fin {π : Policy 𝓢 𝓐 H} (hπ : ∀ h, Measurable (π h)) (h : Fin H)
    (s : 𝓢) :
    M.value H (π.toKernel hπ) h s = M.qValue H (π.toKernel hπ) h s (π h s) := by
  have := M.value_deterministic_of_lt (H := H) (Policy.measurable_extend hπ) h.2 s
  rwa [Policy.extend_fin] at this

end EpisodicMDP

end Learning.MDP.Episodic
