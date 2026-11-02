/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithm

/-!
# Markov algorithms

A *Markov policy* is a sequence `π : ℕ → Kernel 𝓞 𝓐` of Markov kernels. The algorithm
`Algorithm.markov π` plays, at round `n`, an action drawn from `π n o`, where `o` is the observation
of round `n`: it forgets the past rounds. In the environment of a Markov decision process, whose
observations are the states, these are the Markov policies of the process, and a constant sequence
is a stationary policy.

## Main definitions

* `Learning.Algorithm.markov π : Algorithm 𝓞 𝓐 𝓨`: the algorithm playing the Markov policy `π`.

## Main statements

* `Learning.IsAlgEnvSeq.hasCondDistrib_action_markov`: in an algorithm-environment sequence of
  `Algorithm.markov π`, the action of round `n` has conditional law `π n` given the observation of
  round `n`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- The algorithm playing the Markov policy `π`: at round `n`, it draws its action from `π n o`,
where `o` is the observation of round `n`, whatever the past rounds. -/
noncomputable def Algorithm.markov (π : ℕ → Kernel 𝓞 𝓐) [∀ n, IsMarkovKernel (π n)] :
    Algorithm 𝓞 𝓐 𝓨 where
  policy n := (π n).comap Prod.snd measurable_snd

variable (π : ℕ → Kernel 𝓞 𝓐) [∀ n, IsMarkovKernel (π n)]

/-- The policy of `Algorithm.markov π` at round `n` is `π n` applied to the current observation. -/
lemma Algorithm.policy_markov (n : ℕ) :
    (Algorithm.markov π : Algorithm 𝓞 𝓐 𝓨).policy n = (π n).comap Prod.snd measurable_snd :=
  (rfl)

@[simp]
lemma Algorithm.policy_markov_apply (n : ℕ) (p : Hist 𝓞 𝓐 𝓨 n × 𝓞) :
    (Algorithm.markov π : Algorithm 𝓞 𝓐 𝓨).policy n p = π n p.2 := by
  rw [Algorithm.policy_markov, Kernel.comap_apply]

/-- Two Markov policies give the same algorithm if and only if they are equal. -/
lemma Algorithm.markov_inj [Nonempty 𝓨] {π' : ℕ → Kernel 𝓞 𝓐} [∀ n, IsMarkovKernel (π' n)] :
    (Algorithm.markov π : Algorithm 𝓞 𝓐 𝓨) = Algorithm.markov π' ↔ π = π' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  funext n
  ext o : 1
  have : Nonempty 𝓐 := nonempty_of_isProbabilityMeasure (π n o)
  -- the policies of round `n` agree at the observation `o` and any history of `n` rounds
  have h_hist : Hist 𝓞 𝓐 𝓨 n := fun _ ↦ (o, Classical.arbitrary 𝓐, Classical.arbitrary 𝓨)
  simpa using congr(($h).policy n (h_hist, o))

/-- In an algorithm-environment sequence of the algorithm playing the Markov policy `π`, the
action of round `n` has conditional law `π n` given the observation of round `n`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_markov {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {O : ℕ → Ω → 𝓞} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
    {env : Environment 𝓞 𝓐 𝓨} (h : IsAlgEnvSeq O A Y (Algorithm.markov π) env P) (n : ℕ) :
    HasCondDistrib (A n) (O n) (π n) P :=
  (h.hasCondDistrib_action n).comp_right (hf := measurable_snd)

end Learning
