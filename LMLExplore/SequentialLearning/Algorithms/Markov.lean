/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.Algorithms.Markov

/-!
# Markov algorithms

A *Markov policy* is a sequence `π : ℕ → Kernel 𝓞 𝓐` of Markov kernels. LML's algorithm
`Algorithm.markov π` plays, at round `n`, an action drawn from `π n o`, where `o` is the observation
of round `n`: it forgets the past rounds. In the environment of a Markov decision process, whose
observations are the states, these are the Markov policies of the process, and a constant sequence
is a stationary policy.

## Main statements

* `Learning.Algorithm.policy_markov_apply`: the policy of `Algorithm.markov π` at round `n` is
  `π n` applied to the current observation.
* `Learning.Algorithm.markov_inj`: two Markov policies give the same algorithm if and only if they
  are equal.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

variable (π : ℕ → Kernel 𝓞 𝓐) [∀ n, IsMarkovKernel (π n)]

/-- The policy of `Algorithm.markov π` at round `n` is `π n` applied to the current observation. -/
@[simp]
lemma Algorithm.policy_markov_apply (n : ℕ) (p : Hist 𝓞 𝓐 𝓨 n × 𝓞) :
    (Algorithm.markov π : Algorithm 𝓞 𝓐 𝓨).policy n p = π n p.2 := by
  rw [Algorithm.policy_markov, Kernel.prodMkLeft_apply]

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

end Learning
