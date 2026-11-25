/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.WeightAlgorithm

/-!
# Directly parametrized policies

On a countable state space `𝓢` with finitely many actions, a stationary policy is given by a
probability vector in every state, `p : 𝓢 → 𝓐 → ℝ` with `p s ∈ simplex 𝓐`. This is the **direct
parametrization** of policies [AKLM21, §4], in which policy optimization methods such as projected
gradient ascent and policy mirror descent [Xiao22] update the probabilities themselves. This file
turns such a family into a kernel, the form in which values, action values and occupancy measures
of stationary policies are defined.

## Main definitions

* `LMLExplore.ReinforcementLearning.directPolicy p`: the stationary policy drawing its action at the
  state `s` from the weights `p s`.

## Main statements

* `LMLExplore.ReinforcementLearning.isMarkovKernel_directPolicy`: for probability vectors, the
  direct policy is a Markov kernel.
* `LMLExplore.ReinforcementLearning.integral_directPolicy`: integrals against the direct policy
  are the weighted sums `∑ a, p s a • f a`.
* `LMLExplore.ReinforcementLearning.measureReal_directPolicy_singleton`: the probability of the
  action `a` at the state `s` is `p s a`.

## References

* [A. Agarwal, S. M. Kakade, J. D. Lee and G. Mahajan, *On the theory of policy gradient methods:
  optimality, approximation, and distribution shift*, JMLR 22 (2021), arXiv:1908.00261][AKLM21],
  §4
* [L. Xiao, *On the convergence rates of policy gradient methods*, JMLR 23 (2022),
  arXiv:2201.07443][Xiao22]
-/

public section

open MeasureTheory ProbabilityTheory

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 : Type*} [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] [Countable 𝓢]
  [MeasurableSingletonClass 𝓢] [Fintype 𝓐]

/-- The **directly parametrized policy** of the weights `p : 𝓢 → 𝓐 → ℝ`: the stationary policy
that draws its action at the state `s` from the weights `p s`, that is, for nonnegative
weights, `π_p (a | s) = p s a` [AKLM21, §4]. Every map on the countable state space `𝓢` is
measurable, so no measurability hypothesis on `p` is needed. -/
noncomputable def directPolicy (p : 𝓢 → 𝓐 → ℝ) : Kernel 𝓢 𝓐 :=
  Bandits.weightKernel p fun _ ↦ measurable_of_countable _

/-- The direct policy draws its action at the state `s` from the weights `p s`. -/
@[simp]
lemma directPolicy_apply (p : 𝓢 → 𝓐 → ℝ) (s : 𝓢) :
    directPolicy p s = weightedMeasure (p s) :=
  Bandits.weightKernel_apply _ _ s

/-- The direct policy of probability vectors is a Markov kernel. -/
lemma isMarkovKernel_directPolicy {p : 𝓢 → 𝓐 → ℝ} (hp : ∀ s, p s ∈ simplex 𝓐) :
    IsMarkovKernel (directPolicy p) :=
  Bandits.isMarkovKernel_weightKernel _ hp

variable [MeasurableSingletonClass 𝓐]

/-- For nonnegative weights at the state `s`, the integral of a function of the actions against
the direct policy at `s` is the weighted sum `∑ a, p s a • f a`. -/
lemma integral_directPolicy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {p : 𝓢 → 𝓐 → ℝ} {s : 𝓢} (hp : ∀ a, 0 ≤ p s a) (f : 𝓐 → E) :
    ∫ a, f a ∂(directPolicy p s) = ∑ a, p s a • f a := by
  rw [directPolicy_apply, integral_weightedMeasure_eq_sum hp]

/-- For nonnegative weights at the state `s`, the probability that the direct policy plays the
action `a` at `s` is `p s a`. -/
lemma measureReal_directPolicy_singleton {p : 𝓢 → 𝓐 → ℝ} {s : 𝓢} (hp : ∀ a, 0 ≤ p s a)
    (a : 𝓐) : (directPolicy p s).real {a} = p s a := by
  rw [directPolicy_apply, measureReal_weightedMeasure_singleton hp]

end LMLExplore.ReinforcementLearning
