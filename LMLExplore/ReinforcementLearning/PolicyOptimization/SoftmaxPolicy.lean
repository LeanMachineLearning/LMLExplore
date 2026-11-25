/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.ExponentialWeights
public import LMLExplore.ReinforcementLearning.PolicyOptimization.DirectPolicy

/-!
# Softmax policies

On a countable state space `𝓢` with measurable singletons and a finite action set `𝓐`, a real
parameter `θ : 𝓢 → 𝓐 → ℝ` defines the stationary **softmax policy**
`π_θ (a | s) = exp (θ s a) / ∑ b, exp (θ s b)`, the direct policy
(`LMLExplore.ReinforcementLearning.directPolicy`) of the probability vectors `softmax (θ s)`.
Softmax policies are the policies of policy gradient methods with the softmax parametrization and
of natural policy gradient [AKLM21, §§5.1, 5.3]. The
multiplicative update `π_θ (a | s) ↦ π_θ (a | s) * exp (u s a)`, normalized, is the softmax policy
of `θ + u` (`LMLExplore.OnlineLearning.softmax_add_apply`).

## Main definitions

* `LMLExplore.ReinforcementLearning.softmaxPolicy θ`: the softmax policy of the parameter `θ`, a
  Markov kernel from `𝓢` to `𝓐`.

## Main statements

* `LMLExplore.ReinforcementLearning.integral_softmaxPolicy`: integrals against `π_θ s` are the
  sums `∑ a, softmax (θ s) a • f a`.
* `LMLExplore.ReinforcementLearning.measureReal_softmaxPolicy_singleton`: the probability of the
  action `a` at the state `s` is `softmax (θ s) a`.

## References

* [A. Agarwal, S. M. Kakade, J. D. Lee and G. Mahajan, *On the theory of policy gradient methods:
  optimality, approximation, and distribution shift*, JMLR 22 (2021), arXiv:1908.00261][AKLM21],
  §§5.1, 5.3
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore.OnlineLearning

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 : Type*} [MeasurableSpace 𝓢] [MeasurableSpace 𝓐] [Countable 𝓢]
  [MeasurableSingletonClass 𝓢] [Fintype 𝓐]

/-- The **softmax policy** of the parameter `θ : 𝓢 → 𝓐 → ℝ`: the stationary policy that draws its
action at the state `s` from the probability vector `softmax (θ s)`, that is
`π_θ (a | s) = exp (θ s a) / ∑ b, exp (θ s b)`: the direct policy of the weights
`fun s ↦ softmax (θ s)`. -/
noncomputable def softmaxPolicy (θ : 𝓢 → 𝓐 → ℝ) : Kernel 𝓢 𝓐 :=
  directPolicy fun s ↦ softmax (θ s)

/-- The softmax policy draws its action at the state `s` from the weights `softmax (θ s)`. -/
lemma softmaxPolicy_apply (θ : 𝓢 → 𝓐 → ℝ) (s : 𝓢) :
    softmaxPolicy θ s = weightedMeasure (softmax (θ s)) :=
  directPolicy_apply _ s

instance isMarkovKernel_softmaxPolicy [Nonempty 𝓐] (θ : 𝓢 → 𝓐 → ℝ) :
    IsMarkovKernel (softmaxPolicy θ) :=
  isMarkovKernel_directPolicy fun s ↦ softmax_mem_simplex (θ s)

variable [MeasurableSingletonClass 𝓐]

/-- The integral of a function of the actions against the softmax policy at the state `s` is the
average `∑ a, softmax (θ s) a • f a`. -/
lemma integral_softmaxPolicy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (θ : 𝓢 → 𝓐 → ℝ) (s : 𝓢) (f : 𝓐 → E) :
    ∫ a, f a ∂(softmaxPolicy θ s) = ∑ a, softmax (θ s) a • f a :=
  integral_directPolicy (p := fun s ↦ softmax (θ s)) (softmax_nonneg (θ s)) f

/-- The probability that the softmax policy plays the action `a` at the state `s` is
`softmax (θ s) a`. -/
@[simp]
lemma measureReal_softmaxPolicy_singleton (θ : 𝓢 → 𝓐 → ℝ) (s : 𝓢) (a : 𝓐) :
    (softmaxPolicy θ s).real {a} = softmax (θ s) a :=
  measureReal_directPolicy_singleton (p := fun s ↦ softmax (θ s)) (softmax_nonneg (θ s)) a

end LMLExplore.ReinforcementLearning
