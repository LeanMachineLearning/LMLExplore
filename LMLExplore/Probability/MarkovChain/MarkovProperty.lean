/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Probability.Kernel.Operator
public import Mathlib.Probability.HasCondDistrib
public import TauCeti.Probability.MarkovChain.MarkovProperty

/-!
# Means and conditional laws of the states of a Markov chain

Let `X` be the coordinate process on path space `ℕ → α` under the law `markovChainLaw ν κ` of the
homogeneous Markov chain with initial law `ν` and transition kernel `κ`, with its natural filtration
`MeasureTheory.Filtration.piLE`. This file expresses the mean of a bounded measurable function of
`X n`, for the chain started at a point, through the action `κ.integralCLM` of `κ` on bounded
measurable functions, and states the law of the next state given the past as a conditional
distribution. The Markov property in conditional-expectation form,
`E[f (X (n + 1)) | X 0, …, X n] = ∫ f dκ (X n)` for bounded measurable `f`, is Tau Ceti's
`TauCeti.Probability.isMarkovChain_markovChainLaw` (field `IsMarkovChain.condExp_eq`, and
`IsMarkovChain.condExp_add` for `k` steps).

## Main statements

* `ProbabilityTheory.Kernel.integral_eval_markovChainKernel`: started from `x`, the mean of
  `g (X n)` is `κ ^ n g x`.
* `MeasureTheory.Measure.hasCondDistrib_eval_succ_markovChainLaw`: given `X 0, …, X n`, the next
  state `X (n + 1)` has conditional law `κ (X n)`.
-/

public section

open MeasureTheory LMLExplore TauCeti.Probability
open scoped ENNReal lp

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]

/-- Started from `x`, the chain is at time `n` distributed as `(κ ^ n) x`
(`ProbabilityTheory.Kernel.markovChainKernel_map_eval`), so that the mean of `g` at time `n` is
the action of `κ ^ n` on `g` at `x`. -/
theorem integral_eval_markovChainKernel (g : boundedMeasurable α) (n : ℕ) (x : α) :
    ∫ y, (g : ℓ^∞(α, ℝ)) (y n) ∂κ.markovChainKernel x =
      ((κ ^ n).integralCLM g : ℓ^∞(α, ℝ)) x := by
  rw [integralCLM_apply, ← markovChainKernel_map_eval, Kernel.map_apply _ (measurable_pi_apply n),
    integral_map (measurable_pi_apply n).aemeasurable
      (boundedMeasurable.measurable g).aestronglyMeasurable]

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

open ProbabilityTheory Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α α} [IsMarkovKernel κ]
  {ν : Measure α} [IsProbabilityMeasure ν]

/-- The next state of the chain has conditional law `κ` from the last state, given the prefix of
the path: the conditional-distribution form of
`TauCeti.Probability.markovChainLaw_map_prefix_succ_eq_compProd`. -/
theorem hasCondDistrib_eval_succ_markovChainLaw (n : ℕ) :
    HasCondDistrib (fun ω : ℕ → α ↦ ω (n + 1)) (fun ω (i : Fin (n + 1)) ↦ ω i)
      (κ.comap (fun w : Fin (n + 1) → α ↦ w (Fin.last n)) (measurable_pi_apply _))
      (markovChainLaw ν κ) where
  aemeasurable := by fun_prop
  map_eq := markovChainLaw_map_prefix_succ_eq_compProd ν κ n

end MeasureTheory.Measure
