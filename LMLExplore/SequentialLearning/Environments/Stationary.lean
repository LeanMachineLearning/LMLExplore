/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv

/-!
# Stationary environments without observations

LML's stochastic bandit `Environment.bandit ν` is the stationary environment
`Environment.stationary (Measure.dirac ()) (ν.prodMkLeft Unit)`, whose observations are the point
of `Unit`. Conversely, every stationary environment whose observations are the point of `Unit`
is a stochastic bandit: its feedback kernel `ν : Kernel (Unit × 𝓐) 𝓨` only depends on the action.
This lets the results LML states for `Environment.bandit`, such as the divergence decomposition
`Learning.IsAlgEnvSeq.klDiv_map_history_bandit`, apply to environments defined as stationary
environments, for instance linear bandits with a fixed action set.

## Main statements

* `Learning.Environment.stationary_dirac_unit_eq_bandit`: the stationary environment with
  observations in `Unit` and feedback kernel `ν` is the bandit with the kernel `a ↦ ν ((), a)`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-- A stationary environment whose observations are the point of `Unit` is a stochastic bandit:
the bandit with the reward kernel `a ↦ ν ((), a)`. -/
lemma Environment.stationary_dirac_unit_eq_bandit (ν : Kernel (Unit × 𝓐) 𝓨) [IsMarkovKernel ν] :
    Environment.stationary (Measure.dirac ()) ν =
      Environment.bandit (ν.comap (fun a ↦ ((), a)) measurable_prodMk_left) := by
  -- The two feedback kernels agree at every `p : Unit × 𝓐`, since `p = ((), p.2)`.
  have hν : (ν.comap (fun a ↦ ((), a)) measurable_prodMk_left).prodMkLeft Unit = ν := by
    ext ⟨⟨⟩, a⟩ : 1
    rw [Kernel.prodMkLeft_apply, Kernel.comap_apply]
  -- `simp only` rather than `rw`: the `IsMarkovKernel` instance of `stationary` depends on the
  -- kernel being rewritten.
  simp only [Environment.bandit_def, hν]

end Learning
