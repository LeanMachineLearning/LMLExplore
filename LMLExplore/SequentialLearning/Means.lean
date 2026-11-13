/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.SequentialLearning.Means

/-!
# The feedback kernel and the means of an environment along a run

Equations for LML's `Learning.Environment.feedbackKernel` and `Learning.Environment.means`: at the
run's history and observation of round `n`, they are the feedback kernel `env.feedback n` of the
environment and its mean.

## Main statements

* `Learning.Environment.feedbackKernel_apply`: the law of the feedback of an action `k` at round `n`
  is `env.feedback n ((history O A Y n ω, O n ω), k)`.
* `Learning.Environment.means_eq_integral`: the mean of the feedback of `k` at round `n` is the
  integral `∫ y, y ∂env.feedback n ((history O A Y n ω, O n ω), k)`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Learning.Environment

variable {Ω 𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨}

/-- The law of the feedback of an action `k` at round `n`, given the history and the observation
of the run at `ω`, is the feedback kernel `env.feedback n` at the history, the observation and
`k`. -/
@[simp]
lemma feedbackKernel_apply (env : Environment 𝓞 𝓐 𝓨) (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐)
    (Y : ℕ → Ω → 𝓨) (n : ℕ) (ω : Ω) (k : 𝓐) :
    env.feedbackKernel O A Y n ω k = env.feedback n ((history O A Y n ω, O n ω), k) := by
  rw [feedbackKernel, Kernel.sectR_apply]

/-- The mean of the feedback of an action `k` at round `n`, given the history and the observation
of the run at `ω`, is the integral of the feedback kernel `env.feedback n` at the history, the
observation and `k`. -/
lemma means_eq_integral [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨] (env : Environment 𝓞 𝓐 𝓨)
    (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (k : 𝓐) (n : ℕ) (ω : Ω) :
    env.means O A Y k n ω = ∫ y, y ∂env.feedback n ((history O A Y n ω, O n ω), k) := by
  simp only [means, feedbackKernel_apply, id_eq]

end Learning.Environment
