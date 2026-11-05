/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.CondVar

/-!
# Conditional expectation and variance of a constant minus a random variable

The conditional expectation of `c - X` is `c` minus that of `X`, and the conditional variance is
invariant under `X ↦ c - X`, the conditional analogue of Mathlib's
`ProbabilityTheory.variance_const_sub`. The loss-based importance-weighted estimator of bandit
algorithms is `1` minus an importance-weighted estimator, so the two have the same conditional
variance.

## Main statements

* `MeasureTheory.condExp_const_sub`: `μ[c - X | m] = c - μ[X | m]` almost everywhere, for `X`
  integrable and `μ` finite.
* `ProbabilityTheory.condVar_const_sub`: `Var[c - X; μ | m] = Var[X; μ | m]` almost everywhere,
  for `X` integrable and `μ` finite.
-/

public section

open MeasureTheory

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

namespace MeasureTheory

/-- The conditional expectation of `c - X` is `c` minus that of `X`, for `X` integrable and `μ`
finite. -/
lemma condExp_const_sub [IsFiniteMeasure μ] (hm : m ≤ m₀) (hX : Integrable X μ) (c : ℝ) :
    μ[fun ω ↦ c - X ω | m] =ᵐ[μ] fun ω ↦ c - μ[X | m] ω := by
  filter_upwards [condExp_sub (integrable_const c) hX m] with ω hω
  simpa only [Pi.sub_def, condExp_const hm] using hω

end MeasureTheory

namespace ProbabilityTheory

/-- The conditional variance of `c - X` is that of `X`, for `X` integrable and `μ` finite. -/
lemma condVar_const_sub [IsFiniteMeasure μ] (hm : m ≤ m₀) (hX : Integrable X μ) (c : ℝ) :
    Var[fun ω ↦ c - X ω; μ | m] =ᵐ[μ] Var[X; μ | m] := by
  rw [condVar, condVar]
  refine condExp_congr_ae ?_
  filter_upwards [condExp_const_sub hm hX c] with ω hω
  simp only [Pi.pow_apply, Pi.sub_apply, hω]
  ring

end ProbabilityTheory
