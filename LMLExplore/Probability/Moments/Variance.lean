/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Moments.Variance

/-!
# Variances under a kernel, and of bounded random variables

The variance `Var[X; η b]` of a measurable real function `X` under the laws of an s-finite kernel
`η` is a measurable function of the starting point `b`, as the integrals of `X` and of `X ^ 2` are.
This is what makes one-step variances such as `κ (V ^ 2) - (κ V) ^ 2` of a Markov kernel `κ`
themselves integrable against kernels, in variance recursions of Markov chains.

A real random variable with `|X| ≤ B` almost surely has variance at most `B ^ 2`, the symmetric
case of Mathlib's `ProbabilityTheory.variance_le_sq_of_bounded`.

## Main statements

* `Measurable.variance_kernel`: `b ↦ Var[X; η b]` is measurable.
* `ProbabilityTheory.variance_le_sq_of_abs_le`: `|X| ≤ B` almost surely gives `Var[X; μ] ≤ B ^ 2`.
-/

public section

open MeasureTheory ProbabilityTheory

variable {β δ : Type*} {mβ : MeasurableSpace β} {mδ : MeasurableSpace δ}

/-- The variance of a measurable real function under the laws of an s-finite kernel is a
measurable function of the starting point. -/
theorem Measurable.variance_kernel {η : Kernel β δ} [IsSFiniteKernel η] {X : δ → ℝ}
    (hX : Measurable X) :
    Measurable fun b ↦ Var[X; η b] := by
  simp only [variance, evariance]
  have h_mean : Measurable fun b ↦ ∫ z, X z ∂(η b) :=
    hX.stronglyMeasurable.integral_kernel.measurable
  refine ENNReal.measurable_toReal.comp (Measurable.lintegral_kernel_prod_right'
    (f := fun p : β × δ ↦ ‖X p.2 - ∫ z, X z ∂(η p.1)‖ₑ ^ 2) ?_)
  exact ((hX.comp measurable_snd).sub (h_mean.comp measurable_fst)).enorm.pow_const 2

namespace ProbabilityTheory

variable {μ : Measure β} [IsProbabilityMeasure μ] {X : β → ℝ} {B : ℝ}

/-- A real random variable bounded by `B` in absolute value almost surely has variance at most
`B ^ 2`. -/
theorem variance_le_sq_of_abs_le (hX : AEMeasurable X μ) (hXB : ∀ᵐ b ∂μ, |X b| ≤ B) :
    Var[X; μ] ≤ B ^ 2 :=
  (variance_le_sq_of_bounded (a := -B) (b := B) (hXB.mono fun _ ↦ abs_le.1) hX).trans_eq
    (by ring)

end ProbabilityTheory
