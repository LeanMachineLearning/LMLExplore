/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Independence.Integration

/-!
# Expectation of a finite product of independent random variables

Mathlib's `ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun` computes the
expectation of `∏ i ∈ s, X i` for an independent family `X`, assuming every `X i` measurable.
This file proves the same identity assuming measurability only of the factors `X i` with
`i ∈ s`.

## Main statements

* `ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun'`: for an independent family
  `X` whose factors in `s` are measurable, `∫⁻ ∏ i ∈ s, X i = ∏ i ∈ s, ∫⁻ X i`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The expectation of a finite product of independent `ℝ≥0∞`-valued random variables is the
product of their expectations. Unlike `lintegral_prod_eq_prod_lintegral_of_indepFun`, only the
factors indexed by `s` need to be measurable. -/
theorem lintegral_prod_eq_prod_lintegral_of_indepFun' (s : Finset ι) {X : ι → Ω → ℝ≥0∞}
    (hX : iIndepFun X μ) (x_mea : ∀ i ∈ s, Measurable (X i)) :
    ∫⁻ ω, ∏ i ∈ s, X i ω ∂μ = ∏ i ∈ s, ∫⁻ ω, X i ω ∂μ := by
  simp_rw [← Finset.prod_coe_sort s]
  exact lintegral_prod_eq_prod_lintegral_of_indepFun _ (fun i : s ↦ X i)
    (hX.precomp Subtype.val_injective) fun i ↦ x_mea i i.2

end ProbabilityTheory
