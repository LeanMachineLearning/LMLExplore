/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

import LMLExplore.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals of differences against a composition-product

Complements to Mathlib's `Mathlib.Probability.Kernel.Composition.IntegralCompProd`. For a Markov
kernel `κ`, the integral against `μ` of `f a - ∫ g (a, b) dκ_a(b)` is the integral of
`f p.1 - g p` against the composition-product `μ ⊗ₘ κ`.

## Main statements

* `MeasureTheory.Measure.integral_sub_integral_eq_integral_compProd`:
  `∫ (f a - ∫ g (a, b) dκ_a(b)) dμ(a) = ∫ (f p.1 - g p) d(μ ⊗ₘ κ)(p)`.
-/

public section

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {κ : Kernel α β}

/-- For a Markov kernel `κ`, the integral against `μ` of `f a - ∫ g (a, b) dκ_a(b)` is the
integral of `f p.1 - g p` against the composition-product `μ ⊗ₘ κ`. -/
lemma integral_sub_integral_eq_integral_compProd [CompleteSpace E] [SFinite μ] [IsMarkovKernel κ]
    {f : α → E} {g : α × β → E} (hf : Integrable f μ) (hg : Integrable g (μ ⊗ₘ κ)) :
    ∫ a, (f a - ∫ b, g (a, b) ∂(κ a)) ∂μ = ∫ p, (f p.1 - g p) ∂(μ ⊗ₘ κ) := by
  have hf' : Integrable (fun p ↦ f p.1) (μ ⊗ₘ κ) := by
    rw [← fst_compProd μ κ] at hf
    exact hf.comp_measurable measurable_fst
  rw [integral_compProd (f := fun p ↦ f p.1 - g p) (hf'.sub hg)]
  refine integral_congr_ae ?_
  filter_upwards [((integrable_compProd_iff hg.1).1 hg).1] with a ha
  rw [integral_const_sub _ ha]

end MeasureTheory.Measure
