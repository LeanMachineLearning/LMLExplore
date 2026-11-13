/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

import LMLExplore.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrals against a composition-product

Complements to Mathlib's `Mathlib.Probability.Kernel.Composition.IntegralCompProd`. If `g` is
integrable for the composition-product `μ ⊗ₘ κ`, then `a ↦ ∫ g (a, b) dκ_a(b)` is integrable for
`μ`. For a Markov kernel `κ`, the integral against `μ` of `f a - ∫ g (a, b) dκ_a(b)` is the
integral of `f p.1 - g p` against `μ ⊗ₘ κ`.

## Main statements

* `MeasureTheory.Integrable.integral_measure_compProd`: if `g` is integrable for `μ ⊗ₘ κ`, then
  `a ↦ ∫ g (a, b) dκ_a(b)` is integrable for `μ`.
* `MeasureTheory.Measure.integral_sub_integral_eq_integral_compProd`:
  `∫ (f a - ∫ g (a, b) dκ_a(b)) dμ(a) = ∫ (f p.1 - g p) d(μ ⊗ₘ κ)(p)`.
-/

public section

open ProbabilityTheory

namespace MeasureTheory

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {κ : Kernel α β}

/-- If `g` is integrable for the composition-product `μ ⊗ₘ κ`, then `a ↦ ∫ g (a, b) dκ_a(b)` is
integrable for `μ`. This is the measure form of Mathlib's `Integrable.integral_compProd`. -/
lemma Integrable.integral_measure_compProd [SFinite μ] [IsSFiniteKernel κ] {g : α × β → E}
    (hg : Integrable g (μ ⊗ₘ κ)) : Integrable (fun a ↦ ∫ b, g (a, b) ∂(κ a)) μ := by
  rw [Measure.compProd] at hg
  simpa only [Kernel.prodMkLeft_apply, Kernel.const_apply] using hg.integral_compProd

namespace Measure

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

end Measure

end MeasureTheory
