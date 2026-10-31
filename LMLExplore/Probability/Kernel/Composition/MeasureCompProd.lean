/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Restriction and pointwise congruence of composition-products

Restricting the first marginal of `μ ⊗ₘ κ` to a measurable set `s` is the same as restricting the
composition-product to the cylinder `s ×ˢ univ`. This is the measure version of Mathlib's
`ProbabilityTheory.Kernel.compProd_restrict_left`.

The value of a composition-product of kernels `κ ⊗ₖ η` at a point `a` is the composition-product
of measures `κ a ⊗ₘ η.sectR a`, so it depends only on `κ a` and on the measures `η (a, b)`.

## Main statements

* `MeasureTheory.Measure.compProd_restrict_left`:
  `μ.restrict s ⊗ₘ κ = (μ ⊗ₘ κ).restrict (s ×ˢ univ)`.
* `ProbabilityTheory.Kernel.compProd_apply_congr`: if `κ a = κ' a` and `η (a, b) = η' (a, b)`
  for all `b`, then `(κ ⊗ₖ η) a = (κ' ⊗ₖ η') a`.
-/

public section

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {κ : Kernel α β} {s : Set α}

/-- Restricting the first marginal of a composition-product to `s` is restricting the
composition-product to `s ×ˢ univ`. -/
lemma compProd_restrict_left [SFinite μ] [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    μ.restrict s ⊗ₘ κ = (μ ⊗ₘ κ).restrict (s ×ˢ univ) := by
  ext t ht
  rw [restrict_apply ht, compProd_apply ht, compProd_apply (ht.inter (hs.prod .univ)),
    ← lintegral_indicator hs]
  refine lintegral_congr fun a ↦ ?_
  by_cases ha : a ∈ s <;> simp [ha, Set.preimage, Set.indicator]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {κ κ' : Kernel α β} {η η' : Kernel (α × β) γ} {a : α}

/-- Two composition-products of kernels agree at a point `a` if the first kernels agree at `a`
and the second kernels agree at every `(a, b)`. -/
lemma compProd_apply_congr [IsSFiniteKernel κ] [IsSFiniteKernel κ'] [IsSFiniteKernel η]
    [IsSFiniteKernel η'] (hκ : κ a = κ' a) (hη : ∀ b, η (a, b) = η' (a, b)) :
    (κ ⊗ₖ η) a = (κ' ⊗ₖ η') a := by
  rw [compProd_apply_eq_compProd_sectR, compProd_apply_eq_compProd_sectR, hκ]
  congr 1
  ext b : 1
  exact hη b

end ProbabilityTheory.Kernel
