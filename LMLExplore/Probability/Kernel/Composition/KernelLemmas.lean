/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Composition-products with kernels that ignore the first draw, and compositions with `id ×ₖ η`

Complements to Mathlib's `Mathlib.Probability.Kernel.Composition.KernelLemmas`, relating different
ways to compose kernels. If the second kernel of a composition-product `κ ⊗ₖ η'` does not depend
on the draw of `κ`, that is `η' = η.prodMkRight β`, the composition-product is the product
`κ ×ₖ η`: the two draws are independent given the input. This is the kernel version of
Mathlib's `MeasureTheory.Measure.compProd_const`.

The composition `κ ∘ₖ (Kernel.id ×ₖ η)` of a kernel `κ` from pairs with `Kernel.id ×ₖ η` draws
`b` from `η a`, then the output from `κ (a, b)`. In a Markov decision process, it is the state
kernel of a policy `η` for the transition kernel `κ`. Integrating against it averages over the
draws of `η a` the integrals against `κ (a, b)`, and for a deterministic `η = deterministic f` it
is `a ↦ κ (a, f a)`.

## Main statements

* `ProbabilityTheory.Kernel.compProd_prodMkRight_eq_prod`: `κ ⊗ₖ η.prodMkRight β = κ ×ₖ η`.
* `ProbabilityTheory.Kernel.integral_comp_id_prod_apply`:
  `∫ v d((κ ∘ₖ (Kernel.id ×ₖ η)) a) = ∫ (∫ v dκ (a, b)) dη a (b)`.
* `ProbabilityTheory.Kernel.comp_id_prod_deterministic_apply`:
  `(κ ∘ₖ (Kernel.id ×ₖ deterministic f hf)) a = κ (a, f a)`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- The composition-product of `κ` with a kernel `η.prodMkRight β` that ignores the draw of `κ` is
the product `κ ×ₖ η`. -/
@[simp]
lemma compProd_prodMkRight_eq_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [IsSFiniteKernel η] :
    κ ⊗ₖ η.prodMkRight β = κ ×ₖ η := by
  ext a s hs
  simp [compProd_apply hs, prod_apply, Measure.prod_apply hs, Set.preimage]

/-- Integrating against `κ ∘ₖ (Kernel.id ×ₖ η)` from `a` averages over the draws `b` of `η a` the
integral against `κ (a, b)`. -/
lemma integral_comp_id_prod_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : Kernel (α × β) γ) (η : Kernel α β) [IsSFiniteKernel η] {a : α} {v : γ → E}
    (hv : Integrable v ((κ ∘ₖ (Kernel.id ×ₖ η)) a)) :
    ∫ c, v c ∂((κ ∘ₖ (Kernel.id ×ₖ η)) a) = ∫ b, ∫ c, v c ∂(κ (a, b)) ∂(η a) := by
  have h := hv.integral_comp.aestronglyMeasurable
  rw [prod_apply, id_apply, Measure.dirac_prod] at h
  rw [integral_comp hv, prod_apply, id_apply, Measure.dirac_prod,
    integral_map measurable_prodMk_left.aemeasurable h]

/-- For a deterministic kernel `deterministic f hf`, the composition
`κ ∘ₖ (Kernel.id ×ₖ deterministic f hf)` from `a` is `κ (a, f a)`. -/
@[simp]
lemma comp_id_prod_deterministic_apply (κ : Kernel (α × β) γ) {f : α → β} (hf : Measurable f)
    (a : α) : (κ ∘ₖ (Kernel.id ×ₖ deterministic f hf)) a = κ (a, f a) := by
  ext t ht
  rw [comp_apply' _ _ _ ht, prod_apply, id_apply, deterministic_apply, Measure.dirac_prod_dirac,
    lintegral_dirac' _ (κ.measurable_coe ht)]

end ProbabilityTheory.Kernel
