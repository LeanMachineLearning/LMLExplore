/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Composition-products with kernels that ignore the first draw

Complements to Mathlib's `Mathlib.Probability.Kernel.Composition.KernelLemmas`, relating different
ways to compose kernels. If the second kernel of a composition-product `κ ⊗ₖ η'` does not depend
on the draw of `κ`, that is `η' = η.prodMkRight β`, the composition-product is the product
`κ ×ₖ η`: the two draws are independent given the input. This is the kernel version of
Mathlib's `MeasureTheory.Measure.compProd_const`.

## Main statements

* `ProbabilityTheory.Kernel.compProd_prodMkRight_eq_prod`: `κ ⊗ₖ η.prodMkRight β = κ ×ₖ η`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- The composition-product of `κ` with a kernel `η.prodMkRight β` that ignores the draw of `κ` is
the product `κ ×ₖ η`. -/
lemma compProd_prodMkRight_eq_prod (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel α γ)
    [IsSFiniteKernel η] :
    κ ⊗ₖ η.prodMkRight β = κ ×ₖ η := by
  ext a s hs
  simp [compProd_apply hs, prod_apply, Measure.prod_apply hs, Set.preimage]

end ProbabilityTheory.Kernel
