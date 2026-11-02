/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# The monoid of kernels from a space to itself

Mathlib's monoid structure on `Kernel α α` has unit `Kernel.id` and product the composition
`η * κ = η ∘ₖ κ`, so that `κ ^ n` is the `n`-step transition kernel. This file records these two
facts as lemmas, in the form of Mathlib's `Module.End.one_eq_id` and `Module.End.mul_eq_comp`, so
that statements about powers of kernels can be rewritten into compositions.
-/

public section

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

/-- The unit of the monoid of kernels is the identity kernel. -/
lemma one_eq_id : (1 : Kernel α α) = Kernel.id :=
  (rfl)

/-- The product of the monoid of kernels is the composition of kernels. -/
lemma mul_eq_comp (η κ : Kernel α α) : η * κ = η ∘ₖ κ :=
  (rfl)

end ProbabilityTheory.Kernel
