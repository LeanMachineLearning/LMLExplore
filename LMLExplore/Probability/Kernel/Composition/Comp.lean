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
that statements about powers of kernels can be rewritten into compositions. It also provides the
instances stating that the powers of a Markov kernel are Markov kernels, and the powers of an
s-finite kernel are s-finite kernels.
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

/-- The `n`-step transition kernel of a Markov kernel is a Markov kernel. -/
instance (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) : IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero, one_eq_id]; infer_instance
  | succ n ih => rw [pow_succ, mul_eq_comp]; infer_instance

/-- The `n`-step transition kernel of an s-finite kernel is an s-finite kernel. -/
instance (κ : Kernel α α) [IsSFiniteKernel κ] (n : ℕ) : IsSFiniteKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero, one_eq_id]; infer_instance
  | succ n ih => rw [pow_succ, mul_eq_comp]; infer_instance

end ProbabilityTheory.Kernel
