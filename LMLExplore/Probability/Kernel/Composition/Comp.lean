/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Invariance
public import TauCeti.Probability.Kernel.Composition.Power

/-!
# The monoid of kernels from a space to itself

Mathlib's monoid structure on `Kernel α α` has unit `Kernel.id` and product the composition
`η * κ = η ∘ₖ κ`, so that `κ ^ n` is the `n`-step transition kernel. This file records the second
fact as a lemma, in the form of Mathlib's `Module.End.mul_eq_comp`, so that statements about
powers of kernels can be rewritten into compositions. The first is Tau Ceti's
`ProbabilityTheory.Kernel.one_def`, imported here together with Tau Ceti's instances
`ProbabilityTheory.IsMarkovKernel.pow`, `ProbabilityTheory.IsSFiniteKernel.pow` and
`ProbabilityTheory.IsFiniteKernel.pow` stating that the powers of a Markov, s-finite or finite
kernel are again Markov, s-finite or finite kernels. That a measure invariant for a kernel is
invariant for all its powers is Tau Ceti's `ProbabilityTheory.Kernel.Invariant.pow`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

/-- The product of the monoid of kernels is the composition of kernels. -/
lemma mul_eq_comp (η κ : Kernel α α) : η * κ = η ∘ₖ κ :=
  (rfl)

end ProbabilityTheory.Kernel
