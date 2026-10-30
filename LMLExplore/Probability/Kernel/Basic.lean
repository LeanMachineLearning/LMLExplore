/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Kernels from functions on countable spaces

## Main statements

* `ProbabilityTheory.Kernel.ofFunOfCountable_apply`: `Kernel.ofFunOfCountable f a = f a`.
* `ProbabilityTheory.Kernel.isMarkovKernel_ofFunOfCountable`: the kernel `Kernel.ofFunOfCountable f`
  of a family of probability measures `f` is a Markov kernel.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
  [MeasurableSingletonClass α]

/-- The kernel `Kernel.ofFunOfCountable f` maps `a` to `f a`. -/
@[simp]
theorem ofFunOfCountable_apply (f : α → Measure β) (a : α) : ofFunOfCountable f a = f a :=
  rfl

/-- The kernel `Kernel.ofFunOfCountable f` of a family of probability measures `f` is a Markov
kernel. -/
instance isMarkovKernel_ofFunOfCountable (f : α → Measure β) [∀ a, IsProbabilityMeasure (f a)] :
    IsMarkovKernel (ofFunOfCountable f) :=
  ⟨fun a ↦ by rw [ofFunOfCountable_apply]; infer_instance⟩

end ProbabilityTheory.Kernel
