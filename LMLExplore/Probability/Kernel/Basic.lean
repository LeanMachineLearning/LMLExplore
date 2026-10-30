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

* `ProbabilityTheory.Kernel.isMarkovKernel_ofFunOfCountable`: the kernel `Kernel.ofFunOfCountable f`
  of a family of probability measures `f` is a Markov kernel.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
  [MeasurableSingletonClass α]

instance isMarkovKernel_ofFunOfCountable (f : α → Measure β) [∀ a, IsProbabilityMeasure (f a)] :
    IsMarkovKernel (ofFunOfCountable f) :=
  ⟨fun a ↦ (inferInstance : IsProbabilityMeasure (f a))⟩

end ProbabilityTheory.Kernel
