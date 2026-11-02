/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Basic

/-!
# Kernels and families of measures

## Main statements

* `ProbabilityTheory.Kernel.setOf_forall_mem_range_eq_range`: the kernels whose values all lie in
  the range of a family `f` of measures are the range of a parametrization `κ` of the kernels
  `a ↦ f (x a)`.
* `ProbabilityTheory.Kernel.ofFunOfCountable_apply`: `Kernel.ofFunOfCountable f a = f a`.
* `ProbabilityTheory.Kernel.isMarkovKernel_ofFunOfCountable`: the kernel `Kernel.ofFunOfCountable f`
  of a family of probability measures `f` is a Markov kernel.
-/

public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

/-- The kernels whose values all lie in the range of a family `f` of measures are the range of a
parametrization `κ` of the kernels `a ↦ f (x a)`. -/
theorem setOf_forall_mem_range_eq_range {α β X : Type*} {_ : MeasurableSpace α}
    {_ : MeasurableSpace β} {f : X → Measure β} {κ : (α → X) → Kernel α β}
    (hκ : ∀ x a, κ x a = f (x a)) :
    {ν : Kernel α β | ∀ a, ν a ∈ Set.range f} = Set.range κ := by
  ext ν
  refine ⟨fun h ↦ ?_, ?_⟩
  · choose x hx using h
    exact ⟨x, Kernel.ext fun a ↦ (hκ x a).trans (hx a)⟩
  · rintro ⟨x, rfl⟩ a
    exact ⟨x a, (hκ x a).symm⟩

section Countable

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

end Countable

end ProbabilityTheory.Kernel
