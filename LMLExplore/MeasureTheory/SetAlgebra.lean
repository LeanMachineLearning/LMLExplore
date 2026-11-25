/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.SetAlgebra

/-!
# Directed unions of algebras of sets

The union of a nonempty directed family of algebras of sets is an algebra of sets, as
`isPiSystem_iUnion_of_directed_le` is for π-systems. It applies to the measurable sets of the
σ-algebras of a filtration, whose union is an algebra of sets generating the limit σ-algebra.

## Main statements

* `MeasureTheory.isSetAlgebra_iUnion_of_directed_le`: the union of a directed family of algebras
  of sets is an algebra of sets.
-/

public section

open Set

namespace MeasureTheory

variable {α : Type*}

/-- The union of a nonempty directed family of algebras of sets is an algebra of sets, as
`isPiSystem_iUnion_of_directed_le` is for π-systems. It applies to the measurable sets of the
σ-algebras of a filtration. -/
theorem isSetAlgebra_iUnion_of_directed_le {ι : Type*} [Nonempty ι] (p : ι → Set (Set α))
    (hp : ∀ i, IsSetAlgebra (p i)) (hp_directed : Directed (· ≤ ·) p) :
    IsSetAlgebra (⋃ i, p i) where
  empty_mem := mem_iUnion.2 ⟨Classical.arbitrary ι, (hp _).empty_mem⟩
  compl_mem s hs := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hs
    exact mem_iUnion.2 ⟨i, (hp i).compl_mem hi⟩
  union_mem s t hs ht := by
    obtain ⟨i, hi⟩ := mem_iUnion.1 hs
    obtain ⟨j, hj⟩ := mem_iUnion.1 ht
    obtain ⟨k, hik, hjk⟩ := hp_directed i j
    exact mem_iUnion.2 ⟨k, (hp k).union_mem (hik hi) (hjk hj)⟩

end MeasureTheory
