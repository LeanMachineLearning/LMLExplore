/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Indexed suprema in conditionally complete lattices

## Main statements

* `ciSup_mem_Icc`: a supremum of values in `[a, b]` over a nonempty index type lies in `[a, b]`.
-/

public section

open Set

variable {α : Type*} {ι : Sort*} [ConditionallyCompleteLattice α]

/-- A supremum of values in `[a, b]` over a nonempty index type lies in `[a, b]`. -/
theorem ciSup_mem_Icc [Nonempty ι] {f : ι → α} {a b : α} (h : ∀ i, f i ∈ Icc a b) :
    (⨆ i, f i) ∈ Icc a b :=
  ⟨(h (Classical.arbitrary ι)).1.trans (le_ciSup ⟨b, forall_mem_range.2 fun i ↦ (h i).2⟩ _),
    ciSup_le fun i ↦ (h i).2⟩
