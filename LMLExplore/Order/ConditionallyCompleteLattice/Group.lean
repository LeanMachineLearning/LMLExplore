/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Absolute value of an indexed supremum

## Main statements

* `abs_ciSup_le`: in a conditionally complete linearly ordered additive group, if `|f i| ≤ B` for
  every `i` of a nonempty index type, then `|⨆ i, f i| ≤ B`.
-/

public section

open Set

variable {α : Type*} {ι : Sort*} [ConditionallyCompleteLinearOrder α] [AddCommGroup α]
  [IsOrderedAddMonoid α]

/-- A uniform bound `|f i| ≤ B` on a nonempty family bounds the absolute value of its supremum. -/
theorem abs_ciSup_le [Nonempty ι] {f : ι → α} {B : α} (h : ∀ i, |f i| ≤ B) : |⨆ i, f i| ≤ B := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact abs_le.2 ⟨(abs_le.1 (h i)).1.trans
    (le_ciSup ⟨B, forall_mem_range.2 fun i ↦ (abs_le.1 (h i)).2⟩ i),
    ciSup_le fun i ↦ (abs_le.1 (h i)).2⟩
