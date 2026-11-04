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
* `abs_ciSup_sub_ciSup_le`: if `g` is bounded above over a nonempty index type and
  `|f i - g i| ≤ c` for every `i`, then `|⨆ i, f i - ⨆ i, g i| ≤ c`.
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

/-- If `g` is bounded above over a nonempty index type and `f` is within `c` of `g` at every
index, then the suprema of `f` and `g` are within `c` of each other. -/
theorem abs_ciSup_sub_ciSup_le [Nonempty ι] {f g : ι → α} {c : α} (hg : BddAbove (range g))
    (h : ∀ i, |f i - g i| ≤ c) : |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  have hf : BddAbove (range f) := by
    obtain ⟨B, hB⟩ := hg
    exact ⟨c + B, forall_mem_range.2 fun i ↦ (sub_le_iff_le_add.1 (abs_sub_le_iff.1 (h i)).1).trans
      (add_le_add_right (hB (mem_range_self i)) c)⟩
  refine abs_sub_le_iff.2 ⟨sub_le_iff_le_add.2 (ciSup_le fun i ↦ ?_),
    sub_le_iff_le_add.2 (ciSup_le fun i ↦ ?_)⟩
  · calc f i ≤ c + g i := sub_le_iff_le_add.1 (abs_sub_le_iff.1 (h i)).1
      _ ≤ c + ⨆ i, g i := by gcongr; exact le_ciSup hg i
  · calc g i ≤ c + f i := sub_le_iff_le_add.1 (abs_sub_le_iff.1 (h i)).2
      _ ≤ c + ⨆ i, f i := by gcongr; exact le_ciSup hf i
