/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Interval

/-!
# Finite sets of integers of small diameter

A finite set of integers whose elements are pairwise less than `d` apart lies in an interval
`[a, a + d)`, so it has at most `d` elements. The cycle lemma in
`LMLExplore.EValues.MultipleTesting.RunningMaxima.LowerBound` uses it to count the shifts of a
walk whose values are pairwise close.

## Main statements

* `Int.card_le_toNat_of_forall_lt_add`: a finite set of integers whose elements are less than `d`
  apart has at most `d.toNat` elements.
-/

public section

namespace Int

/-- A finite set of integers whose elements are less than `d` apart has at most `d` elements. -/
theorem card_le_toNat_of_forall_lt_add {S : Finset ℤ} {d : ℤ}
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≤ y → y < x + d) :
    S.card ≤ d.toNat := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hsub : S ⊆ Finset.Ico (S.min' hS) (S.min' hS + d) := fun x hx ↦
    Finset.mem_Ico.2 ⟨S.min'_le x hx, h _ (S.min'_mem hS) x hx (S.min'_le x hx)⟩
  calc S.card ≤ (Finset.Ico (S.min' hS) (S.min' hS + d)).card := Finset.card_le_card hsub
    _ = d.toNat := by simp

end Int
