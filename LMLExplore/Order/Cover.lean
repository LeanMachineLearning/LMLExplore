/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.Cover

/-!
# Separating levels in a linear order

In a linear order that need not be dense, two values `a < b` can be separated by levels `c > a`
and `d < b` such that every value below `c` is at most `d`: take `c = b` and `d = a` if `b` covers
`a`, and `c = d` strictly between them otherwise. This replaces `exists_between` in arguments,
such as those on semicontinuity, that must hold in every linear order.
-/

public section

variable {α : Type*} [LinearOrder α] {a b : α}

/-- Two values `a < b` of a linear order are separated by levels `c > a` and `d < b` such that
every value below `c` is at most `d`. -/
theorem exists_gt_exists_lt_forall_lt_le (h : a < b) : ∃ c > a, ∃ d < b, ∀ e < c, e ≤ d := by
  by_cases hab : a ⋖ b
  · exact ⟨b, h, a, h, fun e he ↦ hab.le_of_lt he⟩
  · obtain ⟨c, h₁, h₂⟩ := (not_covBy_iff h).1 hab
    exact ⟨c, h₁, c, h₂, fun e he ↦ he.le⟩
