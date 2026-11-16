/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Types with two elements

In a finite type with exactly two elements `a ≠ b`, every element other than `b` is `a`. This is
the step that identifies the other arm in a bandit with two arms.
-/

public section

namespace Fintype

variable {α : Type*} [Fintype α] {a b c : α}

/-- In a type with two elements `a ≠ b`, every element other than `b` is `a`. -/
theorem eq_of_ne_of_card_eq_two (hα : Fintype.card α = 2) (hab : a ≠ b) (hc : c ≠ b) : c = a :=
  ((Nat.card_eq_two_iff' b).mp (Nat.card_eq_fintype_card.trans hα)).unique hc hab

end Fintype
