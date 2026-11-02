/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.Bounds.Basic

/-!
# Attained maxima of monotone maps

## Main statements

* `Monotone.of_isGreatest_range`: the maximum of a family of monotone maps is monotone, when it is
  attained: `B x` is the greatest of the values `T d x`.
-/

public section

open Set

/-- The maximum of monotone maps is monotone, when it is attained: `B x` is the greatest of the
values `T d x`. -/
theorem Monotone.of_isGreatest_range {α D : Type*} [Preorder α] {T : D → α → α} {B : α → α}
    (hT : ∀ d, Monotone (T d)) (hB : ∀ x, IsGreatest (range fun d ↦ T d x) (B x)) :
    Monotone B := fun x y hxy ↦ by
  obtain ⟨d, hd⟩ := (hB x).1
  rw [← hd]
  exact (hT d hxy).trans ((hB y).2 ⟨d, rfl⟩)
