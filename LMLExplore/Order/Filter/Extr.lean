/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima are invariant under adding a constant

Adding a constant to a function into an ordered additive structure with cancellation changes none
of its minimum points, with respect to a filter or on a set.

## Main statements

* `isMinFilter_add_const_iff`: `fun b ↦ f b + c` has a minimum at `a` with respect to `l` iff `f`
  does.
* `isMinOn_add_const_iff`: `fun b ↦ f b + c` has a minimum at `a` on `s` iff `f` does.
-/

public section

variable {α β : Type*} [Add β] [Preorder β] [AddRightMono β] [AddRightReflectLE β]
  {f : α → β} {l : Filter α} {s : Set α} {a : α}

/-- Adding a constant to a function changes none of its minimum points with respect to a
filter. -/
theorem isMinFilter_add_const_iff (c : β) :
    IsMinFilter (fun b ↦ f b + c) l a ↔ IsMinFilter f l a := by
  simp only [IsMinFilter, add_le_add_iff_right]

/-- Adding a constant to a function changes none of its minimum points on a set. -/
theorem isMinOn_add_const_iff (c : β) : IsMinOn (fun b ↦ f b + c) s a ↔ IsMinOn f s a :=
  isMinFilter_add_const_iff c
