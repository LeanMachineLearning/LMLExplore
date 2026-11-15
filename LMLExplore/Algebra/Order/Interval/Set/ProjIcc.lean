/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Order.Filter.Extr
public import Mathlib.Order.Interval.Set.ProjIcc

/-!
# The projection onto a closed interval is a nearest point

In a linearly ordered additive group, `Set.projIcc a b h x` is a point of `[a, b]` nearest to `x`
for the distance `|y - x|`: it minimizes `y ↦ |y - x|` over `[a, b]`. This is the projection step
of projected online subgradient descent on an interval of `ℝ`, and coordinatewise on a box.

## Main statements

* `Set.isMinOn_abs_sub_projIcc`: `projIcc a b h x` minimizes `y ↦ |y - x|` over `Icc a b`.
-/

public section

namespace Set

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}

/-- **The projection onto a closed interval is a nearest point**: `projIcc a b h x` minimizes the
distance `y ↦ |y - x|` to `x` over `[a, b]`. -/
theorem isMinOn_abs_sub_projIcc (h : a ≤ b) (x : α) :
    IsMinOn (fun y ↦ |y - x|) (Icc a b) (projIcc a b h x : α) := by
  refine isMinOn_iff.mpr fun y hy ↦ ?_
  rcases le_total x a with hxa | hax
  · rw [projIcc_of_le_left h hxa, abs_of_nonneg (sub_nonneg.mpr hxa),
      abs_of_nonneg (sub_nonneg.mpr (hxa.trans hy.1))]
    exact sub_le_sub_right hy.1 x
  rcases le_total b x with hbx | hxb
  · rw [projIcc_of_right_le h hbx, abs_of_nonpos (sub_nonpos.mpr hbx),
      abs_of_nonpos (sub_nonpos.mpr (hy.2.trans hbx))]
    exact neg_le_neg (sub_le_sub_right hy.2 x)
  · rw [projIcc_of_mem h ⟨hax, hxb⟩, sub_self, abs_zero]
    exact abs_nonneg _

end Set
