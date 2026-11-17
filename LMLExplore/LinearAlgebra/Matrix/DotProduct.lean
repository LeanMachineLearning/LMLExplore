/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Matrix.Mul

/-!
# Bounds on dot products

A dot product `u ⬝ᵥ x` over a linearly ordered ring is at most `(∑ a, |u a|) ρ` in absolute value
when every coordinate of `x` is at most `ρ` in absolute value: the `ℓ¹`–`ℓ^∞` Hölder bound.

## Main statements

* `LMLExplore.abs_dotProduct_le_sum_abs_mul`: `|u ⬝ᵥ x| ≤ (∑ a, |u a|) ρ` when `|x a| ≤ ρ` for
  every `a`.
-/

public section

namespace LMLExplore

variable {α R : Type*} [Fintype α] [Ring R] [LinearOrder R] [IsOrderedRing R]

/-- A vector `x` with coordinates at most `ρ` in absolute value has
`|u ⬝ᵥ x| ≤ (∑ a, |u a|) ρ`. -/
theorem abs_dotProduct_le_sum_abs_mul (u : α → R) {x : α → R} {ρ : R} (hx : ∀ a, |x a| ≤ ρ) :
    |u ⬝ᵥ x| ≤ (∑ a, |u a|) * ρ :=
  calc |u ⬝ᵥ x| ≤ ∑ a, |u a * x a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |u a| * ρ := Finset.sum_le_sum fun a _ ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hx a) (abs_nonneg _)
    _ = (∑ a, |u a|) * ρ := by rw [Finset.sum_mul]

end LMLExplore
