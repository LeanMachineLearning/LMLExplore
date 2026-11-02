/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# Bounds on `x y / (x + y)`

For nonnegative `x` and `y` in a linearly ordered semifield, `x y / (x + y)` (half the harmonic
mean of `x` and `y`) is at most `x` and at most `y`.

## Main statements

* `mul_div_add_le_left`: `x y / (x + y) ≤ x` for `0 ≤ x` and `0 ≤ y`.
* `mul_div_add_le_right`: `x y / (x + y) ≤ y` for `0 ≤ x` and `0 ≤ y`.
-/

public section

variable {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {x y : K}

/-- `x y / (x + y) ≤ x` for `0 ≤ x` and `0 ≤ y`. -/
theorem mul_div_add_le_left (hx : 0 ≤ x) (hy : 0 ≤ y) : x * y / (x + y) ≤ x :=
  div_le_of_le_mul₀ (add_nonneg hx hy) hx
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx) hx)

/-- `x y / (x + y) ≤ y` for `0 ≤ x` and `0 ≤ y`. -/
theorem mul_div_add_le_right (hx : 0 ≤ x) (hy : 0 ≤ y) : x * y / (x + y) ≤ y := by
  rw [mul_comm, add_comm]
  exact mul_div_add_le_left hy hx
