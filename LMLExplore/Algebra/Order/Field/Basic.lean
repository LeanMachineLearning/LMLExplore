/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# Bounds in linearly ordered fields

For nonnegative `x` and `y` in a linearly ordered semifield, `x y / (x + y)` (half the harmonic
mean of `x` and `y`) is at most `x` and at most `y`. In a linearly ordered field, an affine
function `t ↦ A + t * B` that is bounded below on `t ≥ 0` has a nonnegative slope `B`.

## Main statements

* `mul_div_add_le_left`: `x y / (x + y) ≤ x` for `0 ≤ x` and `0 ≤ y`.
* `mul_div_add_le_right`: `x y / (x + y) ≤ y` for `0 ≤ x` and `0 ≤ y`.
* `nonneg_of_forall_lt_add_mul`: if `v < A + t * B` for every `t ≥ 0`, then `0 ≤ B`.
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

/-- If `v < A + t * B` for every `t ≥ 0`, then `B` is nonnegative. -/
theorem nonneg_of_forall_lt_add_mul {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A B v : K} (h : ∀ t : K, 0 ≤ t → v < A + t * B) : 0 ≤ B := by
  by_contra! hB
  have h1 := h _ (le_max_left 0 ((A - v) / -B))
  have h3 : max 0 ((A - v) / -B) * B ≤ (A - v) / -B * B :=
    mul_le_mul_of_nonpos_right (le_max_right _ _) hB.le
  have h4 : (A - v) / -B * B = -(A - v) := by rw [div_neg, neg_mul, div_mul_cancel₀ _ hB.ne]
  have h5 := h1.trans_le ((add_le_add_iff_left A).2 h3)
  rw [h4, neg_sub, add_sub_cancel] at h5
  exact lt_irrefl v h5
