/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Bounds in linearly ordered fields

For nonnegative `x` and `y` in a linearly ordered semifield, `x y / (x + y)` (half the harmonic
mean of `x` and `y`) is at most `x` and at most `y`. In a linearly ordered field, an affine
function `t ↦ A + t * B` that is bounded below on `t ≥ 0` has a nonnegative slope `B`, and
`-g / L ∈ [-1, 1]` when `|g| ≤ L` with `L > 0`.

## Main statements

* `mul_div_add_le_left`: `x y / (x + y) ≤ x` for `0 ≤ x` and `0 ≤ y`.
* `mul_div_add_le_right`: `x y / (x + y) ≤ y` for `0 ≤ x` and `0 ≤ y`.
* `nonneg_of_forall_lt_add_mul`: if `v < A + t * B` for every `t ≥ 0`, then `0 ≤ B`.
* `abs_neg_div_le_one`: `|-g / L| ≤ 1` for `0 < L` and `|g| ≤ L`.
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
  have h0 : v < A := by simpa using h 0 le_rfl
  -- at `t = (A - v) / -B`, the affine function takes the value `v`
  have h1 := h ((A - v) / -B) (div_nonneg (sub_nonneg.2 h0.le) (neg_nonneg.2 hB.le))
  field_simp [hB.ne] at h1
  linarith

/-- For `0 < L` and `|g| ≤ L`, the rescaled opposite `-g / L` lies in `[-1, 1]`. -/
theorem abs_neg_div_le_one {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {g L : K} (hL : 0 < L) (hg : |g| ≤ L) : |-g / L| ≤ 1 := by
  rw [abs_div, abs_neg, abs_of_pos hL, div_le_one hL]
  exact hg
