/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Order.Interval.Set.Defs

/-!
# The square of a difference of two points of an interval

Two points `x` and `y` of `[c, d]` in a linearly ordered ring are within `d - c` of each other, so
`(x - y) ^ 2` lies in `[0, (d - c) ^ 2]`. This bounds the centred squares `(f - m) ^ 2` of a
function `f` with values in `[c, d]` around a mean `m ∈ [c, d]`, in the transport of variances.

## Main statements

* `sq_sub_mem_Icc_of_mem_Icc`: `(x - y) ^ 2 ∈ [0, (d - c) ^ 2]` for `x, y ∈ [c, d]`.
-/

public section

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {x y c d : R}

/-- For `x, y ∈ [c, d]`, the square `(x - y) ^ 2` lies in `[0, (d - c) ^ 2]`. -/
theorem sq_sub_mem_Icc_of_mem_Icc (hx : x ∈ Set.Icc c d) (hy : y ∈ Set.Icc c d) :
    (x - y) ^ 2 ∈ Set.Icc 0 ((d - c) ^ 2) :=
  ⟨sq_nonneg _, sq_le_sq' (by rw [neg_sub]; exact sub_le_sub hx.1 hy.2) (sub_le_sub hx.2 hy.1)⟩
