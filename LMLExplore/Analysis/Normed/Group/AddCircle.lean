/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Approximation by the subgroup `(1 / N) ℤ` of the circle

Every point of the circle `UnitAddCircle = ℝ / ℤ` is within `1 / (2 N)` of the subgroup
`(1 / N) ℤ`, for `N > 0`: some shift of any point `y` by a multiple of `1 / N` is within
`1 / (2 N)` of any other point `x₀`.

## Main statements

* `UnitAddCircle.exists_norm_add_intCast_div_sub_le`: for `N > 0`, some shift of `y` by a
  multiple `m / N` is within `1 / (2 N)` of `x₀`.
-/

public section

namespace UnitAddCircle

/-- For any two points `y` and `x₀` of the circle and `N > 0`, some shift of `y` by a multiple
`m / N` of `1 / N` is within `1 / (2 N)` of `x₀`. -/
theorem exists_norm_add_intCast_div_sub_le (y x₀ : UnitAddCircle) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℤ, ‖y + (((m : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle) - x₀‖ ≤ 1 / (2 * N) := by
  induction y using QuotientAddGroup.induction_on with | H a =>
  induction x₀ using QuotientAddGroup.induction_on with | H b =>
  have hN' : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set t := b - a with ht
  refine ⟨round (N * t), ?_⟩
  rw [← AddCircle.coe_add, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  have h : a + ((round (N * t) : ℤ) : ℝ) / N - b = ((round (N * t) : ℤ) : ℝ) / N - t := by
    rw [ht]
    ring
  rw [h]
  calc |(((round (N * t) : ℤ) : ℝ) / N - t) - round ((((round (N * t) : ℤ) : ℝ) / N - t))|
  _ ≤ |(((round (N * t) : ℤ) : ℝ) / N - t) - ((0 : ℤ) : ℝ)| := round_le _ 0
  _ = |N * t - round (N * t)| / N := by
    rw [Int.cast_zero, sub_zero, ← abs_neg, neg_sub,
      show t - ((round (N * t) : ℤ) : ℝ) / N = (N * t - round (N * t)) / N by field_simp,
      abs_div, abs_of_pos hN']
  _ ≤ (1 / 2) / N := by gcongr; exact abs_sub_round _
  _ = 1 / (2 * N) := by field_simp

end UnitAddCircle
