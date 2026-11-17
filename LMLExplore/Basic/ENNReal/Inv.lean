/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv

/-!
# Inverses of extended nonnegative reals

## Main statements

* `ENNReal.exists_nnreal_lt_one_lt_mul_of_inv_lt`: if `D⁻¹ < c` for `D : ℝ≥0∞` and `c : ℝ≥0`,
  then some `κ : ℝ≥0` satisfies `κ < D` and `1 < κ * c`.
* `ENNReal.div_le_inv_mul_of_le_inv`: if `H ≤ a⁻¹`, then `a / b ≤ (H * b)⁻¹`.
-/

public section

open scoped ENNReal NNReal

namespace ENNReal

/-- If `D⁻¹ < c` for `D : ℝ≥0∞` and `c : ℝ≥0`, then some `κ : ℝ≥0` lies strictly below `D` and
satisfies `1 < κ * c`. -/
lemma exists_nnreal_lt_one_lt_mul_of_inv_lt {D : ℝ≥0∞} {c : ℝ≥0} (hc : D⁻¹ < c) :
    ∃ κ : ℝ≥0, (κ : ℝ≥0∞) < D ∧ 1 < κ * c := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact not_lt_zero (ENNReal.coe_zero ▸ hc)
  rw [ENNReal.inv_lt_iff_inv_lt, ← ENNReal.coe_inv hc0] at hc
  obtain ⟨κ, hcκ, hκ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
  refine ⟨κ, hκ, ?_⟩
  rw [← inv_mul_cancel₀ hc0]
  exact mul_lt_mul_of_pos_right (ENNReal.coe_lt_coe.1 hcκ) (pos_iff_ne_zero.2 hc0)

/-- If `H ≤ a⁻¹`, then `a / b ≤ (H * b)⁻¹` for every `b`. -/
lemma div_le_inv_mul_of_le_inv {a b H : ℝ≥0∞} (hH : H ≤ a⁻¹) : a / b ≤ (H * b)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le] at hH ⊢
  calc a / b * (H * b) = H * a * (b⁻¹ * b) := by rw [div_eq_mul_inv]; ring
    _ ≤ 1 * 1 := mul_le_mul' hH (ENNReal.inv_mul_le_one b)
    _ = 1 := one_mul 1

end ENNReal
