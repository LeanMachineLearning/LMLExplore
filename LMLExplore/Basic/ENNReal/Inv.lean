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
* `ENNReal.le_of_forall_natCast_mul_le_add_mul`: if `m * a ≤ (m + K) * b` for every positive
  integer `m`, then `a ≤ b`.
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

/-- If `m * a ≤ (m + K) * b` for every positive integer `m`, then `a ≤ b`: the ratio
`(m + K) / m` tends to `1`. -/
lemma le_of_forall_natCast_mul_le_add_mul {a b : ℝ≥0∞} (K : ℕ)
    (h : ∀ m : ℕ, 0 < m → (m : ℝ≥0∞) * a ≤ (m + K) * b) : a ≤ b := by
  rcases eq_or_ne b ⊤ with hb | hb
  · rw [hb]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) hb) (ENNReal.coe_ne_zero.2 hε.ne'))
  have hm' : (K : ℝ≥0∞) * b ≤ (m + 1 : ℕ) * ε := by
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.coe_ne_zero.2 hε.ne')) (Or.inl ENNReal.coe_ne_top)]
      at hm
    exact hm.le.trans (mul_le_mul_left (by exact_mod_cast Nat.le_succ m) _)
  have hm0 : ((m + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine (ENNReal.mul_le_mul_iff_right hm0 (ENNReal.natCast_ne_top _)).1 ?_
  calc ((m + 1 : ℕ) : ℝ≥0∞) * a ≤ ((m + 1 : ℕ) + K) * b := h (m + 1) m.succ_pos
  _ = (m + 1 : ℕ) * b + K * b := add_mul _ _ _
  _ ≤ (m + 1 : ℕ) * b + (m + 1 : ℕ) * ε := by gcongr
  _ = (m + 1 : ℕ) * (b + ε) := (mul_add _ _ _).symm

end ENNReal
