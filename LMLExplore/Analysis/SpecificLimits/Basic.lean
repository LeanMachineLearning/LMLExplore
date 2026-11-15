/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Limits of ratios to `n` of sequences within bounded distance of a linear sequence

A real sequence `u` that stays within a fixed distance `c` of the linear sequence `n ↦ n w`
satisfies `u n / n → w`. Numbers of pulls of bandit algorithms that track static proportions `w`
up to a bounded error have this form, and so does the number `n / m` of complete blocks of `m`
terms among the first `n`.

## Main statements

* `LMLExplore.tendsto_div_natCast_of_abs_sub_mul_le`: if `|u n - n w| ≤ c` for every `n`, then
  `u n / n → w`.
* `LMLExplore.tendsto_nat_div_div_atTop`: for `m ≠ 0`, the number `n / m` of complete blocks of
  `m` among the first `n` natural numbers satisfies `(n / m) / n → 1 / m`.
-/

public section

open Filter Topology

namespace LMLExplore

/-- If `|u n - n w| ≤ c` for every `n`, then `u n / n → w`. -/
theorem tendsto_div_natCast_of_abs_sub_mul_le {u : ℕ → ℝ} {w c : ℝ}
    (h : ∀ n : ℕ, |u n - n * w| ≤ c) : Tendsto (fun n : ℕ ↦ u n / n) atTop (𝓝 w) := by
  have h0 : Tendsto (fun n : ℕ ↦ (u n - n * w) / n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) (tendsto_const_div_atTop_nhds_zero_nat c)
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    exact div_le_div_of_nonneg_right (h n) n.cast_nonneg
  have h1 : Tendsto (fun n : ℕ ↦ (u n - n * w) / n + w) atTop (𝓝 w) := by
    simpa using h0.add_const w
  refine h1.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [sub_div, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 hn), sub_add_cancel]

/-- The number of complete blocks of `m ≠ 0` terms among the first `n`, divided by `n`, tends to
`1 / m`: `n / m` is within distance `1` of `n / m` computed in `ℝ`. -/
theorem tendsto_nat_div_div_atTop {m : ℕ} (hm : m ≠ 0) :
    Tendsto (fun n : ℕ ↦ ((n / m : ℕ) : ℝ) / n) atTop (𝓝 (m : ℝ)⁻¹) := by
  refine tendsto_div_natCast_of_abs_sub_mul_le (c := 1) fun n ↦ ?_
  have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  -- `(n / m) * m ≤ n < (n / m) * m + m`
  have h1 : ((n / m : ℕ) : ℝ) ≤ n * (m : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hm']
    exact_mod_cast Nat.div_mul_le_self n m
  have h2 : (n : ℝ) * (m : ℝ)⁻¹ < (n / m : ℕ) + 1 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hm', add_mul, one_mul]
    exact_mod_cast Nat.lt_div_mul_add (Nat.pos_of_ne_zero hm)
  rw [abs_le]
  constructor <;> linarith

end LMLExplore
