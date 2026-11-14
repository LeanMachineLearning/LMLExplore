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
up to a bounded error have this form.

## Main statements

* `LMLExplore.tendsto_div_natCast_of_abs_sub_mul_le`: if `|u n - n w| ≤ c` for every `n`, then
  `u n / n → w`.
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

end LMLExplore
