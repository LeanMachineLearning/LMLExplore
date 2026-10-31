/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary bounds on the real logarithm

## Main statements

* `Real.min_one_le_two_mul_log_one_add`: `min 1 u ≤ 2 log (1 + u)` for `u ≥ 0`.
* `Real.monotoneOn_log_one_add_mul_log_sq`: `x ↦ log (1 + x log² x)` is monotone on `[1, ∞)`.
-/

public section

namespace Real

/-- For `u ≥ 0`, `min 1 u ≤ 2 log (1 + u)`. -/
theorem min_one_le_two_mul_log_one_add {u : ℝ} (hu : 0 ≤ u) : min 1 u ≤ 2 * log (1 + u) := by
  have hpos : 0 < u + 2 := by linarith
  have h : min 1 u ≤ 2 * (2 * u / (u + 2)) := by
    rw [show 2 * (2 * u / (u + 2)) = 4 * u / (u + 2) by ring, le_div_iff₀ hpos]
    rcases le_total u 2 with hu2 | hu2
    · nlinarith [mul_le_mul_of_nonneg_right (min_le_right 1 u) hpos.le,
        mul_nonneg hu (sub_nonneg.2 hu2)]
    · nlinarith [mul_le_mul_of_nonneg_right (min_le_left 1 u) hpos.le]
  linarith [le_log_one_add_of_nonneg hu]

/-- The function `x ↦ log (1 + x log² x)` is monotone on `[1, ∞)`. It is the logarithm of the
exploration function `f(x) = 1 + x log² x` of the asymptotically optimal UCB and KL-UCB
algorithms. -/
theorem monotoneOn_log_one_add_mul_log_sq :
    MonotoneOn (fun x ↦ log (1 + x * log x ^ 2)) (Set.Ici 1) := by
  intro x hx y hy hxy
  rw [Set.mem_Ici] at hx hy
  have hx0 : 0 ≤ log x := log_nonneg hx
  have hlog : log x ≤ log y := log_le_log (by linarith) hxy
  have hy0 : 0 ≤ y := by linarith
  dsimp only
  gcongr

end Real
