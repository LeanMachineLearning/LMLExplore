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
* `Real.tendsto_log_one_add_mul_log_sq_div_log_atTop`: `log (1 + x log² x) / log x → 1` as
  `x → ∞`.
* `Real.eventually_lt_mul_log_of_tendsto_div_log`: if `g n / log n → D` and `D < c`, then
  eventually `g n < c log n`.
-/

public section

open Filter Topology

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

/-- `log (1 + x log² x) / log x → 1` as `x → ∞`: the exploration level `log f(x)` of the
asymptotically optimal UCB and KL-UCB algorithms, with `f(x) = 1 + x log² x`, is asymptotically
`log x`. -/
theorem tendsto_log_one_add_mul_log_sq_div_log_atTop :
    Tendsto (fun x ↦ log (1 + x * log x ^ 2) / log x) atTop (𝓝 1) := by
  have h_rem : Tendsto (fun x ↦ 1 + (log 2 + 2 * log (log x)) / log x) atTop (𝓝 1) := by
    have h_div : Tendsto (fun y ↦ log y / y) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h := ((tendsto_const_nhds (x := log 2)).div_atTop tendsto_log_atTop).add
      ((h_div.comp tendsto_log_atTop).const_mul 2)
    simpa [add_div, mul_div_assoc] using h.const_add 1
  -- For `x ≥ e`, `log x ≤ log (1 + x log² x) ≤ log (2 x log² x) = log 2 + log x + 2 log log x`.
  have h_large : ∀ᶠ x in atTop, 1 ≤ x ∧ 1 ≤ log x := by
    filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    have hx0 : 0 < x := (exp_pos 1).trans_le hx
    exact ⟨(one_le_exp zero_le_one).trans hx, (le_log_iff_exp_le hx0).mpr hx⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_rem ?_ ?_
  · filter_upwards [h_large] with x ⟨hx1, hlog⟩
    have hsq : 1 ≤ log x ^ 2 := one_le_pow₀ hlog
    rw [le_div_iff₀ (by linarith), one_mul]
    exact log_le_log (by linarith) (by nlinarith)
  · filter_upwards [h_large] with x ⟨hx1, hlog⟩
    have hsq : 1 ≤ log x ^ 2 := one_le_pow₀ hlog
    have hL : log (1 + x * log x ^ 2) ≤ log 2 + log x + 2 * log (log x) := by
      calc log (1 + x * log x ^ 2) ≤ log (2 * x * log x ^ 2) :=
        log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith)])
      _ = log 2 + log x + 2 * log (log x) := by
        rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity),
          log_pow]
        push_cast
        ring
    rw [div_le_iff₀ (by linarith), add_mul, div_mul_cancel₀ _ (by linarith)]
    linarith

/-- If `g n / log n → D` as `n → ∞` and `D < c`, then eventually `g n < c log n`. -/
theorem eventually_lt_mul_log_of_tendsto_div_log {g : ℕ → ℝ} {D c : ℝ}
    (hg : Tendsto (fun n : ℕ ↦ g n / log n) atTop (𝓝 D)) (hc : D < c) :
    ∀ᶠ n : ℕ in atTop, g n < c * log n := by
  filter_upwards [hg.eventually_lt_const hc,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0] with n hn hlog
  exact (div_lt_iff₀ hlog).mp hn

end Real
