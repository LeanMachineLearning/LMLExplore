/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.MinMulSubLogLog
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The calibration function `𝒞^exp` of Kaufmann and Koolen

Kaufmann and Koolen [KK21, Theorem 7] bound the deviations of the empirical means of several arms
of exponential families uniformly in time: for a set `S` of arms and `x > 0`, with
`X_a(t) = [N_a(t) d(μ̂_a(t), μ_a) - 3 log (1 + log N_a(t))]⁺`,
`P(∃ t, ∑_{a ∈ S} X_a(t) ≥ |S| 𝒞^exp(x / |S|)) ≤ e^{-x}`.
Their proof gives, for every `ξ ∈ (0, 1/2]` and `λ ∈ (0, 1 / (1 + ξ))`, the threshold
`|S| (x / |S| + g_ξ(λ)) / λ` with `g_ξ(λ) = λ (1 + ξ) log C(ξ) - log (1 - λ (1 + ξ))` and
`C(ξ) = 2 ζ(2) / log² (1 + ξ)`, and `𝒞^exp` is the optimal tuning of `ξ` and `λ`
[KK21, Lemma 12]. This file defines `𝒞^exp` by its closed form [KK21, (10)], proves that it is that
optimum, and bounds it: `𝒞^exp(x) = x + O(log (1 + x))`, with explicit constants.

The closed form uses the inverse `h⁻¹` of `h(u) = u - log u` on `[1, ∞)` (`Real.subLogInv`) and
the function `H_z(x) = min_{y ∈ (1, z]} y (x - log log y)` of [KK21, Definition 29]
(`LMLExplore.minMulSubLogLog`): `𝒞^exp(x) = 2 H_{3/2}((h⁻¹(1 + x) + log (2 ζ(2))) / 2)`, where
`2 ζ(2) = π² / 3`.

## Main definitions

* `LMLExplore.calibrationExp x`: `𝒞^exp(x)` [KK21, (10)].

## Main statements

* `LMLExplore.calibrationExp_eq`: the defining equation of `𝒞^exp` in terms of `H_{3/2}`.
* `LMLExplore.isLeast_calibrationExp`: `𝒞^exp(x)` is the optimal tuning of [KK21, Lemma 12].
* `LMLExplore.monotone_calibrationExp`, `LMLExplore.one_add_add_log_le_calibrationExp`,
  `LMLExplore.calibrationExp_le_add_three_mul_log_add`: `𝒞^exp` is monotone and, for `x ≥ 0`,
  `1 + x + log (1 + x) ≤ 𝒞^exp(x) ≤ x + 3 log (1 + x) + 11`.

## References

* [KK21] E. Kaufmann and W. M. Koolen, *Mixture martingales revisited with applications to
  sequential tests and confidence intervals*, JMLR 22 (2021), (10), Theorem 7 and Lemma 12.
-/

public section

open Real Set

namespace LMLExplore

/-- The calibration function `𝒞^exp(x) = 2 H_{3/2}((h⁻¹(1 + x) + log (2 ζ(2))) / 2)` of the
time-uniform deviation inequality of Kaufmann and Koolen for several arms of exponential families
[KK21, (10), Theorem 7], with `2 ζ(2) = π² / 3` (Mathlib's `hasSum_zeta_two`). -/
noncomputable def calibrationExp (x : ℝ) : ℝ :=
  2 * minMulSubLogLog (3 / 2) ((subLogInv (1 + x) + log (π ^ 2 / 3)) / 2)

/-- The defining equation `𝒞^exp(x) = 2 H_{3/2}((h⁻¹(1 + x) + log (π² / 3)) / 2)`. -/
theorem calibrationExp_eq (x : ℝ) :
    calibrationExp x = 2 * minMulSubLogLog (3 / 2) ((subLogInv (1 + x) + log (π ^ 2 / 3)) / 2) := by
  rw [calibrationExp]

private theorem three_halves_le_exp_one : (3 / 2 : ℝ) ≤ exp 1 := by
  linarith [add_one_le_exp (1 : ℝ)]

/-- `𝒞^exp(x)` is the optimal tuning of [KK21, Lemma 12] for `C(ξ) = 2 ζ(2) / log² (1 + ξ)` and
`ξ ∈ (0, 1/2]`: for `x > 0` it is the minimum of `(x + g_ξ(λ)) / λ`, with
`g_ξ(λ) = λ (1 + ξ) log C(ξ) - log (1 - λ (1 + ξ))`, over `ξ ∈ (0, 1/2]` and
`λ ∈ (0, 1 / (1 + ξ))`. -/
theorem isLeast_calibrationExp {x : ℝ} (hx : 0 < x) :
    IsLeast {v | ∃ ξ ∈ Ioc 0 (1 / 2 : ℝ), ∃ l ∈ Ioo 0 (1 + ξ)⁻¹,
        v = (x - log (1 - l * (1 + ξ))) / l + (1 + ξ) * log (π ^ 2 / 3 / log (1 + ξ) ^ 2)}
      (calibrationExp x) := by
  have h := isLeast_two_mul_minMulSubLogLog (c := π ^ 2 / 3) (z := 1 / 2) (by positivity) hx
    (by norm_num) (by linarith [three_halves_le_exp_one])
  rw [calibrationExp_eq]
  rwa [show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] at h

theorem monotone_calibrationExp : Monotone calibrationExp := by
  intro x x' hxx'
  rw [calibrationExp_eq, calibrationExp_eq]
  refine mul_le_mul_of_nonneg_left (monotone_minMulSubLogLog (by norm_num)
    three_halves_le_exp_one ?_) zero_le_two
  gcongr
  exact monotone_subLogInv (by linarith)

/-- `1 ≤ log (π² / 3)`. -/
private theorem one_le_log_pi_sq_div_three : 1 ≤ log (π ^ 2 / 3) := by
  rw [le_log_iff_exp_le (by positivity)]
  have := exp_one_lt_d9
  have := pi_gt_three
  nlinarith

/-- `log (π² / 3) ≤ 2`. -/
private theorem log_pi_sq_div_three_le_two : log (π ^ 2 / 3) ≤ 2 := by
  rw [log_le_iff_le_exp (by positivity)]
  have h5 := quadratic_le_exp_of_nonneg (zero_le_two (α := ℝ))
  have := pi_lt_d2
  have := pi_pos
  nlinarith

/-- The lower bound `1 + x + log (1 + x) ≤ 𝒞^exp(x)` for `x ≥ 0`. -/
theorem one_add_add_log_le_calibrationExp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + log (1 + x) ≤ calibrationExp x := by
  have hY : 0 ≤ (subLogInv (1 + x) + log (π ^ 2 / 3)) / 2 := by
    have := one_le_log_pi_sq_div_three
    have := one_le_subLogInv (1 + x)
    positivity
  have h := self_le_minMulSubLogLog (by norm_num) three_halves_le_exp_one hY
  have h1 := Real.add_log_le_subLogInv (by linarith : (0 : ℝ) < 1 + x)
  have h2 := one_le_log_pi_sq_div_three
  rw [calibrationExp_eq]
  linarith

/-- The upper bound `𝒞^exp(x) ≤ x + 3 log (1 + x) + 11` for `x ≥ 0`: with the lower bound
`one_add_add_log_le_calibrationExp`, `𝒞^exp(x) = x + O(log (1 + x))`. -/
theorem calibrationExp_le_add_three_mul_log_add {x : ℝ} (hx : 0 ≤ x) :
    calibrationExp x ≤ x + 3 * log (1 + x) + 11 := by
  set u₁ := subLogInv (1 + x)
  set L := log (π ^ 2 / 3)
  have hL1 := one_le_log_pi_sq_div_three
  have hL2 := log_pi_sq_div_three_le_two
  have hx1 : 0 < 1 + x := by linarith
  have hlogx : 0 ≤ log (1 + x) := log_nonneg (by linarith)
  have hlog2 := log_two_lt_d9
  norm_num at hlog2
  have hu₁1 : 1 ≤ u₁ := one_le_subLogInv _
  have hY : 1 ≤ (u₁ + L) / 2 := by linarith
  -- `u₁ ≤ 1 + x + log 2 + log (1 + x)`, so `u₁ + L ≤ 4 (1 + x)`
  have hu₁ := Real.subLogInv_le_add_log_two_mul (by linarith : (1 : ℝ) ≤ 1 + x)
  rw [log_mul two_ne_zero hx1.ne'] at hu₁
  have hlogx' : log (1 + x) ≤ x := by linarith [log_le_sub_one_of_pos hx1]
  have h4 : log (2 * ((u₁ + L) / 2)) ≤ 2 * log 2 + log (1 + x) := by
    have h := log_le_log (by linarith) (by linarith : 2 * ((u₁ + L) / 2) ≤ 2 ^ 2 * (1 + x))
    rwa [log_mul (by norm_num) hx1.ne', log_pow, Nat.cast_ofNat] at h
  -- both branches of `minMulSubLogLog_le_max` are at most
  -- `(u₁ + L) / 2 + 2 log 2 + log (1 + x) + 2`
  have hl32 : 2 / 5 ≤ log (3 / 2) := by
    have := le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at this ⊢
    linarith
  have h32 : 3 / 2 / log (3 / 2) ≤ 3 / 2 / (2 / 5) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl32
  have hmax : max (subLogInv ((u₁ + L) / 2) + 2) (3 / 2 / log (3 / 2)) ≤
      (u₁ + L) / 2 + 2 * log 2 + log (1 + x) + 2 :=
    max_le (by linarith [Real.subLogInv_le_add_log_two_mul hY])
      (by norm_num at h32 ⊢; linarith [log_two_gt_d9])
  have h := minMulSubLogLog_le_max (z := 3 / 2) (by norm_num) ((u₁ + L) / 2)
  rw [calibrationExp_eq]
  linarith

end LMLExplore
