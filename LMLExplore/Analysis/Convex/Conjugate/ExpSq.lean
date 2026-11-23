/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.Convex.Conjugate

/-!
# The conjugate of a Gaussian-type exponential

For `α, β > 0`, the function `f θ = β * exp (θ ^ 2 / (2 * α))` on `ℝ` is the shape of the wealth
lower bounds of coin-betting algorithms, as a function of the sum of the coins: the
Krichevsky–Trofimov bettor guarantees a wealth of this order. Through the regret–reward duality
(`LMLExplore.OnlineLearning.sum_apply_sub_le_fenchelConjugate`), its Fenchel conjugate bounds the
regret, so the conjugate is what turns a wealth guarantee into a parameter-free regret bound.

This file bounds that conjugate [Ora, Lemma 13.6]:
`f⋆ u ≤ |u| * √(α * log (1 + α * u ^ 2 / β ^ 2)) - β`. The conjugate is
`TauCeti.fenchelConjugate` for the pairing `(θ, u) ↦ θ * u` of `ℝ` with itself
(`LinearMap.mul ℝ ℝ`).

[Ora] computes the conjugate exactly with the Lambert function and then bounds it. The bound is
proved here directly. With `s = α * u ^ 2 / β ^ 2` and `a = √(α * log (1 + s))`:
* for `|θ| ≤ a`, the linear part `θ * u` is at most `a * |u|` and `f θ ≥ β`;
* for `|θ| > a`, `f` lies above its tangent at `a`, whose slope `β * √(1 + s) * a / α` is at least
  `|u|` because `(1 + s) * log (1 + s) ≥ s`.

## Main statements

* `Real.mul_sub_mul_exp_sq_div_le`: the bound on `θ * u - β * exp (θ ^ 2 / (2 * α))`.
* `LMLExplore.fenchelConjugate_mul_exp_sq_div_le`: the bound on the conjugate [Ora, Lemma 13.6].

## References

* F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Lemma 13.6 [Ora].
-/

public section

open Real

/-- For `α, β > 0` and all real `θ` and `u`,
`θ * u - β * exp (θ ^ 2 / (2 * α)) ≤ |u| * √(α * log (1 + α * u ^ 2 / β ^ 2)) - β`. This bounds
the Fenchel conjugate of `β * exp (· ^ 2 / (2 * α))` without the Lambert function
(`LMLExplore.fenchelConjugate_mul_exp_sq_div_le`). -/
theorem Real.mul_sub_mul_exp_sq_div_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (θ u : ℝ) :
    θ * u - β * exp (θ ^ 2 / (2 * α)) ≤ |u| * √(α * log (1 + α * u ^ 2 / β ^ 2)) - β := by
  set s := α * u ^ 2 / β ^ 2 with hs_def
  set a := √(α * log (1 + s)) with ha_def
  have hs : 0 ≤ s := by positivity
  have ha : 0 ≤ a := sqrt_nonneg _
  have ha2 : a ^ 2 = α * log (1 + s) := sq_sqrt (mul_nonneg hα.le (log_nonneg (by linarith)))
  set q := exp (a ^ 2 / (2 * α)) with hq_def
  have hq : 1 ≤ q := one_le_exp (by positivity)
  have hq2 : q ^ 2 = 1 + s := by
    rw [hq_def, ← exp_natCast_mul, ha2, ← exp_log (show 0 < 1 + s by linarith)]
    congr 1
    field_simp
    norm_num
  -- The slope `β * q * a / α` of `β * exp (· ^ 2 / (2 * α))` at `a` is at least `|u|`, since
  -- `s ≤ (1 + s) * log (1 + s)`.
  have hslope : |u| ≤ β * q * a / α := by
    have hkey : s ≤ (1 + s) * log (1 + s) := by
      have h := one_sub_inv_le_log_of_pos (x := 1 + s) (by linarith)
      have h1s : (1 + s) * (1 - (1 + s)⁻¹) = s := by field_simp; ring
      nlinarith
    have hu2 : u ^ 2 = s * β ^ 2 / α := by rw [hs_def]; field_simp
    refine (pow_le_pow_iff_left₀ (abs_nonneg u) (by positivity) two_ne_zero).1 ?_
    have hβα : 0 ≤ β ^ 2 * α := by positivity
    simp only [sq_abs, hu2, div_pow, mul_pow, hq2, ha2]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hkey hβα]
  have hθu : θ * u ≤ |θ| * |u| := by rw [← abs_mul]; exact le_abs_self _
  have hθ2 : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
  rcases le_or_gt |θ| a with h | h
  · -- Near the origin, the linear part is at most `a * |u|` and the exponential at least `1`.
    have h1 : 1 ≤ exp (θ ^ 2 / (2 * α)) := one_le_exp (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right h (abs_nonneg u)]
  · -- Beyond `a`, the exponential lies above its tangent at `a`, of slope at least `|u|`.
    have hexp : q * (1 + a * (|θ| - a) / α) ≤ exp (θ ^ 2 / (2 * α)) := by
      have hsplit : θ ^ 2 / (2 * α) = a ^ 2 / (2 * α) + (θ ^ 2 - a ^ 2) / (2 * α) := by ring
      rw [hsplit, exp_add, ← hq_def]
      have h1 : a * (|θ| - a) / α ≤ (θ ^ 2 - a ^ 2) / (2 * α) := by
        rw [div_le_div_iff₀ hα (by positivity), hθ2]
        nlinarith [sq_nonneg (|θ| - a)]
      have h2 := add_one_le_exp ((θ ^ 2 - a ^ 2) / (2 * α))
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hpos : 0 ≤ |θ| - a := by linarith
    have h1 : |u| * (|θ| - a) ≤ β * q * a / α * (|θ| - a) :=
      mul_le_mul_of_nonneg_right hslope hpos
    have h2 : β * q * (1 + a * (|θ| - a) / α) = β * q + β * q * a / α * (|θ| - a) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hexp hβ.le]

namespace LMLExplore

open TauCeti

/-- **The conjugate of a Gaussian-type exponential** [Ora, Lemma 13.6]: for `α, β > 0`, the
Fenchel conjugate of `θ ↦ β * exp (θ ^ 2 / (2 * α))` on `ℝ`, for the pairing `(θ, u) ↦ θ * u`,
is at most `|u| * √(α * log (1 + α * u ^ 2 / β ^ 2)) - β`. -/
theorem fenchelConjugate_mul_exp_sq_div_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (u : ℝ) :
    fenchelConjugate (LinearMap.mul ℝ ℝ) (fun θ ↦ ((β * exp (θ ^ 2 / (2 * α)) : ℝ) : EReal)) u ≤
      ((|u| * √(α * log (1 + α * u ^ 2 / β ^ 2)) - β : ℝ) : EReal) :=
  fenchelConjugate_le _ fun θ ↦ by
    rw [LinearMap.mul_apply', ← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact Real.mul_sub_mul_exp_sq_div_le hα hβ θ u

end LMLExplore
