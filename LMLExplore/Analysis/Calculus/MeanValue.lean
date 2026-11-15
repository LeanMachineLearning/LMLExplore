/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv

/-!
# Comparing values of a function through the sign of its derivative

Mathlib's `monotoneOn_of_hasDerivWithinAt_nonneg` and `antitoneOn_of_hasDerivWithinAt_nonpos`
turn the sign of a derivative on an interval into monotonicity. This file packages the two-sided
form used to prove that a point is a maximum: if the derivative of `f` is nonnegative to the left
of `x₀` and nonpositive to its right, then `f x ≤ f x₀` for every `x`. It also gives the
second-order lower bound that a lower bound on the second derivative gives on a convex set.

## Main statements

* `LMLExplore.apply_le_apply_of_hasDerivAt_of_nonneg_of_nonpos`: if `f` is continuous on the
  segment between `x` and `x₀` and has derivative `f' y` at each `y` strictly between them, with
  `f' ≥ 0` on `(x, x₀)` and `f' ≤ 0` on `(x₀, x)`, then `f x ≤ f x₀`.
* `LMLExplore.add_mul_add_mul_sq_le_of_le_deriv2`: if `c ≤ f''` on a convex set `I` containing
  `a`, then `f` lies above its second-order polynomial `f a + f' a (x - a) + c / 2 (x - a) ^ 2`
  on `I`.
-/

public section

namespace LMLExplore

/-- If `f` is continuous on the segment between `x` and `x₀` and differentiable in its interior,
with a nonnegative derivative between `x` and `x₀` when `x < x₀` and a nonpositive one when
`x > x₀`, then `f x ≤ f x₀`. -/
theorem apply_le_apply_of_hasDerivAt_of_nonneg_of_nonpos {f f' : ℝ → ℝ} {x x₀ : ℝ}
    (hcont : ContinuousOn f (Set.uIcc x x₀))
    (hd : ∀ y ∈ Set.Ioo (min x x₀) (max x x₀), HasDerivAt f (f' y) y)
    (hneg : ∀ y ∈ Set.Ioo x x₀, 0 ≤ f' y) (hpos : ∀ y ∈ Set.Ioo x₀ x, f' y ≤ 0) :
    f x ≤ f x₀ := by
  rcases le_total x x₀ with h0 | h0
  · rw [Set.uIcc_of_le h0] at hcont
    rw [min_eq_left h0, max_eq_right h0] at hd
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x x₀) hcont
      (fun y hy ↦ (hd y (by rwa [interior_Icc] at hy)).hasDerivWithinAt) ?_
      ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
    rw [interior_Icc]
    exact hneg
  · rw [Set.uIcc_of_ge h0] at hcont
    rw [min_eq_right h0, max_eq_left h0] at hd
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x₀ x) hcont
      (fun y hy ↦ (hd y (by rwa [interior_Icc] at hy)).hasDerivWithinAt) ?_
      ⟨le_rfl, h0⟩ ⟨h0, le_rfl⟩ h0
    rw [interior_Icc]
    exact hpos

/-- **Second-order lower bound.** If `f` has derivative `f'` and `f'` has derivative `f''` at
every point of a convex set `I` containing `a`, and `c ≤ f''` on `I`, then
`f a + f' a * (x - a) + c / 2 * (x - a) ^ 2 ≤ f x` on `I`. -/
theorem add_mul_add_mul_sq_le_of_le_deriv2 {f f' f'' : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    {a c : ℝ} (ha : a ∈ I) (hf : ∀ x ∈ I, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ I, HasDerivAt f' (f'' x) x) (hc : ∀ x ∈ I, c ≤ f'' x) {x : ℝ} (hx : x ∈ I) :
    f a + f' a * (x - a) + c / 2 * (x - a) ^ 2 ≤ f x := by
  -- `h = f - c / 2 * (· - a) ^ 2` has second derivative `f'' - c ≥ 0`, so it is convex on `I`.
  set h := fun y ↦ f y - c / 2 * (y - a) ^ 2 with h_def
  have hh (y : ℝ) (hy : y ∈ I) : HasDerivAt h (f' y - c * (y - a)) y :=
    (hf y hy).sub (((((hasDerivAt_id y).sub_const a).pow 2).const_mul (c / 2)).congr_deriv
      (by simp only [id, Nat.cast_ofNat]; ring))
  have hh' (y : ℝ) (hy : y ∈ I) : HasDerivAt (fun y ↦ f' y - c * (y - a)) (f'' y - c) y :=
    (hf' y hy).sub ((((hasDerivAt_id y).sub_const a).const_mul c).congr_deriv (by simp))
  have hconv : ConvexOn ℝ I h :=
    convexOn_of_hasDerivWithinAt2_nonneg hI
      (fun y hy ↦ (hh y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hh y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy ↦ (hh' y (interior_subset hy)).hasDerivWithinAt)
      fun y hy ↦ sub_nonneg.2 (hc y (interior_subset hy))
  have hha : HasDerivAt h (f' a) a := by simpa using hh a ha
  rcases lt_trichotomy a x with hax | rfl | hxa
  · have := hconv.le_slope_of_hasDerivAt ha hx hax hha
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hax)] at this
    simp only [h] at this
    linarith
  · simp
  · have := hconv.slope_le_of_hasDerivAt hx ha hxa hha
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hxa)] at this
    simp only [h] at this
    nlinarith

end LMLExplore
