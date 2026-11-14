/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Comparing values of a function through the sign of its derivative

Mathlib's `monotoneOn_of_hasDerivWithinAt_nonneg` and `antitoneOn_of_hasDerivWithinAt_nonpos`
turn the sign of a derivative on an interval into monotonicity. This file packages the two-sided
form used to prove that a point is a maximum: if the derivative of `f` is nonnegative to the left
of `x₀` and nonpositive to its right, then `f x ≤ f x₀` for every `x`.

## Main statements

* `LMLExplore.apply_le_apply_of_hasDerivAt_of_nonneg_of_nonpos`: if `f` is continuous on the
  segment between `x` and `x₀` and has derivative `f' y` at each `y` strictly between them, with
  `f' ≥ 0` on `(x, x₀)` and `f' ≤ 0` on `(x₀, x)`, then `f x ≤ f x₀`.
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

end LMLExplore
