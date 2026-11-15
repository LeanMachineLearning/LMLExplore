/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

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
  set g := fun y ↦ f y - (f a + f' a * (y - a) + c / 2 * (y - a) ^ 2) with hg_def
  set g' := fun y ↦ f' y - (f' a + c * (y - a)) with hg'_def
  have h1 (y : ℝ) : HasDerivAt (fun y ↦ f a + f' a * (y - a) + c / 2 * (y - a) ^ 2)
      (f' a + c * (y - a)) y := by
    have h := (hasDerivAt_id y).sub_const a
    exact (((h.const_mul (f' a)).const_add (f a)).add ((h.pow 2).const_mul (c / 2))).congr_deriv
      (by simp only [id, Nat.cast_ofNat]; ring)
  have hg (y : ℝ) (hy : y ∈ I) : HasDerivAt g (g' y) y := (hf y hy).sub (h1 y)
  have hg' (y : ℝ) (hy : y ∈ I) : HasDerivAt g' (f'' y - c) y :=
    (hf' y hy).sub (((((hasDerivAt_id y).sub_const a).const_mul c).const_add (f' a)).congr_deriv
      (by simp))
  have hmono : MonotoneOn g' I :=
    monotoneOn_of_hasDerivWithinAt_nonneg hI
      (fun y hy ↦ (hg' y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hg' y (interior_subset hy)).hasDerivWithinAt)
      fun y hy ↦ sub_nonneg.2 (hc y (interior_subset hy))
  have hga : g a = 0 := by simp [g]
  have hg'a : g' a = 0 := by simp [g']
  suffices 0 ≤ g x by simp only [g] at this; linarith
  rcases le_total a x with hax | hxa
  · have h : MonotoneOn g (I ∩ Set.Ici a) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (hI.inter (convex_Ici a))
        (fun y hy ↦ (hg y hy.1).continuousAt.continuousWithinAt)
        (fun y hy ↦ (hg y (interior_subset hy).1).hasDerivWithinAt)
        fun y hy ↦ by
          have hy' := interior_subset hy
          rw [← hg'a]
          exact hmono ha hy'.1 hy'.2
    rw [← hga]
    exact h ⟨ha, Set.mem_Ici.2 le_rfl⟩ ⟨hx, hax⟩ hax
  · have h : AntitoneOn g (I ∩ Set.Iic a) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (hI.inter (convex_Iic a))
        (fun y hy ↦ (hg y hy.1).continuousAt.continuousWithinAt)
        (fun y hy ↦ (hg y (interior_subset hy).1).hasDerivWithinAt)
        fun y hy ↦ by
          have hy' := interior_subset hy
          rw [← hg'a]
          exact hmono hy'.1 ha hy'.2
    rw [← hga]
    exact h ⟨hx, hxa⟩ ⟨ha, Set.mem_Iic.2 le_rfl⟩ hxa

end LMLExplore
