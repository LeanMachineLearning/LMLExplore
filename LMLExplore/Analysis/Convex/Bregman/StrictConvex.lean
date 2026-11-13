/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
public import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Bregman divergences of strictly convex functions

The Bregman divergence `D_f(y, x) = f y - f x - g (y - x)` of a function `f` that is strictly
convex on a set `s`, at a subgradient `g` of `f` on `s` at `x ∈ s`, is positive at every point
`y ∈ s` other than `x`. This is the strict form of the nonnegativity that defines subgradients.

In finite dimension, combined with continuity and compactness, this gives a positive lower bound
for `D_f(·, x)` on a small sphere around an interior point `x`, and then, by convexity, a linear
lower bound `c ‖y - x‖ ≤ D_f(y, x)` outside that sphere. This growth bound gives the
differentiability of the conjugate in `LMLExplore.Analysis.Convex.Conjugate`.

## Main statements

* `StrictConvexOn.bregDiv_pos`: for `f` strictly convex on `s`, a subgradient `g` at `x ∈ s` and
  `y ∈ s` with `y ≠ x`, `0 < D_f(y, x)`.
* `StrictConvexOn.exists_pos_mul_norm_le_bregDiv`: for `f` convex on `s` and strictly convex on
  its interior in finite dimension, a subgradient `g` at an interior point `x`, and a sphere of
  radius `ρ > 0` around `x` inside the interior of `s`, `D_f(y, x)` grows at least linearly in
  `‖y - x‖` for `y ∈ s` outside the open ball of radius `ρ`.
-/

public section

open Metric

/-- The Bregman divergence of a strictly convex function at a subgradient is positive away from
the base point: if `g` is a subgradient of `f` on `s` at `x ∈ s`, then `D_f(y, x) > 0` for every
`y ∈ s` other than `x`. -/
theorem StrictConvexOn.bregDiv_pos {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] {s : Set E} {f : E → ℝ} {g : E →L[ℝ] ℝ} {x y : E}
    (hf : StrictConvexOn ℝ s f) (hg : HasSubgradientWithinAt f g s x) (hx : x ∈ s) (hy : y ∈ s)
    (hyx : y ≠ x) :
    0 < bregDiv f y x g := by
  -- Compare the divergence at `y` with the divergence at the midpoint of `x` and `y`.
  have hm := hg _ (hf.1 hx hy one_half_pos.le one_half_pos.le (add_halves 1))
  have hlt := hf.2 hx hy hyx.symm one_half_pos one_half_pos (add_halves 1)
  have h_eq : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y - x = (1 / 2 : ℝ) • (y - x) := by module
  simp only [bregDiv, h_eq, map_smul, smul_eq_mul] at hm hlt ⊢
  linarith

/-- **Linear growth of the Bregman divergence of a strictly convex function**: let `f` be convex
on `s` and strictly convex on the interior of `s` in finite dimension, `g` a subgradient of `f` on
`s` at an interior point `x`, and `ρ > 0` such that the sphere of radius `ρ` around `x` lies in the
interior of `s`. Then there is `c > 0` with `c ‖y - x‖ ≤ D_f(y, x)` for every `y ∈ s` with
`ρ ≤ ‖y - x‖`. The divergence is continuous and positive (`StrictConvexOn.bregDiv_pos`) on the
compact sphere, hence bounded below there, and convexity along the segment from `x` to `y` turns
this into linear growth. -/
theorem StrictConvexOn.exists_pos_mul_norm_le_bregDiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {s : Set E} {f : E → ℝ} {g : E →L[ℝ] ℝ} {x : E}
    {ρ : ℝ} (hfs : StrictConvexOn ℝ (interior s) f) (hf : ConvexOn ℝ s f) (hx : x ∈ interior s)
    (hg : HasSubgradientWithinAt f g s x) (hρ : 0 < ρ) (hsphere : sphere x ρ ⊆ interior s) :
    ∃ c > 0, ∀ y ∈ s, ρ ≤ ‖y - x‖ → c * ‖y - x‖ ≤ bregDiv f y x g := by
  -- The divergence `D_f(·, x)` is continuous and positive on the sphere of radius `ρ`, so it is
  -- bounded below there by some `c > 0`.
  have hcont : ContinuousOn (fun w ↦ bregDiv f w x g) (sphere x ρ) := by
    simp only [bregDiv]
    exact ((hf.continuousOn_interior.mono hsphere).sub continuousOn_const).sub
      (g.continuous.comp_continuousOn (continuousOn_id.sub continuousOn_const))
  obtain ⟨c, hc, hcφ⟩ := (isCompact_sphere x ρ).exists_forall_le' hcont fun w hw ↦
    hfs.bregDiv_pos (hg.mono interior_subset) hx (hsphere hw) (ne_of_mem_sphere hw hρ.ne')
  refine ⟨c / ρ, div_pos hc hρ, fun y hy hyx ↦ ?_⟩
  -- Convexity along the segment from `x` to `y` through the sphere gives
  -- `D_f(y, x) ≥ c ‖y - x‖ / ρ`.
  have hpos : 0 < ‖y - x‖ := hρ.trans_le hyx
  have ht0 : 0 < ρ / ‖y - x‖ := div_pos hρ hpos
  have hw : x + (ρ / ‖y - x‖) • (y - x) ∈ sphere x ρ := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le,
      div_mul_cancel₀ _ hpos.ne']
  have hslope := hf.bregDiv_slope_le (interior_subset hx) hy g ht0 ((div_le_one hpos).2 hyx)
  rw [smul_eq_mul, inv_div] at hslope
  rw [div_mul_comm]
  exact (mul_le_mul_of_nonneg_left (hcφ _ hw) (by positivity)).trans hslope
