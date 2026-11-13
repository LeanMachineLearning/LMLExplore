/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Bregman divergences of strictly convex functions

The Bregman divergence `D_f(y, x) = f y - f x - g (y - x)` of a function `f` that is strictly
convex on a set `s`, at a subgradient `g` of `f` on `s` at `x ∈ s`, is positive at every point
`y ∈ s` other than `x`. This is the strict form of the nonnegativity that defines subgradients.
It bounds the divergence below by a positive constant on compact sets avoiding `x`, which gives
the differentiability of the conjugate in `LMLExplore.Analysis.Convex.Conjugate`.

## Main statements

* `StrictConvexOn.bregDiv_pos`: for `f` strictly convex on `s`, a subgradient `g` at `x ∈ s` and
  `y ∈ s` with `y ≠ x`, `0 < D_f(y, x)`.
-/

public section

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
