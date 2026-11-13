/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Convex.Strong

/-!
# The Euclidean potential

On a real inner product space `E`, the Euclidean potential `b ↦ ‖b‖ ^ 2 / 2` has derivative
`⟪x, ·⟫` at `x`, is `1`-strongly convex, and its Bregman divergence is half the squared distance.
With this potential, mirror descent is projected gradient descent.

## Main statements

* `LMLExplore.hasFDerivAt_norm_sq_div_two`: the derivative of `‖b‖ ^ 2 / 2` at `x` is `⟪x, ·⟫`.
* `LMLExplore.bregDiv_norm_sq_div_two`: the Bregman divergence of `‖b‖ ^ 2 / 2` is
  `D(x, y) = ‖x - y‖ ^ 2 / 2`.
* `LMLExplore.strongConvexOn_norm_sq_div_two`: `‖b‖ ^ 2 / 2` is `1`-strongly convex on every
  convex set.
-/

public section

open scoped RealInnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E}

/-- The derivative of `‖b‖ ^ 2 / 2` at `x` is `⟪x, ·⟫`. -/
theorem hasFDerivAt_norm_sq_div_two (x : E) :
    HasFDerivAt (fun b : E ↦ ‖b‖ ^ 2 / 2) (innerSL ℝ x) x := by
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (2 : ℝ)⁻¹ using 1
  · ext b
    ring
  · ext v
    simp

/-- The Bregman divergence of `‖b‖ ^ 2 / 2` is half the squared distance:
`D(x, y) = ‖x - y‖ ^ 2 / 2`, for the derivative `⟪y, ·⟫` at `y`. -/
@[simp]
theorem bregDiv_norm_sq_div_two (x y : E) :
    bregDiv (fun b : E ↦ ‖b‖ ^ 2 / 2) x y (innerSL ℝ y) = ‖x - y‖ ^ 2 / 2 := by
  simp only [bregDiv, innerSL_apply_apply, @norm_sub_sq_real, inner_sub_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm]
  ring

/-- `‖b‖ ^ 2 / 2` is `1`-strongly convex on every convex set. -/
theorem strongConvexOn_norm_sq_div_two (hK : Convex ℝ K) :
    StrongConvexOn K 1 fun b : E ↦ ‖b‖ ^ 2 / 2 := by
  refine strongConvexOn_iff_convex.mpr ?_
  convert convexOn_const (0 : ℝ) hK using 2 with b
  ring

end LMLExplore
