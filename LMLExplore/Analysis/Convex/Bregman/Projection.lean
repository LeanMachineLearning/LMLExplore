/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Bregman divergences at constrained minimizers

The **Bregman projection** of a point `y` onto a set `K` for a function `F`, with a linear map `J`
in the role of the derivative of `F` at `y`, is a minimizer over `K` of the Bregman divergence
`z ↦ D_F(z, y) = F z - F y - J (z - y)` [LS, Section 26.6]. For `F z = ‖z‖ ^ 2 / 2` on an inner
product space it is the Euclidean projection. Mirror descent plays the Bregman projection of an
unconstrained step onto the constraint set, and follow the regularized leader plays a minimizer
of a linear function plus a regularizer.

At a minimizer `a` over `K` of `c ↦ L c + F c`, for a linear `L` and a function `F`
differentiable within `K` at `a`, the first-order optimality condition bounds the increase of the
function towards every `b` with `[a, b] ⊆ K` from below by the Bregman divergence `D_F(b, a)`.
For a Bregman projection this is the **generalized Pythagorean inequality**
[LS, Exercise 26.13]: if `z` is a Bregman projection of `y` onto a convex set `K` and `F` is
differentiable within `K` at `z`, then `D_F(x, z) + D_F(z, y) ≤ D_F(x, y)` for every `x ∈ K`.
Neither the convexity of `F` nor a derivative of `F` at `y` is needed: `J` is any linear map.
The existence, uniqueness and interiority of Bregman projections for Legendre functions are in
`LMLExplore.Analysis.Convex.Legendre`.

## Main statements

* `LMLExplore.bregDiv_le_sub_of_isMinOn`: at a minimizer `a` of `c ↦ L c + F c` over `K`, with
  `[a, b] ⊆ K`, `D_F(b, a) ≤ L b + F b - (L a + F a)`.
* `LMLExplore.bregDiv_le_sub_of_isMinOn_self`: its case `L = 0`, `D_F(b, a) ≤ F b - F a`.
* `LMLExplore.bregDiv_add_bregDiv_le_of_isMinOn`: [LS, Exercise 26.13 (a)]. The generalized
  Pythagorean inequality `D_F(x, z) + D_F(z, y) ≤ D_F(x, y)` for a Bregman projection `z` of `y`
  onto a convex set `K` and `x ∈ K`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.6 and Exercise 26.13.
-/

public section

open ContinuousLinearMap

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- Let `a` minimize over `K` the function `c ↦ L c + F c`, where `L` is a continuous linear
functional and `F` has derivative `F'` within `K` at `a`. If the segment from `a` to `b` lies in
`K`, then this function increases from `a` to `b` by at least the Bregman divergence
`D_F(b, a)`. -/
lemma bregDiv_le_sub_of_isMinOn {F : E → ℝ} {L F' : E →L[ℝ] ℝ} {a b : E}
    (h_seg : segment ℝ a b ⊆ K) (ha : IsMinOn (fun c ↦ L c + F c) K a)
    (hF' : HasFDerivWithinAt F F' K a) :
    bregDiv F b a F' ≤ L b + F b - (L a + F a) := by
  -- the function has derivative `L + F'` within `K` at `a`, nonnegative towards `b`
  have h_seg' : segment ℝ a (a + (b - a)) ⊆ K := by rwa [add_sub_cancel]
  have h_nonneg := ha.isLocalMinOn.hasFDerivWithinAt_nonneg (L.hasFDerivWithinAt.add hF')
    (mem_posTangentConeAt_of_segment_subset h_seg')
  simp only [add_apply, map_sub] at h_nonneg
  simp only [bregDiv, map_sub]
  linarith

/-- Let `a` minimize `F` over `K`, where `F` has derivative `F'` within `K` at `a`. If the
segment from `a` to `b` lies in `K`, then `D_F(b, a) ≤ F b - F a`. -/
lemma bregDiv_le_sub_of_isMinOn_self {F : E → ℝ} {F' : E →L[ℝ] ℝ} {a b : E}
    (h_seg : segment ℝ a b ⊆ K) (ha : IsMinOn F K a) (hF' : HasFDerivWithinAt F F' K a) :
    bregDiv F b a F' ≤ F b - F a := by
  simpa using bregDiv_le_sub_of_isMinOn (L := 0) h_seg (by simpa using ha) hF'

/-- **Generalized Pythagorean inequality** [LS, Exercise 26.13 (a)]. Let `z` minimize the Bregman
divergence `D_F(·, y)`, for any linear map `J`, over a convex set `K`, and let `F` have derivative
`J_z` within `K` at `z`. Then `D_F(x, z) + D_F(z, y) ≤ D_F(x, y)` for every `x ∈ K`. -/
theorem bregDiv_add_bregDiv_le_of_isMinOn {F : E → ℝ} {J J_z : E →L[ℝ] ℝ} {x y z : E}
    (hK : Convex ℝ K) (hx : x ∈ K) (hz : z ∈ K) (hmin : IsMinOn (fun w ↦ bregDiv F w y J) K z)
    (hJ_z : HasFDerivWithinAt F J_z K z) :
    bregDiv F x z J_z + bregDiv F z y J ≤ bregDiv F x y J := by
  -- up to a constant, `D_F(·, y)` is `w ↦ -J w + F w`
  have hmin' : IsMinOn (fun w ↦ (-J) w + F w) K z := isMinOn_iff.2 fun w hw ↦ by
    have := isMinOn_iff.1 hmin w hw
    simp only [bregDiv, map_sub, neg_apply] at this ⊢
    linarith
  have := bregDiv_le_sub_of_isMinOn (hK.segment_subset hz hx) hmin' hJ_z
  simp only [bregDiv, map_sub, neg_apply] at this ⊢
  linarith

end LMLExplore
