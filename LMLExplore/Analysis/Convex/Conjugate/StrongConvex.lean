/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Conjugate.Basic
public import LMLExplore.Analysis.Convex.Smooth
public import LMLExplore.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Conjugates of strongly convex functions are smooth

On a real normed space `E`, the conjugate `F⋆ w = ⨆ x ∈ D, (w x - F x)` of a function
`F : E → ℝ` on a set `D` (`LMLExplore.fenchelConjugateOn`) lives on the dual `E →L[ℝ] ℝ`. Strong
convexity of `F` and smoothness of `F⋆` are dual [Ora, Example 6.19, Theorem 6.26]:

* the conjugate of `s / 2 * ‖·‖ ^ 2` is `1 / (2 * s) * ‖·‖ ^ 2` on the dual, for `s > 0`;
* if `F` is `m`-strongly convex on `D` with `m > 0`, and `u` is a subgradient of `F` within `D`
  at `x ∈ D` (that is, `x` maximizes `u - F` on `D`), then `F⋆` is finite everywhere and lies
  between its tangent `w ↦ F⋆ u + (w - u) x` and that tangent plus `‖w - u‖ ^ 2 / (2 * m)`. So
  `F⋆` is differentiable at `u` with derivative the evaluation at `x`, the image of `x` in the
  bidual, and this maximizer `x` is unique;
* if moreover every functional is a subgradient of `F` within `D` at some point of `D`, then,
  since the maximizers are `1 / m`-Lipschitz in the functional
  (`StrongConvexOn.mul_norm_sub_le_norm_sub_of_isMinOn_add`), `F⋆` is `1 / m`-smooth on the whole
  dual (`LMLExplore.SmoothOn`);
* in finite dimension, every functional is such a subgradient as soon as `D` is closed and
  nonempty and `F` is lower semicontinuous on `D`, since `F - u` then has a minimizer on `D`
  (`StrongConvexOn.exists_isMinOn_add_continuousLinearMap`).

Only the existence of the maximizers uses finite dimension: the bounds hold in every normed
space, and `F` need not be differentiable or bounded.

## Main statements

* `LMLExplore.fenchelConjugate_mul_norm_sq`: [Ora, Example 6.19] the conjugate of
  `s / 2 * ‖·‖ ^ 2`.
* `StrongConvexOn.bregDiv_toReal_fenchelConjugateOn_le`: the conjugate of an `m`-strongly convex
  function exceeds its tangent at a subgradient by at most `‖w - u‖ ^ 2 / (2 * m)`.
* `StrongConvexOn.hasFDerivAt_toReal_fenchelConjugateOn`: at a subgradient `u` of `F` at `x`, the
  conjugate has derivative the evaluation at `x`.
* `StrongConvexOn.eq_of_hasSubgradientWithinAt`: the maximizer of `u - F` on `D` is unique.
* `StrongConvexOn.exists_hasSubgradientWithinAt`: in finite dimension, it exists for `D` closed
  and nonempty and `F` lower semicontinuous on `D`.
* `StrongConvexOn.smoothOn_toReal_fenchelConjugateOn`: [Ora, Theorem 6.26] the conjugate is
  `1 / m`-smooth when every functional is a subgradient at some point of `D`.
* `StrongConvexOn.smoothOn_toReal_fenchelConjugateOn_of_isClosed`: [Ora, Theorem 6.26] the
  conjugate is `1 / m`-smooth in finite dimension, for `D` closed and nonempty and `F` lower
  semicontinuous on `D`.

## References

* F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213v10, Example 6.19 and
  Theorem 6.26 [Ora].
-/

public section

open Set Metric Filter TauCeti LMLExplore
open scoped Topology

section TopologicalSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The conjugate of `F` on the whole space is Tau Ceti's `fenchelConjugate` of `F`, for the
pairing of `E` with its dual. -/
theorem LMLExplore.fenchelConjugateOn_univ (F : E → ℝ) (u : E →L[ℝ] ℝ) :
    fenchelConjugateOn F univ u =
      fenchelConjugate (topDualPairing ℝ E).flip (fun x ↦ (F x : EReal)) u := by
  classical
  simp [fenchelConjugateOn_eq_fenchelConjugate]

end TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The conjugate of a squared norm** [Ora, Example 6.19]: for `s > 0`, the conjugate of
`s / 2 * ‖·‖ ^ 2` is `1 / (2 * s) * ‖·‖ ^ 2` on the dual, for the dual norm. The space `E` need not
be complete or finite-dimensional, so the dual norm need not be attained. -/
theorem LMLExplore.fenchelConjugate_mul_norm_sq {s : ℝ} (hs : 0 < s) (u : E →L[ℝ] ℝ) :
    fenchelConjugate (topDualPairing ℝ E).flip (fun x ↦ ((s / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) u =
      ((1 / (2 * s) * ‖u‖ ^ 2 : ℝ) : EReal) := by
  rw [one_div_mul_eq_div]
  refine le_antisymm (fenchelConjugate_le _ fun x ↦ ?_)
    (EReal.ge_of_forall_gt_iff_ge.1 fun c hc ↦ ?_)
  · rw [LinearMap.flip_apply, topDualPairing_apply, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    simpa using apply_sub_sub_mul_norm_sq_le hs u x 0
  -- Along `t • x` with `t = ‖u‖ / s` and `u x` close to `‖u‖ ≥ ‖x‖`, the value
  -- `‖u‖ r / s - ‖u‖ ^ 2 / (2 * s)` tends to `‖u‖ ^ 2 / (2 * s)` as `r` tends to `‖u‖`.
  rw [EReal.coe_lt_coe_iff] at hc
  have hlim : Tendsto (fun r ↦ ‖u‖ * r / s - ‖u‖ ^ 2 / (2 * s)) (𝓝[<] ‖u‖)
      (𝓝 (‖u‖ ^ 2 / (2 * s))) := by
    have hcont : Continuous fun r : ℝ ↦ ‖u‖ * r / s - ‖u‖ ^ 2 / (2 * s) := by fun_prop
    convert (hcont.tendsto ‖u‖).mono_left nhdsWithin_le_nhds using 2
    field_simp
    ring
  obtain ⟨r, hcr, hr⟩ := ((hlim.eventually (lt_mem_nhds hc)).and self_mem_nhdsWithin).exists
  obtain ⟨x, hx1, hrx⟩ := u.exists_lt_apply_of_lt_opNorm hr
  obtain ⟨x', hx'1, hrx'⟩ : ∃ x' : E, ‖x'‖ < 1 ∧ r < u x' := by
    rw [Real.norm_eq_abs] at hrx
    rcases abs_choice (u x) with h | h
    · exact ⟨x, hx1, h ▸ hrx⟩
    · exact ⟨-x, by rwa [norm_neg], by rwa [map_neg, ← h]⟩
  set t := ‖u‖ / s with ht_def
  have ht : 0 ≤ t := by positivity
  have key := sub_le_fenchelConjugate (topDualPairing ℝ E).flip
    (fun x ↦ ((s / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) (t • x') u
  rw [LinearMap.flip_apply, topDualPairing_apply, ← EReal.coe_sub] at key
  refine le_trans ?_ key
  rw [EReal.coe_le_coe_iff, map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg ht]
  have h1 : t * r ≤ t * u x' := mul_le_mul_of_nonneg_left hrx'.le ht
  have h2 : (t * ‖x'‖) ^ 2 ≤ t ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg t) (pow_le_one₀ (norm_nonneg _) hx'1.le)
  have h3 : t * r - s / 2 * t ^ 2 = ‖u‖ * r / s - ‖u‖ ^ 2 / (2 * s) := by
    rw [ht_def]
    field_simp
  nlinarith

namespace StrongConvexOn

variable {F : E → ℝ} {D : Set E} {m : ℝ} {x y : E} {u : E →L[ℝ] ℝ}

/-- **The conjugate of a strongly convex function lies below a paraboloid.** If `F` is
`m`-strongly convex on `D` with `m > 0`, and `u` is a subgradient of `F` within `D` at `x ∈ D`,
then `F⋆ w ≤ u x - F x + (w - u) x + ‖w - u‖ ^ 2 / (2 * m)` for every `w`, where
`u x - F x = F⋆ u`. -/
theorem fenchelConjugateOn_le_of_hasSubgradientWithinAt (hf : StrongConvexOn D m F)
    (hm : 0 < m) (hx : x ∈ D) (hu : HasSubgradientWithinAt F u D x) (w : E →L[ℝ] ℝ) :
    fenchelConjugateOn F D w ≤ ((u x - F x + (w - u) x + ‖w - u‖ ^ 2 / (2 * m) : ℝ) : EReal) := by
  refine fenchelConjugateOn_le_coe_iff.2 fun z hz ↦ ?_
  have h1 := hf.add_add_le_of_hasSubgradientWithinAt hx hz hu
  have h2 := apply_sub_sub_mul_norm_sq_le hm (w - u) z x
  simp only [map_sub, sub_apply] at h1 h2 ⊢
  linarith

/-- The conjugate of an `m`-strongly convex function with `m > 0` that has a subgradient at some
point of `D` is finite everywhere. -/
theorem fenchelConjugateOn_ne_top (hf : StrongConvexOn D m F) (hm : 0 < m) (hx : x ∈ D)
    (hu : HasSubgradientWithinAt F u D x) (w : E →L[ℝ] ℝ) :
    fenchelConjugateOn F D w ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (hf.fenchelConjugateOn_le_of_hasSubgradientWithinAt hm hx hu w)

/-- **The tangent of the conjugate.** If `F` is `m`-strongly convex on `D` with `m > 0`, and `u`
is a subgradient of `F` within `D` at `x ∈ D`, then the evaluation at `x` is a subgradient of the
conjugate at `u`: `F⋆ u + (w - u) x ≤ F⋆ w` for every `w`. -/
theorem hasSubgradientWithinAt_toReal_fenchelConjugateOn (hf : StrongConvexOn D m F)
    (hm : 0 < m) (hx : x ∈ D) (hu : HasSubgradientWithinAt F u D x) :
    HasSubgradientWithinAt (fun w ↦ (fenchelConjugateOn F D w).toReal)
      (ContinuousLinearMap.apply ℝ ℝ x) univ u := by
  intro w _
  have := sub_le_toReal_fenchelConjugateOn hx (hf.fenchelConjugateOn_ne_top hm hx hu w)
  simp only [bregDiv, toReal_fenchelConjugateOn_of_hasSubgradientWithinAt hu hx,
    ContinuousLinearMap.apply_apply, sub_apply]
  linarith

/-- **The conjugate of a strongly convex function is smooth at a subgradient.** If `F` is
`m`-strongly convex on `D` with `m > 0`, and `u` is a subgradient of `F` within `D` at `x ∈ D`,
then the Bregman divergence of the conjugate at `u`, with the evaluation at `x` as linear part,
is at most `‖w - u‖ ^ 2 / (2 * m)`: `F⋆ w ≤ F⋆ u + (w - u) x + ‖w - u‖ ^ 2 / (2 * m)`. -/
theorem bregDiv_toReal_fenchelConjugateOn_le (hf : StrongConvexOn D m F) (hm : 0 < m)
    (hx : x ∈ D) (hu : HasSubgradientWithinAt F u D x) (w : E →L[ℝ] ℝ) :
    bregDiv (fun w ↦ (fenchelConjugateOn F D w).toReal) w u (ContinuousLinearMap.apply ℝ ℝ x) ≤
      ‖w - u‖ ^ 2 / (2 * m) := by
  have h := hf.fenchelConjugateOn_le_of_hasSubgradientWithinAt hm hx hu w
  rw [← EReal.coe_toReal (hf.fenchelConjugateOn_ne_top hm hx hu w)
    (fenchelConjugateOn_ne_bot hx w), EReal.coe_le_coe_iff] at h
  simp only [bregDiv, toReal_fenchelConjugateOn_of_hasSubgradientWithinAt hu hx,
    ContinuousLinearMap.apply_apply]
  linarith

/-- **The gradient of the conjugate of a strongly convex function** [Ora, Theorem 6.26]. If `F`
is `m`-strongly convex on `D` with `m > 0`, and `u` is a subgradient of `F` within `D` at
`x ∈ D`, that is, `x` maximizes `u - F` on `D`, then the conjugate is differentiable at `u` with
derivative the evaluation at `x`. -/
theorem hasFDerivAt_toReal_fenchelConjugateOn (hf : StrongConvexOn D m F) (hm : 0 < m)
    (hx : x ∈ D) (hu : HasSubgradientWithinAt F u D x) :
    HasFDerivAt (fun w ↦ (fenchelConjugateOn F D w).toReal) (ContinuousLinearMap.apply ℝ ℝ x)
      u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [closedBall_mem_nhds (0 : E →L[ℝ] ℝ) (by positivity : 0 < 2 * m * ε)] with h hh
  rw [mem_closedBall_zero_iff] at hh
  have hup := hf.bregDiv_toReal_fenchelConjugateOn_le hm hx hu (u + h)
  have hlow := hf.hasSubgradientWithinAt_toReal_fenchelConjugateOn hm hx hu (u + h) (mem_univ _)
  simp only [bregDiv, add_sub_cancel_left, ContinuousLinearMap.apply_apply] at hup hlow
  have hsq : ‖h‖ ^ 2 / (2 * m) ≤ ε * ‖h‖ := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  rw [ContinuousLinearMap.apply_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- **The maximizer of `u - F` is unique.** If `F` is `m`-strongly convex on `D` with `m > 0`, a
functional `u` is a subgradient of `F` within `D` at most at one point of `D`. -/
theorem eq_of_hasSubgradientWithinAt (hf : StrongConvexOn D m F) (hm : 0 < m) (hx : x ∈ D)
    (hy : y ∈ D) (hux : HasSubgradientWithinAt F u D x) (huy : HasSubgradientWithinAt F u D y) :
    x = y := by
  have := hf.mul_norm_sub_sq_le_sub_apply_sub hx hy hux huy
  rw [sub_self, zero_apply] at this
  have h0 : ‖x - y‖ ^ 2 = 0 := le_antisymm (nonpos_of_mul_nonpos_right this hm) (sq_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))

/-- **Strong convexity of a function makes its conjugate smooth** [Ora, Theorem 6.26]. If `F` is
`m`-strongly convex on `D` with `m > 0`, and every functional `u` is a subgradient of `F` within
`D` at some point `x_u ∈ D`, then the conjugate is `1 / m`-smooth on the dual: it is
differentiable everywhere, with derivative at `u` the evaluation at `x_u`, and this derivative is
`1 / m`-Lipschitz. -/
theorem smoothOn_toReal_fenchelConjugateOn (hf : StrongConvexOn D m F) (hm : 0 < m)
    (hsub : ∀ u : E →L[ℝ] ℝ, ∃ x ∈ D, HasSubgradientWithinAt F u D x) :
    SmoothOn univ m⁻¹.toNNReal fun w ↦ (fenchelConjugateOn F D w).toReal := by
  choose X hXD hX using hsub
  have hderiv (u : E →L[ℝ] ℝ) := hf.hasFDerivAt_toReal_fenchelConjugateOn hm (hXD u) (hX u)
  -- `X u` minimizes `F - u` on `D`.
  have hmin (u : E →L[ℝ] ℝ) : IsMinOn (fun a ↦ F a + (-u) a) D (X u) := isMinOn_iff.2 fun y hy ↦ by
    have := hX u y hy
    simp only [bregDiv, map_sub] at this
    simp only [neg_apply]
    linarith
  rw [smoothOn_univ]
  refine ⟨fun u ↦ (hderiv u).differentiableAt, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  rw [(hderiv u).fderiv, (hderiv v).fderiv, dist_eq_norm, dist_eq_norm, ← map_sub,
    Real.coe_toNNReal _ (inv_nonneg.2 hm.le), inv_mul_eq_div, le_div_iff₀ hm]
  have hlip := hf.mul_norm_sub_le_norm_sub_of_isMinOn_add (hXD u) (hXD v) (hmin u) (hmin v)
  rw [neg_sub_neg, norm_sub_rev v u] at hlip
  calc ‖ContinuousLinearMap.apply ℝ ℝ (X u - X v)‖ * m ≤ ‖X u - X v‖ * m :=
        mul_le_mul_of_nonneg_right (NormedSpace.double_dual_bound ℝ E (X u - X v)) hm.le
    _ ≤ ‖u - v‖ := by rw [mul_comm]; exact hlip

/-- **Every functional is a subgradient of a strongly convex function**, in finite dimension: if
`F` is `m`-strongly convex with `m > 0` and lower semicontinuous on a nonempty closed set `D`,
then `u - F` attains its maximum on `D` for every functional `u`. By
`StrongConvexOn.eq_of_hasSubgradientWithinAt` the maximizer is unique. -/
theorem exists_hasSubgradientWithinAt [FiniteDimensional ℝ E] (hf : StrongConvexOn D m F)
    (hm : 0 < m) (hD : IsClosed D) (hD_ne : D.Nonempty) (hf_lsc : LowerSemicontinuousOn F D)
    (u : E →L[ℝ] ℝ) :
    ∃ x ∈ D, HasSubgradientWithinAt F u D x := by
  obtain ⟨x, hx, hmin⟩ := hf.exists_isMinOn_add_continuousLinearMap hm hD hD_ne hf_lsc (-u)
  refine ⟨x, hx, fun y hy ↦ ?_⟩
  have := isMinOn_iff.1 hmin y hy
  simp only [Pi.add_apply, neg_apply] at this
  simp only [bregDiv, map_sub]
  linarith

/-- **The duality of strong convexity and smoothness** [Ora, Theorem 6.26], in finite dimension:
the conjugate of a function that is `m`-strongly convex with `m > 0` and lower semicontinuous on a
nonempty closed set `D` is `1 / m`-smooth on the dual. Its derivative at `u` is the evaluation at
the unique maximizer of `u - F` on `D` (`StrongConvexOn.hasFDerivAt_toReal_fenchelConjugateOn`). -/
theorem smoothOn_toReal_fenchelConjugateOn_of_isClosed [FiniteDimensional ℝ E]
    (hf : StrongConvexOn D m F) (hm : 0 < m) (hD : IsClosed D) (hD_ne : D.Nonempty)
    (hf_lsc : LowerSemicontinuousOn F D) :
    SmoothOn univ m⁻¹.toNNReal fun w ↦ (fenchelConjugateOn F D w).toReal :=
  hf.smoothOn_toReal_fenchelConjugateOn hm
    (hf.exists_hasSubgradientWithinAt hm hD hD_ne hf_lsc)

end StrongConvexOn
