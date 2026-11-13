/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
public import LMLExplore.Analysis.Convex.Bregman.StrictConvex
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import TauCeti.Analysis.Convex.Subdifferential

/-!
# The conjugate of a function on a set, and its gradient at subgradients

A convex function given as `F : E → ℝ` together with its domain `D : Set E` has the
Legendre–Fenchel conjugate `F⋆ u = ⨆ x ∈ D, (u x - F x)` on the dual `E →L[ℝ] ℝ`. This file
defines it as `LMLExplore.fenchelConjugateOn F D`, identifies it with Tau Ceti's
`TauCeti.fenchelConjugate` of `F` extended by `⊤` off `D` (for the pairing `(x, u) ↦ u x` of `E`
with its dual), and relates LML's subgradients `HasSubgradientWithinAt F u D x` to Tau Ceti's
subdifferential.

The main results are the parts of the duality between a strictly convex function and its
conjugate that hold at every subgradient of an interior point [LS, Theorem 26.6]:

* the Fenchel–Young equality `F⋆ u = u x - F x` characterises the subgradients `u` of `F` at `x`;
* the Bregman divergences of `F` and of its conjugate are dual:
  `D_{F⋆}(v, u) = D_F(x, y)` for subgradients `u` at `x` and `v` at `y`, where the divergence of
  `F⋆` is taken with evaluation at `x` as the linear part at `u` (by the next item, this is the
  derivative of `F⋆` at `u` when `F` is strictly convex);
* if `F` is convex on `D` and strictly convex on the interior of `D` in finite dimension, then at
  every subgradient `u` of `F` at an interior point `x`, the conjugate is finite on a
  neighbourhood of `u` and differentiable at `u` with derivative evaluation at `x`. For a
  differentiable `F` the subgradient is `∇F(x)`, so `∇F⋆ (∇F x) = x`: the gradient of the
  conjugate inverts the gradient of `F` on the interior of the domain, and `∇F` maps that
  interior into the interior of the domain of `F⋆`.

No lower semicontinuity of `F` at the boundary of `D` is needed, and `F` need not be
differentiable. The differentiability of `F⋆` comes from a uniform growth bound: the Bregman
divergence `z ↦ D_F(z, x)` is bounded below by a positive constant on a small sphere around `x`
(strict convexity and compactness) and therefore grows linearly away from `x` (convexity).

## Main definitions

* `LMLExplore.fenchelConjugateOn F D`: the conjugate `u ↦ ⨆ x ∈ D, (u x - F x)` of `F` on `D`.

## Main statements

* `LMLExplore.fenchelConjugateOn_eq_fenchelConjugate`: the conversion to Tau Ceti's
  `fenchelConjugate`.
* `LMLExplore.hasSubgradientWithinAt_iff_fenchelConjugateOn_eq`: the Fenchel–Young equality.
* `LMLExplore.bregDiv_fenchelConjugateOn`: `D_{F⋆}(v, u) = D_F(x, y)` [LS, Theorem 26.6 (b)].
* `LMLExplore.hasFDerivAt_fenchelConjugateOn`: the conjugate has derivative evaluation at `x`
  at every subgradient of `F` at an interior point `x` [LS, Theorem 26.6 (a)].
* `LMLExplore.mem_interior_setOf_fenchelConjugateOn_ne_top`: such a subgradient is interior to
  the domain of the conjugate.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.5, Theorem 26.6 [LS].
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Theorems 23.5, 25.1
  and 26.3.
-/

public section

open Filter Set Metric
open scoped Topology

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ} {D : Set E}
  {x y : E} {u v : E →L[ℝ] ℝ} {a : EReal}

open Classical in
/-- The **Legendre–Fenchel conjugate of `F` on `D`**: the function `u ↦ ⨆ x ∈ D, (u x - F x)`
on the dual `E →L[ℝ] ℝ`, with values in `EReal`. It is Tau Ceti's `fenchelConjugate`, for the
pairing `(x, u) ↦ u x` of `E` with its dual, of `F` extended by `⊤` off `D`
(`fenchelConjugateOn_eq_fenchelConjugate`). -/
noncomputable def fenchelConjugateOn (F : E → ℝ) (D : Set E) (u : E →L[ℝ] ℝ) : EReal :=
  TauCeti.fenchelConjugate (topDualPairing ℝ E).flip
    (fun x ↦ if x ∈ D then (F x : EReal) else ⊤) u

/-- The conjugate on `D` is Tau Ceti's `fenchelConjugate` of `F` extended by `⊤` off `D`, for
the pairing of `E` with its dual. -/
theorem fenchelConjugateOn_eq_fenchelConjugate (F : E → ℝ) (D : Set E) [DecidablePred (· ∈ D)]
    (u : E →L[ℝ] ℝ) :
    fenchelConjugateOn F D u = TauCeti.fenchelConjugate (topDualPairing ℝ E).flip
      (fun x ↦ if x ∈ D then (F x : EReal) else ⊤) u := by
  unfold fenchelConjugateOn
  congr! with x

/-- The defining formula of the conjugate on `D`. -/
theorem fenchelConjugateOn_eq_iSup (F : E → ℝ) (D : Set E) (u : E →L[ℝ] ℝ) :
    fenchelConjugateOn F D u = ⨆ x ∈ D, ((u x : EReal) - F x) := by
  classical
  rw [fenchelConjugateOn_eq_fenchelConjugate, TauCeti.fenchelConjugate_apply]
  refine le_antisymm (iSup_le fun x ↦ ?_) (iSup₂_le fun x hx ↦ le_iSup_of_le x ?_)
  · by_cases hx : x ∈ D
    · simpa [hx] using le_iSup₂ (f := fun x (_ : x ∈ D) ↦ (u x : EReal) - F x) x hx
    · simp [hx]
  · simp [hx]

/-- An upper bound for the conjugate on `D` is an upper bound for every `u x - F x` with
`x ∈ D`. -/
theorem fenchelConjugateOn_le_iff :
    fenchelConjugateOn F D u ≤ a ↔ ∀ x ∈ D, (u x : EReal) - F x ≤ a := by
  rw [fenchelConjugateOn_eq_iSup]
  exact iSup₂_le_iff

/-- **The Fenchel–Young inequality** on `D`: `u x - F x ≤ F⋆ u` for `x ∈ D`. -/
theorem sub_le_fenchelConjugateOn (hx : x ∈ D) (u : E →L[ℝ] ℝ) :
    (u x : EReal) - F x ≤ fenchelConjugateOn F D u :=
  fenchelConjugateOn_le_iff.1 le_rfl x hx

/-- The conjugate on a set containing `x` is never `⊥`. -/
theorem fenchelConjugateOn_ne_bot (hx : x ∈ D) (u : E →L[ℝ] ℝ) :
    fenchelConjugateOn F D u ≠ ⊥ :=
  ne_bot_of_le_ne_bot (by simp [← EReal.coe_sub]) (sub_le_fenchelConjugateOn hx u)

/-- At a point of `D`, LML's subgradients of `F` on `D` are the elements of Tau Ceti's
subdifferential of `F` extended by `⊤` off `D`. -/
theorem mem_subdifferential_iff_hasSubgradientWithinAt [DecidablePred (· ∈ D)] (hx : x ∈ D) :
    u ∈ TauCeti.subdifferential (topDualPairing ℝ E).flip
        (fun x ↦ if x ∈ D then (F x : EReal) else ⊤) x ↔
      HasSubgradientWithinAt F u D x := by
  rw [TauCeti.mem_subdifferential_ite_iff _ hx, hasSubgradientWithinAt_iff_le]
  simp

/-- **The Fenchel–Young equality**: for `x ∈ D`, `u` is a subgradient of `F` on `D` at `x`
exactly when `F⋆ u = u x - F x`. -/
theorem hasSubgradientWithinAt_iff_fenchelConjugateOn_eq (hx : x ∈ D) :
    HasSubgradientWithinAt F u D x ↔ fenchelConjugateOn F D u = ((u x - F x : ℝ) : EReal) := by
  refine ⟨fun hu ↦ le_antisymm (fenchelConjugateOn_le_iff.2 fun z hz ↦ ?_) ?_, fun h ↦ ?_⟩
  · have := hu z hz
    simp only [bregDiv, map_sub] at this
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  · simpa [← EReal.coe_sub] using sub_le_fenchelConjugateOn hx u
  · refine fun z hz ↦ ?_
    have := (h ▸ sub_le_fenchelConjugateOn hz u : (u z : EReal) - F z ≤ _)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at this
    simp only [bregDiv, map_sub]
    linarith

/-- The real value of the conjugate at a subgradient `u` of `F` at `x ∈ D` is `u x - F x`. -/
theorem toReal_fenchelConjugateOn_of_hasSubgradientWithinAt (hu : HasSubgradientWithinAt F u D x)
    (hx : x ∈ D) : (fenchelConjugateOn F D u).toReal = u x - F x := by
  rw [(hasSubgradientWithinAt_iff_fenchelConjugateOn_eq hx).1 hu, EReal.toReal_coe]

/-- **Duality of Bregman divergences** [LS, Theorem 26.6 (b)]: for subgradients `u` of `F` at
`x ∈ D` and `v` at `y ∈ D`, the Bregman divergence of the conjugate between `v` and `u`, with
the evaluation at `x` as derivative at `u` (`hasFDerivAt_fenchelConjugateOn`), is
`D_F(x, y) = F x - F y - v (x - y)`. -/
theorem bregDiv_fenchelConjugateOn (hu : HasSubgradientWithinAt F u D x)
    (hv : HasSubgradientWithinAt F v D y) (hx : x ∈ D) (hy : y ∈ D) :
    bregDiv (fun w ↦ (fenchelConjugateOn F D w).toReal) v u (ContinuousLinearMap.apply ℝ ℝ x) =
      bregDiv F x y v := by
  simp only [bregDiv, toReal_fenchelConjugateOn_of_hasSubgradientWithinAt hu hx,
    toReal_fenchelConjugateOn_of_hasSubgradientWithinAt hv hy, ContinuousLinearMap.apply_apply,
    map_sub]
  ring

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The uniform growth bound behind the differentiability of the conjugate: for `F` convex on `D`
and strictly convex on its interior, a subgradient `u` at an interior point `x`, and `ε > 0`,
the tilt `h (z - x)` exceeds the Bregman divergence `D_F(z, x)` by at most `ε ‖h‖` on `D` for all
small `h`. Near `x` the tilt is small; away from `x` the divergence grows linearly with a slope
that beats `‖h‖`. -/
private lemma exists_pos_apply_sub_sub_bregDiv_le (hF : ConvexOn ℝ D F)
    (hFs : StrictConvexOn ℝ (interior D) F) (hx : x ∈ interior D)
    (hu : HasSubgradientWithinAt F u D x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : E →L[ℝ] ℝ, ‖h‖ ≤ δ → ∀ z ∈ D, h (z - x) - bregDiv F z x u ≤ ε * ‖h‖ := by
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set ρ := min (r / 2) ε
  have hρ : 0 < ρ := lt_min (half_pos hr) hε
  have hsphere : sphere x ρ ⊆ interior D := fun w hw ↦ hrD <| by
    rw [mem_sphere] at hw
    rw [mem_ball]
    linarith [min_le_left (r / 2) ε]
  -- The divergence `D_F(·, x)` is continuous and positive on the sphere of radius `ρ`, so it is
  -- bounded below there by some `c > 0`.
  have hcont : ContinuousOn (fun w ↦ bregDiv F w x u) (sphere x ρ) := by
    simp only [bregDiv]
    exact ((hF.continuousOn_interior.mono hsphere).sub continuousOn_const).sub
      (u.continuous.comp_continuousOn (continuousOn_id.sub continuousOn_const))
  obtain ⟨c, hc, hcφ⟩ := (isCompact_sphere x ρ).exists_forall_le' hcont fun w hw ↦
    hFs.bregDiv_pos (hu.mono interior_subset) hx (hsphere hw) (ne_of_mem_sphere hw hρ.ne')
  refine ⟨c / ρ, div_pos hc hρ, fun h hh z hz ↦ ?_⟩
  have hφz : 0 ≤ bregDiv F z x u := hu z hz
  have hhz : h (z - x) ≤ ‖h‖ * ‖z - x‖ := (le_abs_self _).trans (h.le_opNorm _)
  rcases le_or_gt ‖z - x‖ ρ with hzx | hzx
  · -- Near `x`, the tilt is at most `‖h‖ ρ ≤ ε ‖h‖`.
    have : ‖h‖ * ‖z - x‖ ≤ ε * ‖h‖ := by
      nlinarith [norm_nonneg h, min_le_right (r / 2) ε]
    linarith
  · -- Away from `x`, convexity along the segment from `x` to `z` through the sphere gives
    -- `D_F(z, x) ≥ c ‖z - x‖ / ρ ≥ ‖h‖ ‖z - x‖`.
    have hpos : 0 < ‖z - x‖ := hρ.trans hzx
    have ht0 : 0 < ρ / ‖z - x‖ := div_pos hρ hpos
    have hw : x + (ρ / ‖z - x‖) • (z - x) ∈ sphere x ρ := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le,
        div_mul_cancel₀ _ hpos.ne']
    have hslope := hF.bregDiv_slope_le (interior_subset hx) hz u ht0
      ((div_le_one hpos).2 hzx.le)
    rw [smul_eq_mul, inv_div] at hslope
    have h1 : ‖z - x‖ / ρ * c ≤ bregDiv F z x u :=
      (mul_le_mul_of_nonneg_left (hcφ _ hw) (by positivity)).trans hslope
    have h2 : ‖h‖ * ρ ≤ c := (le_div_iff₀ hρ).1 hh
    have h3 : ‖h‖ * ‖z - x‖ ≤ ‖z - x‖ / ρ * c := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hρ]
      nlinarith [norm_nonneg (z - x)]
    nlinarith [norm_nonneg h]

/-- The conjugate grows at most like its tangent `w ↦ u x - F x + (w - u) x` near a subgradient
`u` at an interior point `x`, up to `ε ‖w - u‖`. -/
private lemma exists_pos_fenchelConjugateOn_add_le (hF : ConvexOn ℝ D F)
    (hFs : StrictConvexOn ℝ (interior D) F) (hx : x ∈ interior D)
    (hu : HasSubgradientWithinAt F u D x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : E →L[ℝ] ℝ, ‖h‖ ≤ δ →
      fenchelConjugateOn F D (u + h) ≤ ((u x - F x + h x + ε * ‖h‖ : ℝ) : EReal) := by
  obtain ⟨δ, hδ, hest⟩ := exists_pos_apply_sub_sub_bregDiv_le hF hFs hx hu hε
  refine ⟨δ, hδ, fun h hh ↦ fenchelConjugateOn_le_iff.2 fun z hz ↦ ?_⟩
  have := hest h hh z hz
  simp only [bregDiv, map_sub] at this
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff, add_apply]
  linarith

/-- A subgradient of a function convex on `D` and strictly convex on its interior, at an
interior point of `D`, lies in the interior of the domain of the conjugate
[LS, Theorem 26.6 (a)]. -/
theorem mem_interior_setOf_fenchelConjugateOn_ne_top (hF : ConvexOn ℝ D F)
    (hFs : StrictConvexOn ℝ (interior D) F) (hx : x ∈ interior D)
    (hu : HasSubgradientWithinAt F u D x) :
    u ∈ interior {w | fenchelConjugateOn F D w ≠ ⊤} := by
  obtain ⟨δ, hδ, hle⟩ := exists_pos_fenchelConjugateOn_add_le hF hFs hx hu one_pos
  refine mem_interior_iff_mem_nhds.2 (mem_of_superset (closedBall_mem_nhds u hδ) fun w hw ↦ ?_)
  have := hle (w - u) (by rwa [mem_closedBall, dist_eq_norm] at hw)
  rw [add_sub_cancel] at this
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) this

/-- **The gradient of the conjugate inverts the subgradient** [LS, Theorem 26.6 (a)]: if `F` is
convex on `D` and strictly convex on the interior of `D`, then at every subgradient `u` of `F`
on `D` at an interior point `x`, the real representative of the conjugate is differentiable with
derivative the evaluation at `x`. For a differentiable `F` (`HasFDerivAt.hasSubgradientWithinAt`)
this is `∇F⋆ (∇F x) = x`. -/
theorem hasFDerivAt_fenchelConjugateOn (hF : ConvexOn ℝ D F)
    (hFs : StrictConvexOn ℝ (interior D) F) (hx : x ∈ interior D)
    (hu : HasSubgradientWithinAt F u D x) :
    HasFDerivAt (fun w ↦ (fenchelConjugateOn F D w).toReal) (ContinuousLinearMap.apply ℝ ℝ x)
      u := by
  have hxD := interior_subset hx
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hle⟩ := exists_pos_fenchelConjugateOn_add_le hF hFs hx hu hε
  filter_upwards [closedBall_mem_nhds (0 : E →L[ℝ] ℝ) hδ] with h hh
  have hup := hle h (mem_closedBall_zero_iff.1 hh)
  have hlow := sub_le_fenchelConjugateOn (F := F) hxD (u + h)
  have he := EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hup)
    (fenchelConjugateOn_ne_bot hxD (u + h))
  rw [← he, EReal.coe_le_coe_iff] at hup
  rw [← he, ← EReal.coe_sub, EReal.coe_le_coe_iff, add_apply] at hlow
  rw [toReal_fenchelConjugateOn_of_hasSubgradientWithinAt hu hxD,
    ContinuousLinearMap.apply_apply, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [norm_nonneg h]

end FiniteDimensional

end LMLExplore
