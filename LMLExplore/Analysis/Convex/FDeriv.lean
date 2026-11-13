/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Strict convexity and steepness through the derivative

This file relates two properties of a convex function `f` to its derivative `f'`, in the form in
which they pass from a Legendre function to its conjugate.

Strict convexity is injectivity of the derivative. A function with a subgradient at every point
of a convex set `s` is strictly convex on `s` as soon as no linear form is a subgradient at two
distinct points of `s`; conversely, a strictly convex function has no such common subgradient.
For a convex function with a derivative `f' x` at every point `x` of an open convex set `s`, the
subgradients are the derivatives, so `f` is strictly convex on `s` if and only if `f'` is
injective on `s`. The derivative of the conjugate of a Legendre function is the inverse of the
derivative of the function, which is injective, so this gives the strict convexity of the conjugate
[Roc70, Theorem 26.3].

Steepness passes to the inverse of the derivative. Let `f` be convex on an open set `s` of a proper
space (for instance a finite-dimensional one), with derivatives `f'` on `s` whose norm tends to
infinity at the frontier of `s`. Then for every linear form `b` that is not a derivative of `f` at a
point of `s`, the points of `s` whose derivative is close to `b` are far from the origin. In
particular, for every map `h` with `f' (h u) = u` and `h u ∈ s` for `u` in a set `t`, `‖h u‖` tends
to infinity as `u` tends to `b` within `t`. With `h` the derivative of the conjugate, this is the
steepness of the conjugate of a Legendre function [Roc70, Theorem 26.5; LS, Theorem 26.6].

## Main statements

* `Convex.strictConvexOn_of_hasSubgradientWithinAt`: a function with a subgradient on `s` at every
  point of `s` and no common subgradient at two distinct points is strictly convex on `s`.
* `StrictConvexOn.eq_of_hasSubgradientWithinAt`: two points of `s` at which a strictly convex
  function has a common subgradient on `s` coincide.
* `StrictConvexOn.injOn_of_hasFDerivWithinAt`: the derivative of a strictly convex function is
  injective.
* `ConvexOn.strictConvexOn_of_injOn`, `ConvexOn.strictConvexOn_iff_injOn`: a convex function with
  derivatives on an open set is strictly convex there if and only if its derivative is injective.
* `ConvexOn.tendsto_norm_atTop_of_steep`: for a steep convex function and a linear form `b` that is
  not a derivative at a point of `s`, `‖x‖ → ∞` as `x ∈ s` and `f' x → b`.
* `ConvexOn.tendsto_norm_comp_atTop_of_steep`: the same for a right inverse `h` of the derivative,
  `‖h u‖ → ∞` as `u → b`.

## References

* [Roc70] R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Section 26.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.4, Theorem 26.6.
-/

public section

open Filter Set Topology

variable {E : Type*}

section Subgradient

variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {s : Set E} {f : E → ℝ}
  {g : E →L[ℝ] ℝ} {x y : E}

/-- **Strict convexity from separated subgradients.** A function that has a subgradient on the
convex set `s` at every point of `s`, and no common subgradient at two distinct points of `s`, is
strictly convex on `s`. -/
theorem Convex.strictConvexOn_of_hasSubgradientWithinAt (hs : Convex ℝ s)
    (hsub : ∀ x ∈ s, ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x)
    (heq : ∀ x ∈ s, ∀ y ∈ s, ∀ g : E →L[ℝ] ℝ,
      HasSubgradientWithinAt f g s x → HasSubgradientWithinAt f g s y → x = y) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab ↦ ?_⟩
  -- A subgradient `g` at `z = a • x + b • y` is also one at `x` and `y` if `f` is affine on the
  -- segment, which separation excludes.
  obtain ⟨g, hg⟩ := hsub _ (hs hx hy ha.le hb.le hab)
  set z := a • x + b • y
  rw [hasSubgradientWithinAt_iff_le] at hg
  have hgx := hg x hx
  have hgy := hg y hy
  have hv : a • (x - z) + b • (y - z) = 0 := by
    rw [show a • (x - z) + b • (y - z) = z - (a + b) • z by simp only [z]; module, hab, one_smul,
      sub_self]
  have hlin : a * g (x - z) + b * g (y - z) = 0 := by
    simpa only [map_add, map_smul, smul_eq_mul, map_zero] using congrArg g hv
  simp only [smul_eq_mul]
  by_contra hlt
  push Not at hlt
  -- `f` is affine on the segment: `g` touches `f` at `x` and at `y`.
  have hz : (a + b) * f z = f z := by rw [hab, one_mul]
  have hx_eq : f x = f z + g (x - z) := by
    refine le_antisymm (not_lt.1 fun h ↦ ?_) hgx
    nlinarith [mul_pos ha (sub_pos.2 h), mul_nonneg hb.le (sub_nonneg.2 hgy), hz]
  have hy_eq : f y = f z + g (y - z) := by
    refine le_antisymm (not_lt.1 fun h ↦ ?_) hgy
    nlinarith [mul_pos hb (sub_pos.2 h), mul_nonneg ha.le (sub_nonneg.2 hgx), hz]
  have htouch {w : E} (hw : f w = f z + g (w - z)) : HasSubgradientWithinAt f g s w := by
    rw [hasSubgradientWithinAt_iff_le]
    intro v hv
    have : g (v - w) = g (v - z) - g (w - z) := by rw [← map_sub, sub_sub_sub_cancel_right]
    linarith [hg v hv]
  exact hxy (heq x hx y hy g (htouch hx_eq) (htouch hy_eq))

/-- **Strict convexity separates subgradients.** If `f` is strictly convex on `s` and `g` is a
subgradient of `f` on `s` at two points `x, y ∈ s`, then `x = y`. This is Tau Ceti's
`StrictConvexOn.eq_of_mem_subdifferential` for subgradients on a set. -/
theorem StrictConvexOn.eq_of_hasSubgradientWithinAt (hf : StrictConvexOn ℝ s f) (hx : x ∈ s)
    (hy : y ∈ s) (hgx : HasSubgradientWithinAt f g s x) (hgy : HasSubgradientWithinAt f g s y) :
    x = y := by
  have hmin {w : E} (hgw : HasSubgradientWithinAt f g s w) :
      IsMinOn (f - ⇑g.toLinearMap) s w := by
    rw [isMinOn_iff]
    intro v hv
    have := hasSubgradientWithinAt_iff_le.1 hgw v hv
    simp only [Pi.sub_apply, ContinuousLinearMap.coe_coe, map_sub] at this ⊢
    linarith
  exact (hf.sub_concaveOn (g.toLinearMap.concaveOn hf.1)).eq_of_isMinOn (hmin hgx) (hmin hgy) hx hy

end Subgradient

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
  {f' : E → E →L[ℝ] ℝ}

/-- **The derivative of a strictly convex function is injective.** If `f` is strictly convex on
`s` with derivative `f' x` within `s` at every `x ∈ s`, then `f'` is injective on `s`. -/
theorem StrictConvexOn.injOn_of_hasFDerivWithinAt (hf : StrictConvexOn ℝ s f)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) : s.InjOn f' := fun x hx y hy hxy ↦
  hf.eq_of_hasSubgradientWithinAt hx hy ((hf' x hx).hasSubgradientWithinAt hf.convexOn hx)
    (hxy ▸ (hf' y hy).hasSubgradientWithinAt hf.convexOn hy)

/-- **Strict convexity from an injective derivative.** A function convex on an open set `s`, with
derivative `f' x` at every `x ∈ s`, is strictly convex on `s` if `f'` is injective on `s`. -/
theorem ConvexOn.strictConvexOn_of_injOn (hf : ConvexOn ℝ s f) (hs : IsOpen s)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) (hinj : s.InjOn f') : StrictConvexOn ℝ s f :=
  hf.1.strictConvexOn_of_hasSubgradientWithinAt
    (fun x hx ↦ ⟨f' x, (hf' x hx).hasSubgradientWithinAt hf hx⟩)
    fun x hx y hy _ hgx hgy ↦ hinj hx hy <|
      ((hf' x hx).eq_of_hasSubgradientWithinAt (hs.mem_nhds hx) hgx).symm.trans
        ((hf' y hy).eq_of_hasSubgradientWithinAt (hs.mem_nhds hy) hgy)

/-- A function convex on an open set `s`, with derivative `f' x` at every `x ∈ s`, is strictly
convex on `s` if and only if `f'` is injective on `s`. -/
theorem ConvexOn.strictConvexOn_iff_injOn (hf : ConvexOn ℝ s f) (hs : IsOpen s)
    (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x) : StrictConvexOn ℝ s f ↔ s.InjOn f' :=
  ⟨fun h ↦ h.injOn_of_hasFDerivWithinAt fun x hx ↦ (hf' x hx).hasFDerivWithinAt,
    hf.strictConvexOn_of_injOn hs hf'⟩

/-- **Steepness passes to the inverse of the derivative.** Let `f` be convex on an open set `s` of
a proper space, with derivative `f' x` at every `x ∈ s`, and steep: `‖f' y‖ → ∞` as `y` tends
within `s` to a point of the frontier of `s`. If the linear form `b` is not the derivative of `f`
at a point of `s`, then `‖x‖ → ∞` as `x ∈ s` and `f' x → b`. -/
theorem ConvexOn.tendsto_norm_atTop_of_steep [ProperSpace E] (hf : ConvexOn ℝ s f)
    (hs : IsOpen s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hsteep : ∀ x ∈ frontier s, Tendsto (fun y ↦ ‖f' y‖) (𝓝[s] x) atTop)
    {b : E →L[ℝ] ℝ} (hb : b ∉ f' '' s) :
    Tendsto (fun x ↦ ‖x‖) (comap f' (𝓝 b) ⊓ 𝓟 s) atTop := by
  -- A bounded family of such points has a cluster point `x` in the closure of `s`. If `x ∈ s`, the
  -- subgradient inequalities at the nearby points pass to the limit and make `b` a subgradient,
  -- hence the derivative, at `x`; if `x` is on the frontier, steepness contradicts `f' → b`.
  rw [Filter.tendsto_atTop]
  intro R
  by_contra hR
  rw [not_eventually, frequently_iff_neBot] at hR
  have hball : 𝓟 {y : E | ¬R ≤ ‖y‖} ≤ 𝓟 (Metric.closedBall 0 R) :=
    principal_mono.2 fun y (hy : ¬R ≤ ‖y‖) ↦ by simpa using (not_le.1 hy).le
  obtain ⟨x, -, hx⟩ := (isCompact_closedBall (0 : E) R).exists_clusterPt
    (f := comap f' (𝓝 b) ⊓ 𝓟 s ⊓ 𝓟 {y | ¬R ≤ ‖y‖}) (inf_le_right.trans hball)
  -- `H` is the filter of points of `s` near `x` with derivative near `b`.
  set H := 𝓝 x ⊓ (comap f' (𝓝 b) ⊓ 𝓟 s ⊓ 𝓟 {y | ¬R ≤ ‖y‖})
  have : H.NeBot := hx
  have hHx : H ≤ 𝓝 x := inf_le_left
  have hHs : H ≤ 𝓟 s := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have hHb : Tendsto f' H (𝓝 b) :=
    tendsto_comap.mono_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
  by_cases hxs : x ∈ s
  · -- `b` is a subgradient of `f` on `s` at `x`, hence the derivative there.
    refine hb ⟨x, hxs, ((hf' x hxs).eq_of_hasSubgradientWithinAt (hs.mem_nhds hxs) ?_).symm⟩
    rw [hasSubgradientWithinAt_iff_le]
    intro y hy
    have hlim : Tendsto (fun z ↦ f z + f' z (y - z)) H (𝓝 (f x + b (y - x))) :=
      (((hf' x hxs).continuousAt.tendsto.mono_left hHx)).add <|
        (isBoundedBilinearMap_apply.continuous.tendsto (b, y - x)).comp <|
          hHb.prodMk_nhds ((tendsto_const_nhds.sub tendsto_id).mono_left hHx)
    refine le_of_tendsto hlim ?_
    filter_upwards [le_principal_iff.1 hHs] with z hz
    exact hasSubgradientWithinAt_iff_le.1 ((hf' z hz).hasSubgradientWithinAt hf hz) y hy
  · -- `x` is on the frontier of `s`, where steepness contradicts `f' → b`.
    have hxcl : x ∈ closure s :=
      mem_closure_iff_clusterPt.2 (NeBot.mono this (le_inf hHx hHs))
    have hxf : x ∈ frontier s := by rw [hs.frontier_eq]; exact ⟨hxcl, hxs⟩
    exact not_tendsto_atTop_of_tendsto_nhds (hHb.norm)
      ((hsteep x hxf).mono_left (le_inf hHx hHs))

/-- **Steepness passes to the inverse of the derivative**, for a right inverse. Under the
hypotheses of `ConvexOn.tendsto_norm_atTop_of_steep`, let `h` map a set `t` of linear forms into
`s` with `f' (h u) = u` for `u ∈ t`. Then `‖h u‖ → ∞` as `u` tends to `b` within `t`. -/
theorem ConvexOn.tendsto_norm_comp_atTop_of_steep [ProperSpace E] (hf : ConvexOn ℝ s f)
    (hs : IsOpen s) (hf' : ∀ x ∈ s, HasFDerivAt f (f' x) x)
    (hsteep : ∀ x ∈ frontier s, Tendsto (fun y ↦ ‖f' y‖) (𝓝[s] x) atTop)
    {b : E →L[ℝ] ℝ} (hb : b ∉ f' '' s) {t : Set (E →L[ℝ] ℝ)} {h : (E →L[ℝ] ℝ) → E}
    (hmaps : MapsTo h t s) (hinv : ∀ u ∈ t, f' (h u) = u) :
    Tendsto (fun u ↦ ‖h u‖) (𝓝[t] b) atTop := by
  refine (hf.tendsto_norm_atTop_of_steep hs hf' hsteep hb).comp (tendsto_inf.2 ⟨?_, ?_⟩)
  · rw [tendsto_comap_iff]
    exact tendsto_nhdsWithin_congr (fun u hu ↦ (hinv u hu).symm)
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  · exact tendsto_principal.2 (eventually_mem_nhdsWithin.mono fun u hu ↦ hmaps hu)
