/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Bregman.Projection
public import LMLExplore.Analysis.Convex.Bregman.StrictConvex
public import LMLExplore.Analysis.Convex.Extrema
public import LMLExplore.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Legendre functions

A convex function `F` with domain `D` in a real normed space `E` is **Legendre** [LS, §26.4] if
the interior of `D` is nonempty, `F` is differentiable and strictly convex on the interior of `D`,
and the norm of its derivative tends to infinity at every point of the boundary of the interior
of `D`. The function is represented by `F : E → ℝ` together with its convex domain `D`; its
values outside `D` play no role.

The last condition, steepness, forces the minimizers of `F` to lie in the interior of `D`: the
directional derivative of `F` along a segment from an interior point to a boundary point tends to
infinity [LS, Proposition 26.7], so `F` decreases when one moves from a boundary point into the
interior. Hence a minimizer of `F` over `A ∩ D`, for a convex set `A` meeting the interior of
`D`, is an interior point [LS, Corollary 26.8], where it is characterized by the first-order
condition [LS, Proposition 26.14]. In finite dimension, if `F` has a minimizer over `D`, then it
has a unique minimizer over `A ∩ D` for every closed convex `A` meeting the interior of `D`, and
this minimizer is the Bregman projection onto `A ∩ D` of the minimizer over `D` [LS,
Theorem 26.15]. This is what makes follow the regularized leader and mirror descent with a
Legendre potential well defined, with plays in the interior of the domain, where the potential is
differentiable.

## Main definitions

* `LMLExplore.IsLegendre F D`: `F` is a Legendre function with domain `D`.

## Main statements

* `IsLegendre.tendsto_fderiv_apply_sub`: [LS, Proposition 26.7]. For `x` in the interior of `D`
  and `y` in the boundary of the interior, `∇F(x + α (y - x)) (y - x) → ∞` as `α → 1⁻`.
* `IsLegendre.mem_interior_of_isMinOn_inter`, `IsLegendre.mem_interior_of_isMinOn`:
  [LS, Corollary 26.8]. Minimizers of `F` over `A ∩ D`, for a convex `A` meeting the interior of
  `D`, and in particular over `D`, lie in the interior of `D`.
* `IsLegendre.isMinOn_inter_iff`: [LS, Proposition 26.14]. Such minimizers are the points `x` of
  the interior with `∇F(x) (y - x) ≥ 0` for all `y ∈ A ∩ D`.
* `IsLegendre.add_linear`, `IsLegendre.add_const`: [LS, Exercise 26.10]. Adding an affine
  function preserves the Legendre property.
* `IsLegendre.isBounded_sublevel`: in finite dimension, if `F` has a minimizer over `D`, its
  sublevel sets in `D` are bounded.
* `IsLegendre.existsUnique_isMinOn_inter`, `IsLegendre.isMinOn_bregDiv_iff`: [LS, Theorem 26.15].
  In finite dimension, if `F` has a minimizer `y₀` over `D`, then for every closed convex `A`
  meeting the interior of `D`, `F` has a unique minimizer over `A ∩ D`, and the minimizers of `F`
  over any set are those of the Bregman divergence `D_F(·, y₀)`.
* `IsLegendre.bregDiv`: the Bregman divergence `D_F(·, y)` of a Legendre function is
  Legendre.
* `IsLegendre.existsUnique_isMinOn_bregDiv`, `IsLegendre.mem_interior_of_isMinOn_bregDiv`: in
  finite dimension, the Bregman projection of an interior point onto `A ∩ D` exists and is
  unique, for closed convex `A` meeting the interior of `D`; Bregman projections lie in the
  interior of `D`.
* `IsLegendre.bregDiv_add_bregDiv_le`: [LS, Exercise 26.13 (a)]. The generalized Pythagorean
  inequality `D_F(x, z) + D_F(z, y) ≤ D_F(x, y)` for the Bregman projection `z` of `y`.
* `isLegendre_mul_log`: `x ↦ x log x` is Legendre with domain `[0, ∞)` [LS, Example 26.11].

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Sections 26.4–26.6.
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970, Section 26.
-/

public section

open Set Filter Topology

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ} {D A : Set E}
  {x y : E}

/-- A **Legendre function** [LS, §26.4] with domain `D`: `F` is convex on `D`, the interior of `D`
is nonempty, `F` is differentiable and strictly convex on the interior of `D`, and the norm of the
derivative of `F` tends to infinity at every point of the boundary of the interior of `D`. -/
structure IsLegendre (F : E → ℝ) (D : Set E) : Prop where
  /-- `F` is convex on its domain `D`. -/
  convexOn : ConvexOn ℝ D F
  /-- The interior of the domain is nonempty. -/
  nonempty_interior : (interior D).Nonempty
  /-- `F` is differentiable on the interior of its domain. -/
  differentiableOn : DifferentiableOn ℝ F (interior D)
  /-- `F` is strictly convex on the interior of its domain. -/
  strictConvexOn : StrictConvexOn ℝ (interior D) F
  /-- Steepness: the norm of the derivative tends to infinity at the boundary of the interior of
  the domain. -/
  tendsto_norm_fderiv : ∀ x ∈ frontier (interior D),
    Tendsto (fun y ↦ ‖fderiv ℝ F y‖) (𝓝[interior D] x) atTop

namespace IsLegendre

variable (hF : IsLegendre F D)
include hF

/-- The domain of a Legendre function is convex. -/
lemma convex : Convex ℝ D := hF.convexOn.1

/-- A Legendre function has its derivative at every interior point of its domain. -/
lemma hasFDerivAt (hx : x ∈ interior D) : HasFDerivAt F (fderiv ℝ F x) x :=
  (hF.differentiableOn.differentiableAt (isOpen_interior.mem_nhds hx)).hasFDerivAt

/-- The derivative of a Legendre function at an interior point of its domain is a subgradient
of it over the domain: `D_F(y, x) ≥ 0` for `y ∈ D` [LS, Theorem 26.3 (a)]. -/
lemma hasSubgradientWithinAt (hx : x ∈ interior D) :
    HasSubgradientWithinAt F (fderiv ℝ F x) D x :=
  (hF.hasFDerivAt hx).hasSubgradientWithinAt hF.convexOn (interior_subset hx)

/-- The tangent inequality `F x + ∇F(x) (y - x) ≤ F y` at an interior point `x` of the domain,
for `y ∈ D`. -/
lemma add_fderiv_apply_sub_le (hx : x ∈ interior D) (hy : y ∈ D) :
    F x + fderiv ℝ F x (y - x) ≤ F y :=
  hasSubgradientWithinAt_iff_le.1 (hF.hasSubgradientWithinAt hx) y hy

/-- A point of the closure of the domain that is not interior lies in the boundary of the
interior. -/
lemma mem_frontier_interior (hx : x ∈ closure D) (hx' : x ∉ interior D) :
    x ∈ frontier (interior D) := by
  rw [frontier, interior_interior,
    hF.convex.closure_interior_eq_closure_of_nonempty_interior hF.nonempty_interior]
  exact ⟨hx, hx'⟩

/-- Along a segment from an interior point `x` of the domain, the directional derivative
`α ↦ ∇F(x + α (y - x)) (y - x)` is nondecreasing on `[0, 1)`. -/
private lemma fderiv_apply_sub_mono (hx : x ∈ interior D) (hy : y ∈ closure D) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β < 1) :
    fderiv ℝ F (x + α • (y - x)) (y - x) ≤ fderiv ℝ F (x + β • (y - x)) (y - x) := by
  have hzα := hF.convex.add_smul_sub_mem_interior_of_mem_closure hx hy hα (hαβ.trans_lt hβ)
  have hzβ := hF.convex.add_smul_sub_mem_interior_of_mem_closure hx hy (hα.trans hαβ) hβ
  have h := HasSubgradientWithinAt.sub_apply_sub_nonneg (interior_subset hzβ)
    (interior_subset hzα) (hF.hasSubgradientWithinAt hzβ) (hF.hasSubgradientWithinAt hzα)
  have h_eq : x + β • (y - x) - (x + α • (y - x)) = (β - α) • (y - x) := by module
  rw [h_eq, map_smul, smul_eq_mul, sub_apply] at h
  rcases hαβ.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact sub_nonneg.1 ((mul_nonneg_iff_of_pos_left (sub_pos.2 hlt)).1 h)

/-- If the directional derivative `∇F(x + α (y - x)) (y - x)` is at most `M` on `[0, 1)`, the
derivative of `F` stays bounded along the segment from the interior point `x` to `y`. -/
private lemma exists_norm_fderiv_le (hx : x ∈ interior D) (hy : y ∈ closure D) {M : ℝ}
    (hM : ∀ α ∈ Ico (0 : ℝ) 1, fderiv ℝ F (x + α • (y - x)) (y - x) ≤ M) :
    ∃ C, ∀ α ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ F (x + α • (y - x))‖ ≤ C := by
  -- `F` is at most `F x + 1` on a closed ball around `x` contained in `D`.
  have h_nhds : D ∩ {u | F u < F x + 1} ∈ 𝓝 x :=
    inter_mem (mem_interior_iff_mem_nhds.1 hx)
      ((hF.hasFDerivAt hx).continuousAt.eventually (gt_mem_nhds (lt_add_one (F x))))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 h_nhds
  have hr : 0 < ε / 2 := half_pos hε
  have hmem : ∀ w ∈ Metric.closedBall (0 : E) (ε / 2), x + w ∈ D ∧ F (x + w) ≤ F x + 1 := by
    intro w hw
    have hw' : x + w ∈ Metric.ball x ε := by
      rw [Metric.mem_closedBall, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith
    exact ⟨(hball hw').1, (hball hw').2.le⟩
  set L₀ := fderiv ℝ F x
  refine ⟨(1 + |L₀ (y - x)| + |M|) / (ε / 2), fun α hα ↦ ?_⟩
  set z := x + α • (y - x)
  have hz := hF.convex.add_smul_sub_mem_interior_of_mem_closure hx hy hα.1 hα.2
  -- The tangent inequalities at `x` and at `z` bound `∇F(z)` on the ball.
  have hlow : F x + α * L₀ (y - x) ≤ F z := by
    have := hF.add_fderiv_apply_sub_le hx (interior_subset hz)
    rwa [show z - x = α • (y - x) by simp [z], map_smul, smul_eq_mul] at this
  have hbound : ∀ w ∈ Metric.closedBall (0 : E) (ε / 2),
      fderiv ℝ F z w ≤ 1 + |L₀ (y - x)| + |M| := by
    intro w hw
    obtain ⟨hwD, hwF⟩ := hmem w hw
    have := hF.add_fderiv_apply_sub_le hz hwD
    rw [show x + w - z = w - α • (y - x) by simp [z], map_sub, map_smul,
      smul_eq_mul] at this
    have h1 : α * fderiv ℝ F z (y - x) ≤ |M| :=
      (mul_le_mul_of_nonneg_left (hM α hα) hα.1).trans
        ((mul_le_mul_of_nonneg_left (le_abs_self M) hα.1).trans
          (mul_le_of_le_one_left (abs_nonneg M) hα.2.le))
    have h2 : -(α * L₀ (y - x)) ≤ |L₀ (y - x)| := by
      rw [← mul_neg]
      exact (mul_le_mul_of_nonneg_left (neg_le_abs _) hα.1).trans
        (mul_le_of_le_one_left (abs_nonneg _) hα.2.le)
    linarith
  refine ContinuousLinearMap.opNorm_bound_of_ball_bound hr _ _ fun w hw ↦ ?_
  have hw' : -w ∈ Metric.closedBall (0 : E) (ε / 2) := by simpa using hw
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hbound (-w) hw', map_neg (fderiv ℝ F z) w], hbound w hw⟩

/-- **The derivative of a Legendre function blows up at the boundary** [LS, Proposition 26.7].
For `x` in the interior of the domain and `y` in the boundary of the interior, the directional
derivative `∇F(x + α (y - x)) (y - x)` tends to infinity as `α → 1⁻`. -/
theorem tendsto_fderiv_apply_sub (hx : x ∈ interior D) (hy : y ∈ frontier (interior D)) :
    Tendsto (fun α : ℝ ↦ fderiv ℝ F (x + α • (y - x)) (y - x)) (𝓝[<] 1) atTop := by
  have hyD : y ∈ closure D := closure_mono interior_subset (frontier_subset_closure hy)
  rw [tendsto_atTop]
  intro M
  by_contra hM
  -- By monotonicity, the directional derivative stays below `M` on `[0, 1)`.
  have hlt : ∀ α ∈ Ico (0 : ℝ) 1, fderiv ℝ F (x + α • (y - x)) (y - x) ≤ M := by
    intro α hα
    by_contra hαM
    refine hM (eventually_of_mem (Ioo_mem_nhdsLT hα.2) fun β hβ ↦ ?_)
    exact (not_le.1 hαM).le.trans (fderiv_apply_sub_mono hF hx hyD hα.1 hβ.1.le hβ.2)
  obtain ⟨C, hC⟩ := exists_norm_fderiv_le hF hx hyD hlt
  -- But the derivative is unbounded near the boundary point `y`.
  have h_tendsto : Tendsto (fun α : ℝ ↦ x + α • (y - x)) (𝓝[<] 1) (𝓝[interior D] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_of_mem (Ioo_mem_nhdsLT zero_lt_one)
      fun α hα ↦ hF.convex.add_smul_sub_mem_interior_of_mem_closure hx hyD hα.1.le hα.2⟩
    have : Tendsto (fun α : ℝ ↦ x + α • (y - x)) (𝓝 1) (𝓝 (x + (1 : ℝ) • (y - x))) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 1)
    rw [one_smul, add_sub_cancel] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨α, hαC, hα⟩ := (((hF.tendsto_norm_fderiv y hy).comp h_tendsto).eventually_gt_atTop C
    |>.and (Ioo_mem_nhdsLT zero_lt_one)).exists
  exact (hC α ⟨hα.1.le, hα.2⟩).not_gt hαC

/-- **Minimizers of a Legendre function are interior** [LS, Corollary 26.8]. If `A` is convex and
meets the interior of the domain `D`, then every minimizer of `F` over `A ∩ D` lies in the interior
of `D`. -/
theorem mem_interior_of_isMinOn_inter (hA : Convex ℝ A) (hAD : (A ∩ interior D).Nonempty)
    (hx : x ∈ A ∩ D) (hmin : IsMinOn F (A ∩ D) x) : x ∈ interior D := by
  by_contra hx'
  obtain ⟨x₀, hx₀A, hx₀⟩ := hAD
  have hxD : x ∈ closure D := subset_closure hx.2
  obtain ⟨α, hpos, hα⟩ := ((hF.tendsto_fderiv_apply_sub hx₀
    (hF.mem_frontier_interior hxD hx')).eventually_gt_atTop 0
    |>.and (Ioo_mem_nhdsLT zero_lt_one)).exists
  set z := x₀ + α • (x - x₀)
  have hz := hF.convex.add_smul_sub_mem_interior_of_mem_closure hx₀ hxD hα.1.le hα.2
  have hzA : z ∈ A := hA.add_smul_sub_mem hx₀A hx.1 ⟨hα.1.le, hα.2.le⟩
  -- The tangent inequality at `z` shows `F z < F x`.
  have htan := hF.add_fderiv_apply_sub_le hz hx.2
  rw [show x - z = (1 - α) • (x - x₀) by simp [z]; module, map_smul, smul_eq_mul] at htan
  have := mul_pos (sub_pos.2 hα.2) hpos
  linarith [isMinOn_iff.1 hmin z ⟨hzA, interior_subset hz⟩]

/-- **Minimizers of a Legendre function are interior** [LS, Corollary 26.8]: every minimizer of
`F` over its domain lies in the interior of the domain. -/
theorem mem_interior_of_isMinOn (hx : x ∈ D) (hmin : IsMinOn F D x) : x ∈ interior D :=
  hF.mem_interior_of_isMinOn_inter (A := univ) convex_univ (by simpa using hF.nonempty_interior)
    (by simpa using hx) (by simpa using hmin)

/-- The derivative of a Legendre function vanishes at its minimizers over the domain. -/
theorem fderiv_eq_zero_of_isMinOn (hx : x ∈ D) (hmin : IsMinOn F D x) : fderiv ℝ F x = 0 :=
  (hmin.isLocalMin
    (mem_interior_iff_mem_nhds.1 (hF.mem_interior_of_isMinOn hx hmin))).fderiv_eq_zero

/-- **First-order optimality for Legendre functions** [LS, Proposition 26.14]. If `A` is convex
and meets the interior of the domain `D`, a point `x ∈ A ∩ D` minimizes `F` over `A ∩ D` if and
only if it lies in the interior of `D` and `∇F(x) (y - x) ≥ 0` for every `y ∈ A ∩ D`. -/
theorem isMinOn_inter_iff (hA : Convex ℝ A) (hAD : (A ∩ interior D).Nonempty) (hx : x ∈ A ∩ D) :
    IsMinOn F (A ∩ D) x ↔ x ∈ interior D ∧ ∀ y ∈ A ∩ D, 0 ≤ fderiv ℝ F x (y - x) := by
  have hconv : ConvexOn ℝ (A ∩ D) F := hF.convexOn.subset inter_subset_right (hA.inter hF.convex)
  refine ⟨fun h ↦ ?_, fun ⟨hxi, h⟩ ↦ ?_⟩
  · have hxi := hF.mem_interior_of_isMinOn_inter hA hAD hx h
    exact ⟨hxi, (hconv.isMinOn_iff_forall_apply_sub_nonneg hx
      (hF.hasFDerivAt hxi).hasFDerivWithinAt).1 h⟩
  · exact (hconv.isMinOn_iff_forall_apply_sub_nonneg hx
      (hF.hasFDerivAt hxi).hasFDerivWithinAt).2 h

/-- **Adding a linear function preserves the Legendre property** [LS, Exercise 26.10]. -/
theorem add_linear (L : E →L[ℝ] ℝ) : IsLegendre (fun x ↦ F x + L x) D where
  convexOn := hF.convexOn.add (L.toLinearMap.convexOn hF.convex)
  nonempty_interior := hF.nonempty_interior
  differentiableOn := hF.differentiableOn.add L.differentiable.differentiableOn
  strictConvexOn := hF.strictConvexOn.add_convexOn (L.toLinearMap.convexOn hF.convex.interior)
  tendsto_norm_fderiv x hx := by
    refine tendsto_atTop_mono' _ ?_
      (tendsto_atTop_add_const_right _ (-‖L‖) (hF.tendsto_norm_fderiv x hx))
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [fderiv_fun_add (hF.hasFDerivAt hy).differentiableAt L.differentiableAt, L.fderiv]
    have := norm_sub_le (fderiv ℝ F y + L) L
    rw [add_sub_cancel_right] at this
    linarith

/-- Adding a constant preserves the Legendre property. -/
theorem add_const (c : ℝ) : IsLegendre (fun x ↦ F x + c) D where
  convexOn := hF.convexOn.add_const c
  nonempty_interior := hF.nonempty_interior
  differentiableOn := hF.differentiableOn.add_const c
  strictConvexOn := hF.strictConvexOn.add_const c
  tendsto_norm_fderiv x hx := by simpa only [fderiv_add_const] using hF.tendsto_norm_fderiv x hx

/-- In finite dimension, the sublevel sets `{x ∈ D | F x ≤ c}` of a Legendre function with a
minimizer over its domain are bounded. -/
theorem isBounded_sublevel [FiniteDimensional ℝ E] {y₀ : E} (hy₀ : y₀ ∈ D) (hmin : IsMinOn F D y₀)
    (c : ℝ) : Bornology.IsBounded {x ∈ D | F x ≤ c} := by
  have hy₀i := hF.mem_interior_of_isMinOn hy₀ hmin
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hy₀i)
  have hsph : Metric.sphere y₀ (r / 2) ⊆ interior D := fun z hz ↦
    interior_maximal hball Metric.isOpen_ball
      (by rw [Metric.mem_ball, Metric.mem_sphere.1 hz]; linarith)
  -- Beyond the sphere of radius `r / 2`, `F x - F y₀ = D_F(x, y₀)` grows at least linearly in
  -- `‖x - y₀‖`, since the derivative of `F` vanishes at the minimizer `y₀`.
  obtain ⟨k, hk, hgrow⟩ := hF.strictConvexOn.exists_pos_mul_norm_le_bregDiv hF.convexOn hy₀i
    (hF.hasSubgradientWithinAt hy₀i) (half_pos hr) hsph
  refine (Metric.isBounded_closedBall (x := y₀) (r := max (r / 2) ((c - F y₀) / k))).subset
    fun x ⟨hxD, hxc⟩ ↦ ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  by_contra hfar
  have hgrow_x := hgrow x hxD ((le_max_left _ _).trans (not_le.1 hfar).le)
  rw [bregDiv, hF.fderiv_eq_zero_of_isMinOn hy₀ hmin, zero_apply,
    sub_zero] at hgrow_x
  have hd : (c - F y₀) / k < ‖x - y₀‖ := (le_max_right _ _).trans_lt (not_le.1 hfar)
  rw [div_lt_iff₀ hk] at hd
  linarith

/-- Along a segment from an interior point `x₀` to a boundary point `b` of the interior of the
domain, `F` cannot stay below the chord to a level `m` at `b`: if
`F (x₀ + α (b - x₀)) ≤ (1 - α) F x₀ + α m` for `0 ≤ α < 1`, then `F < m` at some point of the open
segment. -/
private lemma exists_apply_add_smul_sub_lt {x₀ b : E} {m : ℝ} (hx₀ : x₀ ∈ interior D)
    (hb : b ∈ frontier (interior D))
    (hm : ∀ α ∈ Ico (0 : ℝ) 1, F (x₀ + α • (b - x₀)) ≤ (1 - α) * F x₀ + α * m) :
    ∃ α ∈ Ioo (0 : ℝ) 1, F (x₀ + α • (b - x₀)) < m := by
  have hbD : b ∈ closure D := closure_mono interior_subset (frontier_subset_closure hb)
  -- A point `z₀` of the segment where the directional derivative `g` is positive.
  obtain ⟨α₀, hg, hα₀⟩ := ((hF.tendsto_fderiv_apply_sub hx₀ hb).eventually_gt_atTop 0
    |>.and (Ioo_mem_nhdsLT zero_lt_one)).exists
  set g := fderiv ℝ F (x₀ + α₀ • (b - x₀)) (b - x₀)
  have hz₀ := hF.convex.add_smul_sub_mem_interior_of_mem_closure hx₀ hbD hα₀.1.le hα₀.2
  refine ⟨α₀, hα₀, ?_⟩
  -- The chord bound beyond `z₀`, minus the tangent at `z₀`, tends to `m - (1 - α₀) g < m`.
  have hcont : Tendsto (fun α : ℝ ↦ (1 - α) * F x₀ + α * m - (α - α₀) * g) (𝓝[<] 1)
      (𝓝 ((1 - 1) * F x₀ + 1 * m - (1 - α₀) * g)) :=
    (Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds
  have hlt : (1 - 1) * F x₀ + 1 * m - (1 - α₀) * g < m := by
    nlinarith [mul_pos (sub_pos.2 hα₀.2) hg]
  obtain ⟨α, hαm, hα⟩ := ((hcont.eventually (Iio_mem_nhds hlt)).and
    (Ioo_mem_nhdsLT hα₀.2)).exists
  have hz := hF.convex.add_smul_sub_mem_interior_of_mem_closure hx₀ hbD
    (hα₀.1.le.trans hα.1.le) hα.2
  have htan := hF.add_fderiv_apply_sub_le hz₀ (interior_subset hz)
  rw [show x₀ + α • (b - x₀) - (x₀ + α₀ • (b - x₀)) = (α - α₀) • (b - x₀) by module, map_smul,
    smul_eq_mul] at htan
  have := hm α ⟨hα₀.1.le.trans hα.1.le, hα.2⟩
  linarith

/-- If points `x n ∈ D` tend to `b` and `F (x n)` tends to `m`, then on the segment from an
interior point `x₀` to `b`, `F` lies below the chord from `F x₀` to `m`. -/
private lemma apply_add_smul_sub_le_of_tendsto {x₀ b : E} {m : ℝ} {u : ℕ → E}
    (hx₀ : x₀ ∈ interior D) (hb : b ∈ closure D) (huD : ∀ n, u n ∈ D)
    (hu : Tendsto u atTop (𝓝 b)) (hFu : Tendsto (fun n ↦ F (u n)) atTop (𝓝 m)) {α : ℝ}
    (hα : α ∈ Ico (0 : ℝ) 1) :
    F (x₀ + α • (b - x₀)) ≤ (1 - α) * F x₀ + α * m := by
  have hz := hF.convex.add_smul_sub_mem_interior_of_mem_closure hx₀ hb hα.1 hα.2
  have hlim : Tendsto (fun n ↦ x₀ + α • (u n - x₀)) atTop (𝓝 (x₀ + α • (b - x₀))) :=
    tendsto_const_nhds.add ((hu.sub_const x₀).const_smul α)
  refine le_of_tendsto_of_tendsto' (((hF.hasFDerivAt hz).continuousAt.tendsto).comp hlim)
    ((tendsto_const_nhds.mul tendsto_const_nhds).add (tendsto_const_nhds.mul hFu))
    fun n ↦ ?_
  have := hF.convexOn.2 (interior_subset hx₀) (huD n) (sub_nonneg.2 hα.2.le) hα.1 (by ring)
  rwa [smul_eq_mul, smul_eq_mul, show (1 - α) • x₀ + α • u n = x₀ + α • (u n - x₀) by module]
    at this

/-- Existence in [LS, Theorem 26.15 (a)]: in finite dimension, a Legendre function with a
minimizer over its domain attains its minimum over `A ∩ D` for every closed convex `A` meeting the
interior of `D`. -/
private lemma exists_isMinOn_inter [FiniteDimensional ℝ E] (hA : IsClosed A) (hAc : Convex ℝ A)
    (hAD : (A ∩ interior D).Nonempty) {y₀ : E} (hy₀ : y₀ ∈ D) (hmin : IsMinOn F D y₀) :
    ∃ y ∈ A ∩ D, IsMinOn F (A ∩ D) y := by
  obtain ⟨x₀, hx₀A, hx₀⟩ := hAD
  -- A minimizing sequence `u n`, bounded since it stays in a sublevel set.
  have hbdd : BddBelow (F '' (A ∩ D)) :=
    ⟨F y₀, forall_mem_image.2 fun x hx ↦ isMinOn_iff.1 hmin x hx.2⟩
  obtain ⟨v, hv_anti, hv, hv_mem⟩ := exists_seq_tendsto_sInf (S := F '' (A ∩ D))
    ⟨F x₀, mem_image_of_mem F ⟨hx₀A, interior_subset hx₀⟩⟩ hbdd
  set m := sInf (F '' (A ∩ D))
  have hm : ∀ y ∈ A ∩ D, m ≤ F y := fun y hy ↦ csInf_le hbdd (mem_image_of_mem F hy)
  choose u hu hFu using hv_mem
  obtain ⟨b, hb, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (hF.isBounded_sublevel hy₀ hmin (v 0))
    fun n ↦ ⟨(hu n).2, (hFu n).le.trans (hv_anti (Nat.zero_le n))⟩
  have hbD : b ∈ closure D := closure_mono (sep_subset _ _) hb
  have hbA : b ∈ A := hA.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ (hu (φ n)).1)
  have hFlim : Tendsto (fun n ↦ F (u (φ n))) atTop (𝓝 m) := by
    simpa only [Function.comp_def, hFu] using hv.comp hφ.tendsto_atTop
  by_cases hbi : b ∈ interior D
  · -- An interior limit point is a minimizer, by continuity of `F` there.
    have hFb : F b = m :=
      tendsto_nhds_unique (((hF.hasFDerivAt hbi).continuousAt.tendsto).comp hlim) hFlim
    exact ⟨b, ⟨hbA, interior_subset hbi⟩, isMinOn_iff.2 fun y hy ↦ hFb ▸ hm y hy⟩
  · -- A boundary limit point is impossible: `F < m` at some point of `A ∩ D`.
    obtain ⟨α, hα, hlt⟩ := hF.exists_apply_add_smul_sub_lt hx₀ (hF.mem_frontier_interior hbD hbi)
      fun α hα ↦ hF.apply_add_smul_sub_le_of_tendsto hx₀ hbD (fun n ↦ (hu (φ n)).2) hlim hFlim hα
    exact absurd (hm _ ⟨hAc.add_smul_sub_mem hx₀A hbA ⟨hα.1.le, hα.2.le⟩, interior_subset
      (hF.convex.add_smul_sub_mem_interior_of_mem_closure hx₀ hbD hα.1.le hα.2)⟩) (not_le.2 hlt)

/-- **Minimization of a Legendre function over a closed convex set** [LS, Theorem 26.15 (a)]. In
finite dimension, if `F` has a minimizer over its domain `D`, then for every closed convex set `A`
meeting the interior of `D`, `F` has a unique minimizer over `A ∩ D`. -/
theorem existsUnique_isMinOn_inter [FiniteDimensional ℝ E] (hA : IsClosed A) (hAc : Convex ℝ A)
    (hAD : (A ∩ interior D).Nonempty) {y₀ : E} (hy₀ : y₀ ∈ D) (hmin : IsMinOn F D y₀) :
    ∃! y, y ∈ A ∩ D ∧ IsMinOn F (A ∩ D) y := by
  obtain ⟨y, hy, hymin⟩ := hF.exists_isMinOn_inter hA hAc hAD hy₀ hmin
  refine ⟨y, ⟨hy, hymin⟩, fun y' ⟨hy', hy'min⟩ ↦ ?_⟩
  -- Both minimizers are interior, where `F` is strictly convex.
  have hi := hF.mem_interior_of_isMinOn_inter hAc hAD hy hymin
  have hi' := hF.mem_interior_of_isMinOn_inter hAc hAD hy' hy'min
  have hsub : A ∩ interior D ⊆ A ∩ D := inter_subset_inter_right A interior_subset
  exact (hF.strictConvexOn.subset inter_subset_right (hAc.inter hF.convex.interior)).eq_of_isMinOn
    (hy'min.of_subset hsub) (hymin.of_subset hsub) ⟨hy'.1, hi'⟩ ⟨hy.1, hi⟩

/-- **The constrained minimizer is a Bregman projection** [LS, Theorem 26.15 (b)]. If `y₀`
minimizes `F` over its domain, then on every set `S`, the minimizers of the Bregman divergence
`D_F(·, y₀)` are the minimizers of `F`. -/
theorem isMinOn_bregDiv_iff {y₀ : E} (hy₀ : y₀ ∈ D) (hmin : IsMinOn F D y₀) {S : Set E} :
    IsMinOn (fun z ↦ bregDiv F z y₀ (fderiv ℝ F y₀)) S y ↔ IsMinOn F S y := by
  simp [hF.fderiv_eq_zero_of_isMinOn hy₀ hmin, bregDiv, isMinOn_iff]

/-! ### Bregman projections -/

/-- The Bregman divergence `D_F(·, y) = F - F y - J (· - y)` of a Legendre function, for any
linear map `J`, is Legendre with the same domain. -/
protected theorem bregDiv (y : E) (J : E →L[ℝ] ℝ) : IsLegendre (fun x ↦ bregDiv F x y J) D := by
  convert (hF.add_linear (-J)).add_const (J y - F y) using 1
  ext x
  simp only [bregDiv, map_sub, neg_apply]
  ring

/-- **Bregman projections onto closed convex sets** [LS, Section 26.6, Theorem 26.15]. In finite
dimension, for a point `y` of the interior of the domain `D` and a closed convex set `A` meeting
the interior of `D`, the Bregman divergence `D_F(·, y)` has a unique minimizer over `A ∩ D`. -/
theorem existsUnique_isMinOn_bregDiv [FiniteDimensional ℝ E] (hA : IsClosed A) (hAc : Convex ℝ A)
    (hAD : (A ∩ interior D).Nonempty) (hy : y ∈ interior D) :
    ∃! z, z ∈ A ∩ D ∧ IsMinOn (fun w ↦ bregDiv F w y (fderiv ℝ F y)) (A ∩ D) z :=
  (hF.bregDiv y (fderiv ℝ F y)).existsUnique_isMinOn_inter hA hAc hAD
    (interior_subset hy) (isMinOn_iff.2 fun w hw ↦ by
      have := hF.add_fderiv_apply_sub_le hy hw
      simp only [bregDiv, sub_self, map_zero]
      linarith)

/-- Bregman projections onto `A ∩ D`, for a convex set `A` meeting the interior of the domain `D`,
lie in the interior of `D`. -/
theorem mem_interior_of_isMinOn_bregDiv {J : E →L[ℝ] ℝ} {z : E} (hAc : Convex ℝ A)
    (hAD : (A ∩ interior D).Nonempty) (hz : z ∈ A ∩ D)
    (hmin : IsMinOn (fun w ↦ bregDiv F w y J) (A ∩ D) z) : z ∈ interior D :=
  (hF.bregDiv y J).mem_interior_of_isMinOn_inter hAc hAD hz hmin

/-- **Generalized Pythagorean inequality for Legendre functions** [LS, Exercise 26.13 (a)]. If `z`
is a Bregman projection of `y` onto `A ∩ D`, for a convex set `A` meeting the interior of the
domain `D`, then `D_F(x, z) + D_F(z, y) ≤ D_F(x, y)` for every `x ∈ A ∩ D`, with the derivative
of `F` at the interior point `z`. -/
theorem bregDiv_add_bregDiv_le {J : E →L[ℝ] ℝ} {z : E} (hAc : Convex ℝ A)
    (hAD : (A ∩ interior D).Nonempty) (hx : x ∈ A ∩ D) (hz : z ∈ A ∩ D)
    (hmin : IsMinOn (fun w ↦ bregDiv F w y J) (A ∩ D) z) :
    bregDiv F x z (fderiv ℝ F z) + bregDiv F z y J ≤ bregDiv F x y J :=
  bregDiv_add_bregDiv_le_of_isMinOn (hAc.inter hF.convex) hx hz hmin
    (hF.hasFDerivAt (hF.mem_interior_of_isMinOn_bregDiv hAc hAD hz hmin)).hasFDerivWithinAt

end IsLegendre

/-- The function `x ↦ x log x`, the one-dimensional unnormalized negative entropy, is Legendre
with domain `[0, ∞)` [LS, Example 26.11]: its derivative `log x + 1` tends to `-∞` at `0`. -/
theorem isLegendre_mul_log : IsLegendre (fun x : ℝ ↦ x * Real.log x) (Ici 0) where
  convexOn := Real.convexOn_mul_log
  nonempty_interior := ⟨1, by simp⟩
  differentiableOn x hx := by
    rw [interior_Ici] at hx
    exact (Real.hasDerivAt_mul_log (ne_of_gt hx)).differentiableAt.differentiableWithinAt
  strictConvexOn := by
    rw [interior_Ici]
    exact Real.strictConvexOn_mul_log.subset Ioi_subset_Ici_self (convex_Ioi 0)
  tendsto_norm_fderiv x hx := by
    rw [interior_Ici, frontier_Ioi, mem_singleton_iff] at hx
    subst hx
    rw [interior_Ici]
    refine (tendsto_abs_atBot_atTop.comp
      (tendsto_atBot_add_const_right _ 1 Real.tendsto_log_nhdsGT_zero)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Function.comp_apply, ← norm_deriv_eq_norm_fderiv,
      (Real.hasDerivAt_mul_log (ne_of_gt hy)).deriv, Real.norm_eq_abs]

end LMLExplore
