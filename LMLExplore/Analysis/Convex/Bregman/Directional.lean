/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# Bregman divergences with directional derivatives

A convex function need not be differentiable, but along every segment `[y, x]` of its domain it
has a one-sided directional derivative
`∇_{x - y} F(y) = lim_{h → 0⁺} (F (y + h • (x - y)) - F y) / h`, in `[-∞, ∞)`, since the slopes
of a convex function decrease to it. [LS, Section 26.3] defines the
Bregman divergence of a convex function with it, `D_F(x, y) = F x - F y - ∇_{x - y} F(y)`, which
is the Bregman divergence `bregDiv F x y F'` whenever `F` has a derivative `F'` within a set
containing the segment. This is the divergence in which the regret of follow the regularized
leader with a convex potential is stated [LS, Theorem 28.5], with no differentiability assumption.

The directional derivative is Mathlib's line derivative within the segment,
`lineDerivWithin ℝ F (segment ℝ y x) y (x - y)`: its points `y + t • (x - y)` with `t ∈ [0, 1]`
are the points of the segment, so it is one-sided.

At a minimizer `a` over a set `K` of `c ↦ L c + F c`, for a linear `L` and a function `F` convex
on `K`, the slopes of `F` from `a` towards a point `b` with `[a, b] ⊆ K` are bounded below by
`-L (b - a)`, so the directional derivative is finite and at least `-L (b - a)`. The increase of
the function from `a` to `b` is then at least `D_F(b, a)`, as for differentiable `F`
(`LMLExplore.bregDiv_le_sub_of_isMinOn`).

## Main definitions

* `LMLExplore.dirBregDiv F x y`: the Bregman divergence `F x - F y - ∇_{x - y} F(y)` with the
  one-sided directional derivative of `F` at `y` towards `x` [LS, Section 26.3].

## Main statements

* `ConvexOn.hasDerivWithinAt_sInf_slope_of_bddBelow`: a convex function on `[x, b)` whose slopes
  at `x` are bounded below has the right derivative at `x` given by the infimum of the slopes.
* `LMLExplore.HasLineDerivWithinAt.dirBregDiv_eq`: if `F` has the directional derivative `d` at
  `y` towards `x`, then `D_F(x, y) = F x - F y - d`.
* `LMLExplore.HasFDerivWithinAt.dirBregDiv_eq_bregDiv`: for `F` with derivative `F'` within a
  set containing `[y, x]`, `D_F(x, y) = bregDiv F x y F'`.
* `LMLExplore.dirBregDiv_self`: `D_F(x, x) = 0`.
* `ConvexOn.dirBregDiv_nonneg`: the divergence of a convex function is nonnegative where the
  directional derivative exists.
* `ConvexOn.exists_le_hasLineDerivWithinAt_segment`: a convex function whose increments from `a`
  towards `b` are at least `c` times the step has a directional derivative at `a` towards `b`, at
  least `c`.
* `ConvexOn.dirBregDiv_le_sub_of_isMinOn`: at a minimizer `a` of `c ↦ L c + F c` over `K`, for `F`
  convex on `K` and `[a, b] ⊆ K`, `D_F(b, a) ≤ L b + F b - (L a + F a)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.3 and Theorem 28.5.
-/

public section

open Set Filter
open scoped Topology

section Real

/-- A function convex on a set containing `[x, b)`, with `x < b`, whose slopes at `x` are bounded
below on `(x, b)`, has at `x` the right derivative `sInf (slope f x '' Ioo x b)`, the infimum of
these slopes. -/
theorem ConvexOn.hasDerivWithinAt_sInf_slope_of_bddBelow {S : Set ℝ} {f : ℝ → ℝ} {x b : ℝ}
    (hf : ConvexOn ℝ S f) (hxb : x < b) (hS : Ico x b ⊆ S)
    (hbdd : BddBelow (slope f x '' Ioo x b)) :
    HasDerivWithinAt f (sInf (slope f x '' Ioo x b)) (Ioi x) x := by
  refine (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).2 ?_
  have h : Ioo x b ⊆ {y | y ∈ S ∧ x < y} := fun z hz ↦ ⟨hS ⟨hz.1.le, hz.2⟩, hz.1⟩
  exact ((hf.monotoneOn_slope_gt (hS ⟨le_rfl, hxb⟩)).mono h).tendsto_nhdsWithin_Ioo_right
    (nonempty_Ioo.2 hxb) hbdd

end Real

namespace LMLExplore

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} {F : E → ℝ} {a b x y : E}

/-- The **Bregman divergence with directional derivatives** [LS, Section 26.3] of `F` between
`x` and `y`: `F x - F y - ∇_{x - y} F(y)`, where `∇_{x - y} F(y)` is the one-sided directional
derivative `lim_{h → 0⁺} (F (y + h • (x - y)) - F y) / h` of `F` at `y` towards `x`, Mathlib's line
derivative within the segment `[y, x]`. It is defined for every function, and is the Bregman
divergence `bregDiv F x y F'` when `F` has a derivative `F'` within a set containing `[y, x]`
(`HasFDerivWithinAt.dirBregDiv_eq_bregDiv`). Where the directional derivative does not exist, for
example where a convex function has directional derivative `-∞`, the line derivative takes the
junk value `0`. -/
noncomputable def dirBregDiv (F : E → ℝ) (x y : E) : ℝ :=
  F x - F y - lineDerivWithin ℝ F (segment ℝ y x) y (x - y)

/-- The definition of `dirBregDiv` with Mathlib's line derivative within the segment. -/
lemma dirBregDiv_def (F : E → ℝ) (x y : E) :
    dirBregDiv F x y = F x - F y - lineDerivWithin ℝ F (segment ℝ y x) y (x - y) := (rfl)

/-- The parameters `t ∈ [0, 1]` give points `y + t • (x - y)` of the segment `[y, x]`. -/
lemma Icc_subset_preimage_segment (x y : E) :
    Icc (0 : ℝ) 1 ⊆ (fun t : ℝ ↦ y + t • (x - y)) ⁻¹' segment ℝ y x := fun t ht ↦ by
  rw [mem_preimage, segment_eq_image']
  exact mem_image_of_mem _ ht

/-- The Bregman divergence of `F` from a point to itself is `0`. -/
@[simp]
lemma dirBregDiv_self (F : E → ℝ) (x : E) : dirBregDiv F x x = 0 := by
  simp [dirBregDiv_def, lineDerivWithin]

/-- If `F` has the directional derivative `d` at `y` towards `x` within the segment `[y, x]`, then
`D_F(x, y) = F x - F y - d`. -/
lemma _root_.HasLineDerivWithinAt.dirBregDiv_eq {d : ℝ}
    (h : HasLineDerivWithinAt ℝ F d (segment ℝ y x) y (x - y)) :
    dirBregDiv F x y = F x - F y - d := by
  have hu : UniqueDiffWithinAt ℝ ((fun t : ℝ ↦ y + t • (x - y)) ⁻¹' segment ℝ y x) 0 :=
    (uniqueDiffOn_Icc zero_lt_one 0 (left_mem_Icc.2 zero_le_one)).mono
      (Icc_subset_preimage_segment x y)
  -- `HasLineDerivWithinAt` and `lineDerivWithin` are by definition the derivative of
  -- `t ↦ F (y + t • (x - y))` within the preimage of the segment
  rw [dirBregDiv_def, lineDerivWithin, HasDerivWithinAt.derivWithin h hu]

/-- Let `F` be convex on `K` with `[a, b] ⊆ K`. The function `t ↦ F (a + t • (b - a))` is convex
on `[0, 1]`. -/
lemma _root_.ConvexOn.convexOn_Icc_comp_segment (hF : ConvexOn ℝ K F)
    (h_seg : segment ℝ a b ⊆ K) : ConvexOn ℝ (Icc 0 1) fun t : ℝ ↦ F (a + t • (b - a)) := by
  have h_eq : (fun t : ℝ ↦ F (a + t • (b - a))) = F ∘ AffineMap.lineMap a b := by
    ext t
    rw [Function.comp_apply, AffineMap.lineMap_apply_module', add_comm]
  rw [h_eq]
  exact (hF.comp_affineMap (AffineMap.lineMap a b)).subset
    (fun t ht ↦ h_seg (lineMap_mem_segment ℝ a b ht)) (convex_Icc 0 1)

/-- **Nonnegativity of the Bregman divergence of a convex function.** Let `F` be convex on `K`,
with `[y, x] ⊆ K`, and let `F` have a directional derivative at `y` towards `x`. Then
`0 ≤ D_F(x, y)`. -/
theorem _root_.ConvexOn.dirBregDiv_nonneg (hF : ConvexOn ℝ K F) (h_seg : segment ℝ y x ⊆ K)
    (hd : LineDifferentiableWithinAt ℝ F (segment ℝ y x) y (x - y)) : 0 ≤ dirBregDiv F x y := by
  have hd' := hd.hasLineDerivWithinAt
  rw [hd'.dirBregDiv_eq, sub_nonneg]
  -- the directional derivative is the right derivative at `0` of the convex function
  -- `g t = F (y + t • (x - y))` on `[0, 1]`, hence at most its slope `F x - F y` on `[0, 1]`
  have hg : HasDerivWithinAt (fun t : ℝ ↦ F (y + t • (x - y)))
      (lineDerivWithin ℝ F (segment ℝ y x) y (x - y)) (Ioi 0) 0 :=
    hasDerivWithinAt_Ioi_iff_Ici.2 (((HasDerivWithinAt.mono hd'
      (Icc_subset_preimage_segment x y))).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE zero_lt_one))
  have := (hF.convexOn_Icc_comp_segment h_seg).le_slope_of_hasDerivWithinAt_Ioi
    (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_lt_one hg
  simpa [slope_def_field] using this

/-- **Existence of directional derivatives of convex functions.** Let `F` be convex on `K` with
`[a, b] ⊆ K`, and let its increments from `a` towards `b` be at least `c` times the step:
`c * t ≤ F (a + t • (b - a)) - F a` for `t ∈ (0, 1)`. Then `F` has a directional derivative
`d ≥ c` at `a` towards `b` within the segment `[a, b]`. -/
theorem _root_.ConvexOn.exists_le_hasLineDerivWithinAt_segment (hF : ConvexOn ℝ K F)
    (h_seg : segment ℝ a b ⊆ K) {c : ℝ}
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, c * t ≤ F (a + t • (b - a)) - F a) :
    ∃ d, c ≤ d ∧ HasLineDerivWithinAt ℝ F d (segment ℝ a b) a (b - a) := by
  set g : ℝ → ℝ := fun t ↦ F (a + t • (b - a)) with hg_def
  rcases eq_or_ne a b with rfl | hab
  · -- along a constant direction `F` is constant, and `c ≤ 0`
    refine ⟨0, ?_, ?_⟩
    · have := hc (1 / 2) ⟨by norm_num, by norm_num⟩
      simp only [sub_self, smul_zero, add_zero] at this
      linarith
    · rw [HasLineDerivWithinAt]
      simp only [sub_self, smul_zero, add_zero]
      exact hasDerivWithinAt_const _ _ _
  -- the slopes of `g` at `0` on `(0, 1)` are at least `c`
  have h_slope : ∀ s ∈ slope g 0 '' Ioo 0 1, c ≤ s := by
    rintro _ ⟨t, ht, rfl⟩
    rw [slope_def_field, sub_zero, le_div_iff₀ ht.1]
    simpa [hg_def] using hc t ht
  have h_ne : (slope g 0 '' Ioo 0 1).Nonempty := (nonempty_Ioo.2 zero_lt_one).image _
  refine ⟨_, le_csInf h_ne h_slope, ?_⟩
  -- for `a ≠ b` the parameters of the segment are exactly `[0, 1]`
  have h_pre : (fun t : ℝ ↦ a + t • (b - a)) ⁻¹' segment ℝ a b = Icc 0 1 := by
    rw [segment_eq_image']
    exact ((add_right_injective a).comp (smul_left_injective ℝ (sub_ne_zero.2 hab.symm))
      ).preimage_image _
  have h := (hF.convexOn_Icc_comp_segment h_seg).hasDerivWithinAt_sInf_slope_of_bddBelow
    zero_lt_one Ico_subset_Icc_self ⟨c, h_slope⟩
  rw [HasLineDerivWithinAt, h_pre]
  exact (hasDerivWithinAt_Ioi_iff_Ici.1 h).mono Icc_subset_Ici_self

/-- **The increase from a constrained minimizer is at least the Bregman divergence** of a convex
function. Let `a` minimize over `K` the function `c ↦ L c + F c`, where `L` is linear and `F` is
convex on `K`. If the segment from `a` to `b` lies in `K`, then this function increases from `a`
to `b` by at least the Bregman divergence `D_F(b, a)` with the directional derivative of `F`.
No derivative of `F` is assumed: the directional derivative of `F` at `a` towards `b` exists and
is at least `-L (b - a)`. -/
theorem _root_.ConvexOn.dirBregDiv_le_sub_of_isMinOn (hF : ConvexOn ℝ K F) (L : E →ₗ[ℝ] ℝ)
    (h_seg : segment ℝ a b ⊆ K) (ha : IsMinOn (fun c ↦ L c + F c) K a) :
    dirBregDiv F b a ≤ L b + F b - (L a + F a) := by
  -- by minimality, the increments of `F` from `a` towards `b` are at least `-L (b - a)` times
  -- the step
  obtain ⟨d, hd, hF'⟩ := hF.exists_le_hasLineDerivWithinAt_segment h_seg (c := -L (b - a))
    fun t ht ↦ by
      have h_mem : a + t • (b - a) ∈ K := h_seg (by
        rw [segment_eq_image']
        exact mem_image_of_mem _ (Ioo_subset_Icc_self ht))
      have := isMinOn_iff.1 ha _ h_mem
      simp only [map_add, map_smul, smul_eq_mul] at this
      linarith
  rw [hF'.dirBregDiv_eq]
  have : L (b - a) = L b - L a := map_sub L b a
  linarith

end Module

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ}
  {F' : E →L[ℝ] ℝ} {x y : E}

/-- For a function `F` with derivative `F'` within a set `K` at `y`, and `[y, x] ⊆ K`, the Bregman
divergence with the directional derivative is the Bregman divergence with the derivative:
`D_F(x, y) = F x - F y - F' (x - y)`. -/
theorem _root_.HasFDerivWithinAt.dirBregDiv_eq_bregDiv (hF : HasFDerivWithinAt F F' K y)
    (h_seg : segment ℝ y x ⊆ K) : dirBregDiv F x y = bregDiv F x y F' := by
  rw [((hF.hasLineDerivWithinAt (x - y)).mono h_seg).dirBregDiv_eq, bregDiv]

end NormedSpace

end LMLExplore
