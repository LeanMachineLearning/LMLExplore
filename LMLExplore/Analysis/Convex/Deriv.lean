/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Convex.Deriv

/-!
# One-sided derivatives of convex functions

A convex function on `ℝ` has, at each point of its domain from which its slopes to the right are
bounded below, a right derivative: the infimum of these slopes. Mathlib proves this at interior
points (`ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior`); this file proves it at a left
endpoint of the domain. Along a segment `[a, b]` of the domain of a convex function `F` on a real
vector space, `t ↦ F (a + t • (b - a))` is convex on `[0, 1]`, so that `F` has a one-sided
directional derivative at `a` towards `b` as soon as its increments from `a` are bounded below by a
multiple of the step.

## Main statements

* `ConvexOn.hasDerivWithinAt_sInf_slope_of_bddBelow`: a convex function on `[x, b)` whose slopes
  at `x` are bounded below has the right derivative at `x` given by the infimum of the slopes.
* `ConvexOn.comp_lineMap_Icc`: a convex function along a segment of its domain is convex in the
  parameter `t ∈ [0, 1]`.
* `ConvexOn.exists_le_hasLineDerivWithinAt_segment`: a convex function whose increments from `a`
  towards `b` are at least `c` times the step has a directional derivative at `a` towards `b`,
  within the segment `[a, b]`, at least `c`.
-/

public section

open Set

/-- A function convex on a set containing `[x, b)`, with `x < b`, whose slopes at `x` are bounded
below on `(x, b)`, has at `x` the right derivative `sInf (slope f x '' Ioo x b)`, the infimum of
these slopes. This is the companion at a boundary point of Mathlib's
`ConvexOn.hasDerivWithinAt_sInf_slope_of_mem_interior`, whose proof it follows: the slopes are
monotone on `(x, b)`, hence converge to their infimum at `x`. -/
theorem ConvexOn.hasDerivWithinAt_sInf_slope_of_bddBelow {S : Set ℝ} {f : ℝ → ℝ} {x b : ℝ}
    (hf : ConvexOn ℝ S f) (hxb : x < b) (hS : Ico x b ⊆ S)
    (hbdd : BddBelow (slope f x '' Ioo x b)) :
    HasDerivWithinAt f (sInf (slope f x '' Ioo x b)) (Ioi x) x := by
  refine (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).2 ?_
  have h : Ioo x b ⊆ {y | y ∈ S ∧ x < y} := fun z hz ↦ ⟨hS ⟨hz.1.le, hz.2⟩, hz.1⟩
  exact ((hf.monotoneOn_slope_gt (hS ⟨le_rfl, hxb⟩)).mono h).tendsto_nhdsWithin_Ioo_right
    (nonempty_Ioo.2 hxb) hbdd

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} {F : E → ℝ} {a b : E}

/-- Let `F` be convex on `K` with `[a, b] ⊆ K`. The function `t ↦ F (a + t • (b - a))`, that is
`F` composed with the line map from `a` to `b`, is convex on `[0, 1]`. -/
lemma ConvexOn.comp_lineMap_Icc (hF : ConvexOn ℝ K F) (h_seg : segment ℝ a b ⊆ K) :
    ConvexOn ℝ (Icc 0 1) fun t : ℝ ↦ F (a + t • (b - a)) := by
  have h_eq : (fun t : ℝ ↦ F (a + t • (b - a))) = F ∘ AffineMap.lineMap a b := by
    ext t
    rw [Function.comp_apply, AffineMap.lineMap_apply_module', add_comm]
  rw [h_eq]
  exact (hF.comp_affineMap (AffineMap.lineMap a b)).subset
    (fun t ht ↦ h_seg (lineMap_mem_segment ℝ a b ht)) (convex_Icc 0 1)

/-- **Existence of directional derivatives of convex functions.** Let `F` be convex on `K` with
`[a, b] ⊆ K`, and let its increments from `a` towards `b` be at least `c` times the step:
`c * t ≤ F (a + t • (b - a)) - F a` for `t ∈ (0, 1)`. Then `F` has a directional derivative
`d ≥ c` at `a` towards `b` within the segment `[a, b]`. -/
theorem ConvexOn.exists_le_hasLineDerivWithinAt_segment (hF : ConvexOn ℝ K F)
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
    · rw [LMLExplore.hasLineDerivWithinAt_iff_hasDerivWithinAt]
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
  have h := (hF.comp_lineMap_Icc h_seg).hasDerivWithinAt_sInf_slope_of_bddBelow
    zero_lt_one Ico_subset_Icc_self ⟨c, h_slope⟩
  rw [LMLExplore.hasLineDerivWithinAt_iff_hasDerivWithinAt, h_pre]
  exact (hasDerivWithinAt_Ioi_iff_Ici.1 h).mono Icc_subset_Ici_self
