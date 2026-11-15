/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Subgradients of continuous convex functions

A real function that is convex and continuous on an open set `s` of a real topological vector space
(for instance a real normed space) has a subgradient within `s` at every point of `s`, in the sense
of LML's `HasSubgradientWithinAt`. No finite dimension and no local convexity are needed: the proof
separates the point `(x, f x)` from the strict epigraph `{(y, t) | y ∈ s, f y < t}`, which is open
by continuity and convex by convexity, with the geometric Hahn–Banach theorem
`geometric_hahn_banach_open_point`, and reads the subgradient off the separating functional
[ET, Chapter I, Section 5]. This applies to functions that are continuous on a normed space of any
dimension, such as the distance to a convex set [Ora, Section 12.1]. In finite dimension, Tau
Ceti's `TauCeti.nonempty_subdifferential_of_mem_interior` needs no continuity assumption.

## Main statements

* `ConvexOn.exists_hasSubgradientWithinAt_of_continuousOn`: a function convex and continuous on an
  open set `s` has a subgradient within `s` at every point of `s`.
* `ConvexOn.exists_hasSubgradientWithinAt_univ`: a continuous convex function on the whole space
  has a subgradient at every point.

## References

* [ET] I. Ekeland and R. Témam, *Convex Analysis and Variational Problems*, North-Holland, 1976,
  Chapter I, Section 5.
* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Section 12.1.
-/

public section

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} {f : E → ℝ} {x : E}

/-- **Subgradients of continuous convex functions.** A real function that is convex and continuous
on an open set `s` of a real topological vector space has a subgradient within `s` at every point of
`s`. -/
theorem ConvexOn.exists_hasSubgradientWithinAt_of_continuousOn (hf : ConvexOn ℝ s f)
    (hs : IsOpen s) (hfc : ContinuousOn f s) (hx : x ∈ s) :
    ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x := by
  -- The strict epigraph `A` of `f` on `s` is open and convex, and does not contain `(x, f x)`.
  set A : Set (E × ℝ) := {p | p.1 ∈ s ∧ f p.1 < p.2}
  have hAo : IsOpen A := by
    have hcont : ContinuousOn (fun p : E × ℝ ↦ (f p.1, p.2)) (Prod.fst ⁻¹' s) :=
      (hfc.comp continuousOn_fst fun _ hp ↦ hp).prodMk continuousOn_snd
    exact hcont.isOpen_inter_preimage (hs.preimage continuous_fst)
      (isOpen_lt continuous_fst continuous_snd)
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point (x := (x, f x)) hf.convex_strict_epigraph hAo
    fun h ↦ lt_irrefl _ h.2
  -- Write the separating functional as `(y, t) ↦ ℓ y + t * c`.
  set ℓ : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  set c : ℝ := φ (0, 1)
  have hφ_apply (y : E) (t : ℝ) : φ (y, t) = ℓ y + t * c := by
    have : ((y, t) : E × ℝ) = (y, 0) + t • ((0, 1) : E × ℝ) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply]
  -- The vertical coefficient is negative, since `(x, f x + 1)` lies in `A`.
  have hc : 0 < -c := by
    have := hφ (x, f x + 1) ⟨hx, by linarith⟩
    rw [hφ_apply, hφ_apply] at this
    linarith
  refine ⟨(-c)⁻¹ • ℓ, hasSubgradientWithinAt_iff_le.2 fun y hy ↦ ?_⟩
  rw [FunLike.coe_smul, Pi.smul_apply, map_sub, smul_eq_mul]
  refine le_of_forall_gt_imp_ge_of_dense fun t ht ↦ ?_
  have := hφ (y, t) ⟨hy, ht⟩
  rw [hφ_apply, hφ_apply] at this
  have : (-c)⁻¹ * (ℓ y - ℓ x) < t - f x := by
    rw [inv_mul_lt_iff₀ hc]
    linarith
  linarith

/-- **Subgradients of continuous convex functions on the whole space.** A continuous convex
function on a real topological vector space has a subgradient at every point. -/
theorem ConvexOn.exists_hasSubgradientWithinAt_univ (hf : ConvexOn ℝ univ f) (hfc : Continuous f)
    (x : E) : ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g univ x :=
  hf.exists_hasSubgradientWithinAt_of_continuousOn isOpen_univ hfc.continuousOn (mem_univ x)
