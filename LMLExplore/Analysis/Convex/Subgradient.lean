/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Basic
public import LMLExplore.Analysis.Convex.FDeriv
public import LMLExplore.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Convex.Extrema
public import Mathlib.Analysis.Convex.Function
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Subgradients within a set: existence, convexity and Lipschitz functions

This file relates the subgradients within a set of LML's `HasSubgradientWithinAt` to continuity,
convexity and Lipschitz continuity, for real functions with subgradients in the dual `E →L[ℝ] ℝ`.

A real function that is convex and continuous on an open set `s` of a real topological vector space
(for instance a real normed space) has a subgradient within `s` at every point of `s`. No finite
dimension and no local convexity are needed: the proof separates the point `(x, f x)` from the
strict epigraph `{(y, t) | y ∈ s, f y < t}`, which is open by continuity and convex by convexity,
with the geometric Hahn–Banach theorem `geometric_hahn_banach_open_point`, and reads the
subgradient off the separating functional [ET, Chapter I, Section 5]. This applies to functions
that are continuous on a normed space of any dimension, such as the distance to a convex set
[Ora, Section 12.1]. In the same generality, for a function convex on `s`, a subgradient
within a neighbourhood of `x` in `s` is a subgradient within all of `s`: convexity turns the local
supporting inequality into a global one.

On a real normed space `E` [Ora, Theorems 2.30 and 4.21, Lemma 4.20]:

* in finite dimension, a function convex on `s` is continuous on the interior of `s`, so has a
  subgradient within `s` at every interior point of `s`; on an open convex set convexity is thus
  the existence of subgradients at every point (the converse direction is
  `Convex.convexOn_of_hasSubgradientWithinAt`, [Ora, Theorem 2.21]);
* a function `L`-Lipschitz on a neighbourhood of `x` has only subgradients of dual norm at most
  `L` at `x`, and conversely a function with a subgradient of dual norm at most `L` at every
  point of `s` is `L`-Lipschitz on `s`. On an open set where subgradients exist, `L`-Lipschitz
  continuity is thus the bound `‖g‖ ≤ L` on all subgradients.

The Lipschitz characterization is how bounds on the losses of online convex optimization become
bounds `‖g_t‖ ≤ L` on the subgradients that enter the regret bounds, and the existence of
subgradients is what lets a convex loss be linearized at every play in the interior of the
feasible set.

## Main statements

* `ConvexOn.exists_hasSubgradientWithinAt_of_continuousOn`: a function convex and continuous on an
  open set `s` has a subgradient within `s` at every point of `s`.
* `ConvexOn.exists_hasSubgradientWithinAt_univ`: a continuous convex function on the whole space
  has a subgradient at every point.
* `ConvexOn.hasSubgradientWithinAt_of_mem_nhdsWithin`: local subgradients of a convex function
  are global.
* `HasSubgradientWithinAt.apply_sub_le_of_le_add_mul_add_sq`: on a convex set, a subgradient `g`
  at `x` satisfies `g (z - x) ≤ c` whenever `f (x + τ • (z - x)) ≤ f x + τ * c + τ ^ 2 * C` for
  `τ ∈ (0, 1]`.
* `ConvexOn.exists_hasSubgradientWithinAt_of_mem_interior`: in finite dimension, a convex function
  has a subgradient at every interior point.
* `Convex.convexOn_iff_forall_exists_hasSubgradientWithinAt`: on an open convex set in finite
  dimension, convexity is the existence of subgradients everywhere.
* `HasSubgradientWithinAt.norm_le_of_lipschitzOnWith`: the subgradients of an `L`-Lipschitz
  function on a neighbourhood have dual norm at most `L`.
* `LipschitzOnWith.of_forall_exists_hasSubgradientWithinAt`: subgradients of dual norm at most `L`
  everywhere make a function `L`-Lipschitz.
* `IsOpen.lipschitzOnWith_iff_forall_norm_le`,
  `ConvexOn.lipschitzOnWith_iff_forall_norm_le`: the resulting characterizations on open sets.

## References

* [ET] I. Ekeland and R. Témam, *Convex Analysis and Variational Problems*, North-Holland, 1976,
  Chapter I, Section 5.
* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Section 12.1, Theorems 2.30 and 4.21, Lemma 4.20.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

section TopologicalVectorSpace

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

/-- **Local subgradients of a convex function are global.** If `f` is convex on `s` and `g` is a
subgradient of `f` at `x ∈ s` within a neighbourhood `t` of `x` in `s`, then `g` is a subgradient
of `f` within `s` at `x`. -/
theorem ConvexOn.hasSubgradientWithinAt_of_mem_nhdsWithin {t : Set E} {g : E →L[ℝ] ℝ}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (ht : t ∈ 𝓝[s] x) (hg : HasSubgradientWithinAt f g t x) :
    HasSubgradientWithinAt f g s x := by
  -- The subgradient inequality says that `x` minimizes the convex function `f - g` on `t`, hence
  -- locally on `s`, hence globally on `s`.
  have hmin : IsMinOn (f - ⇑g) s x := by
    refine IsMinOn.of_isLocalMinOn_of_convexOn hx ?_ (hf.sub ((g : E →ₗ[ℝ] ℝ).concaveOn hf.1))
    filter_upwards [ht] with y hy
    have := hasSubgradientWithinAt_iff_le.1 hg y hy
    simp only [Pi.sub_apply, map_sub] at this ⊢
    linarith
  refine hasSubgradientWithinAt_iff_le.2 fun y hy ↦ ?_
  have := isMinOn_iff.1 hmin y hy
  simp only [Pi.sub_apply] at this
  rw [map_sub]
  linarith

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- **Subgradients under a quadratic upper bound along a segment.** Let `g` be a subgradient of `f`
within a convex set `s` at `x ∈ s`, and let `z ∈ s`. If `f` grows along the segment from `x` to
`z` at most like `f (x + τ • (z - x)) ≤ f x + τ * c + τ ^ 2 * C` for `τ ∈ (0, 1]`, then
`g (z - x) ≤ c`. For a function that is quadratic along segments, such as a sum of a linear
function and a quadratic form, `c` is its derivative at `x` in the direction `z - x`, so on a
convex set its subgradients at `x` are bounded by its derivative along the directions into the
set. -/
theorem HasSubgradientWithinAt.apply_sub_le_of_le_add_mul_add_sq {g : E →L[ℝ] ℝ} {z : E}
    {c C : ℝ} (hg : HasSubgradientWithinAt f g s x) (hs : Convex ℝ s) (hx : x ∈ s) (hz : z ∈ s)
    (hf : ∀ τ ∈ Ioc (0 : ℝ) 1, f (x + τ • (z - x)) ≤ f x + τ * c + τ ^ 2 * C) :
    g (z - x) ≤ c := by
  -- the subgradient inequality at `x + τ • (z - x)` gives `g (z - x) ≤ c + τ * C`; let `τ → 0⁺`
  have hle (τ : ℝ) (hτ : τ ∈ Ioc (0 : ℝ) 1) : g (z - x) ≤ c + τ * C := by
    have h := hasSubgradientWithinAt_iff_le.1 hg _ (hs.add_smul_sub_mem hx hz ⟨hτ.1.le, hτ.2⟩)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h
    have h' : τ * g (z - x) ≤ τ * (c + τ * C) := by nlinarith [hf τ hτ]
    exact le_of_mul_le_mul_left h' hτ.1
  have hlim : Tendsto (fun τ : ℝ ↦ c + τ * C) (𝓝[>] 0) (𝓝 c) := by
    have h : Tendsto (fun τ : ℝ ↦ c + τ * C) (𝓝 0) (𝓝 (c + 0 * C)) :=
      tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
    rw [zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with τ hτ using hle τ hτ)

end TopologicalVectorSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s t : Set E} {f : E → ℝ}
  {g : E →L[ℝ] ℝ} {x : E} {L : ℝ≥0}

namespace ConvexOn

/-- **Subgradients exist in the interior**. In a finite-dimensional real
normed space, a function convex on `s` has a subgradient within `s` at every interior point of
`s`. -/
theorem exists_hasSubgradientWithinAt_of_mem_interior [FiniteDimensional ℝ E]
    (hf : ConvexOn ℝ s f) (hx : x ∈ interior s) :
    ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x := by
  -- `f` is continuous on the open set `interior s`, so has a subgradient within `interior s`,
  -- which is a neighbourhood of `x` in `s`.
  obtain ⟨g, hg⟩ := (hf.subset interior_subset hf.1.interior)
    |>.exists_hasSubgradientWithinAt_of_continuousOn isOpen_interior hf.continuousOn_interior hx
  exact ⟨g, hf.hasSubgradientWithinAt_of_mem_nhdsWithin (interior_subset hx)
    (mem_nhdsWithin_of_mem_nhds (isOpen_interior.mem_nhds hx)) hg⟩

end ConvexOn

/-- **Convexity is the existence of subgradients**. On an open
convex set `s` of a finite-dimensional real normed space, `f` is convex if and only if it has a
subgradient within `s` at every point of `s`. -/
theorem Convex.convexOn_iff_forall_exists_hasSubgradientWithinAt [FiniteDimensional ℝ E]
    (hs : Convex ℝ s) (hs' : IsOpen s) :
    ConvexOn ℝ s f ↔ ∀ x ∈ s, ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x :=
  ⟨fun hf _ hx ↦ hf.exists_hasSubgradientWithinAt_of_mem_interior (by rwa [hs'.interior_eq]),
    hs.convexOn_of_hasSubgradientWithinAt⟩

/-- **The subgradients of a Lipschitz function are bounded**. If `f` is
`L`-Lipschitz on a neighbourhood `s` of `x`, then every subgradient of `f` within `s` at `x` has
dual norm at most `L`. -/
theorem HasSubgradientWithinAt.norm_le_of_lipschitzOnWith (hg : HasSubgradientWithinAt f g s x)
    (hs : s ∈ 𝓝 x) (hf : LipschitzOnWith L f s) : ‖g‖ ≤ L := by
  -- In each direction `v`, compare the subgradient inequality with the Lipschitz bound at a point
  -- `x + τ • v` of `s` with `τ > 0`.
  have key (v : E) : g v ≤ L * ‖v‖ := by
    have hlim : Tendsto (fun τ : ℝ ↦ x + τ • v) (𝓝[>] 0) (𝓝 x) := by
      simpa using ((by fun_prop : Continuous fun τ : ℝ ↦ x + τ • v).tendsto 0).mono_left
        nhdsWithin_le_nhds
    obtain ⟨τ, hτs, hτ⟩ := ((hlim.eventually hs).and self_mem_nhdsWithin).exists
    have hτ : 0 < τ := Set.mem_Ioi.1 hτ
    have h₁ := hasSubgradientWithinAt_iff_le.1 hg _ hτs
    have h₂ := hf.le_add_mul hτs (mem_of_mem_nhds hs)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h₁
    rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg hτ.le] at h₂
    refine le_of_mul_le_mul_left ?_ hτ
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ L.property fun v ↦ abs_le.2 ⟨?_, key v⟩
  have := key (-v)
  rw [map_neg, norm_neg] at this
  linarith

/-- **Bounded subgradients make a function Lipschitz**. If `f` has, at every
point of `s`, a subgradient within `s` of dual norm at most `L`, then `f` is `L`-Lipschitz on `s`.
Neither convexity nor openness of `s` is needed. -/
protected theorem LipschitzOnWith.of_forall_exists_hasSubgradientWithinAt
    (h : ∀ x ∈ s, ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x ∧ ‖g‖ ≤ L) :
    LipschitzOnWith L f s := by
  refine LipschitzOnWith.of_le_add_mul L fun x hx y hy ↦ ?_
  obtain ⟨g, hg, hgL⟩ := h x hx
  have h₁ := hasSubgradientWithinAt_iff_le.1 hg y hy
  have h₂ : -g (y - x) ≤ L * dist x y := by
    rw [← map_neg, neg_sub, dist_eq_norm]
    exact (g.apply_le_opNorm_mul_norm _).trans (mul_le_mul_of_nonneg_right hgL (norm_nonneg _))
  linarith

/-- **Lipschitz functions are those with bounded subgradients**. On an open set
`s` at each point of which `f` has a subgradient within `s`, `f` is `L`-Lipschitz on `s` if and only
if every subgradient of `f` within `s` at a point of `s` has dual norm at most `L`. -/
theorem IsOpen.lipschitzOnWith_iff_forall_norm_le (hs : IsOpen s)
    (hsub : ∀ x ∈ s, ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x) :
    LipschitzOnWith L f s ↔
      ∀ x ∈ s, ∀ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x → ‖g‖ ≤ L :=
  ⟨fun hf _ hx _ hg ↦ hg.norm_le_of_lipschitzOnWith (hs.mem_nhds hx) hf,
    fun h ↦ .of_forall_exists_hasSubgradientWithinAt fun x hx ↦
      (hsub x hx).imp fun g hg ↦ ⟨hg, h x hx g hg⟩⟩

/-- **Convex Lipschitz functions are those with bounded subgradients**. In
finite dimension, a function `f` convex on an open set `s` is `L`-Lipschitz on `s` if and only if
every subgradient of `f` within `s` at a point of `s` has dual norm at most `L`. -/
theorem ConvexOn.lipschitzOnWith_iff_forall_norm_le [FiniteDimensional ℝ E] (hf : ConvexOn ℝ s f)
    (hs : IsOpen s) :
    LipschitzOnWith L f s ↔
      ∀ x ∈ s, ∀ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x → ‖g‖ ≤ L :=
  hs.lipschitzOnWith_iff_forall_norm_le fun _ hx ↦
    hf.exists_hasSubgradientWithinAt_of_mem_interior (by rwa [hs.interior_eq])

end NormedSpace
