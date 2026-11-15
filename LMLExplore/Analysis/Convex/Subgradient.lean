/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.FDeriv
public import LMLExplore.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Convex.Extrema
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Convex.SubgradientImage

/-!
# Subgradients within a set: convexity, existence and Lipschitz functions

This file relates the subgradients within a set of LML's `HasSubgradientWithinAt` to convexity
and to Lipschitz continuity, for real functions on a real normed space `E` with subgradients in
the dual `E →L[ℝ] ℝ` [Ora, Theorems 2.30 and 4.21, Lemma 4.20]:

* for a function convex on `s`, a subgradient within a neighbourhood of `x` in `s` is a
  subgradient within all of `s`: convexity turns the local supporting inequality into a global
  one;
* in finite dimension, a function convex on `s` has a subgradient within `s` at every interior
  point of `s`, so on an open convex set convexity is the existence of subgradients at every
  point (the converse direction is `Convex.convexOn_of_hasSubgradientWithinAt`, [Ora, Theorem
  2.21]);
* a function `L`-Lipschitz on a neighbourhood of `x` has only subgradients of dual norm at most
  `L` at `x`, and conversely a function with a subgradient of dual norm at most `L` at every
  point of `s` is `L`-Lipschitz on `s`. On an open set where subgradients exist, `L`-Lipschitz
  continuity is thus the bound `‖g‖ ≤ L` on all subgradients.

The Lipschitz characterization is how bounds on the losses of online convex optimization become
bounds `‖g_t‖ ≤ L` on the subgradients that enter the regret bounds, and the existence of
subgradients is what lets a convex loss be linearized at every play in the interior of the
feasible set. The existence statement is transferred from Tau Ceti's
`ConvexOn.exists_forall_add_inner_le`, stated in finite-dimensional inner product spaces, through
a continuous linear equivalence with a Euclidean space.

## Main statements

* `ConvexOn.hasSubgradientWithinAt_of_mem_nhdsWithin`: local subgradients of a convex function
  are global.
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

* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Theorems 2.30 and 4.21, Lemma 4.20.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s t : Set E} {f : E → ℝ}
  {g : E →L[ℝ] ℝ} {x : E} {L : ℝ≥0}

/-- The points `x + τ • v` lie in a neighbourhood `u` of `x` for all small enough `τ > 0`. -/
private theorem eventually_add_smul_mem {u : Set E} (hu : u ∈ 𝓝 x) (v : E) :
    ∀ᶠ τ in 𝓝[>] (0 : ℝ), x + τ • v ∈ u := by
  have hlim : Tendsto (fun τ : ℝ ↦ x + τ • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using ((by fun_prop : Continuous fun τ : ℝ ↦ x + τ • v).tendsto 0).mono_left
      nhdsWithin_le_nhds
  exact hlim.eventually hu

namespace ConvexOn

/-- **Local subgradients of a convex function are global.** If `f` is convex on `s` and `g` is a
subgradient of `f` at `x ∈ s` within a neighbourhood `t` of `x` in `s`, then `g` is a subgradient
of `f` within `s` at `x`. -/
theorem hasSubgradientWithinAt_of_mem_nhdsWithin (hf : ConvexOn ℝ s f) (hx : x ∈ s)
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
  have := hmin hy
  simp only [mem_ofPred_eq, Pi.sub_apply] at this
  rw [map_sub]
  linarith

/-- **Subgradients exist in the interior**. In a finite-dimensional real
normed space, a function convex on `s` has a subgradient within `s` at every interior point of
`s`. -/
theorem exists_hasSubgradientWithinAt_of_mem_interior [FiniteDimensional ℝ E]
    (hf : ConvexOn ℝ s f) (hx : x ∈ interior s) :
    ∃ g : E →L[ℝ] ℝ, HasSubgradientWithinAt f g s x := by
  -- Transport `f` to a Euclidean space, where Tau Ceti's supporting hyperplane theorem applies on
  -- the open set corresponding to `interior s`.
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hΩ : IsOpen (e.symm ⁻¹' interior s) := isOpen_interior.preimage e.symm.continuous
  have hu : ConvexOn ℝ (e.symm ⁻¹' interior s) (f ∘ e.symm) :=
    (hf.subset interior_subset hf.1.interior).comp_linearMap
      (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →ₗ[ℝ] E)
  obtain ⟨p, hp⟩ := hu.exists_forall_add_inner_le hΩ (x := e x) (by simpa using hx)
  -- The supporting slope `p` gives a subgradient within `interior s`, hence within `s`.
  refine ⟨(innerSL ℝ p).comp (e : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
    hf.hasSubgradientWithinAt_of_mem_nhdsWithin (interior_subset hx)
      (mem_nhdsWithin_of_mem_nhds (isOpen_interior.mem_nhds hx)) ?_⟩
  refine hasSubgradientWithinAt_iff_le.2 fun z hz ↦ ?_
  simpa [real_inner_comm] using hp (e z) (by simpa using hz)

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
    obtain ⟨τ, hτs, hτ⟩ := ((eventually_add_smul_mem hs v).and self_mem_nhdsWithin).exists
    have hτ : 0 < τ := Set.mem_Ioi.1 hτ
    have h₁ := hasSubgradientWithinAt_iff_le.1 hg _ hτs
    have h₂ := hf.le_add_mul hτs (mem_of_mem_nhds hs)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h₁
    rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg hτ.le] at h₂
    refine le_of_mul_le_mul_left ?_ hτ
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ L.2 fun v ↦ abs_le.2 ⟨?_, key v⟩
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
