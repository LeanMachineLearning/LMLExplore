/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Compactness of the convex hull of a compact set

In a finite-dimensional real topological vector space, the convex hull of a compact set is
compact. By Carathéodory's theorem, every point of the convex hull of `s` is a convex combination
of `finrank + 1` points of `s`, so the convex hull is the image of the compact set
`StdSimplex ℝ (Fin (finrank + 1)) × s ^ (finrank + 1)` by the continuous map
`(w, z) ↦ ∑ i, w i • z i`. Mathlib proves the case of a finite set,
`Set.Finite.isCompact_convexHull`.

This is the compactness behind the existence of optimal designs: the set of design operators of
a compact set of vectors is the convex hull of the compact set of their rank-one operators.

## Main statements

* `exists_stdSimplex_fin_of_mem_convexHull`: in a finite-dimensional space, every point of the
  convex hull of `s` is a convex combination of `finrank + 1` points of `s`.
* `IsCompact.convexHull`: the convex hull of a compact set in a finite-dimensional real
  topological vector space is compact.

The proof follows `isCompact_convexHull` of the `colt-2026-83` project (Rémy Degenne,
<https://github.com/RemyDegenne/colt-2026-83>).
-/

public section

open Convexity

/-- **Carathéodory's theorem with `finrank + 1` points**: in a finite-dimensional space, every point
of the convex hull of `s` is a convex combination of `finrank + 1` points of `s`. -/
theorem exists_stdSimplex_fin_of_mem_convexHull {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E] {s : Set E}
    {x : E} (hx : x ∈ convexHull 𝕜 s) :
    ∃ (ω : StdSimplex 𝕜 (Fin (Module.finrank 𝕜 E + 1))) (z : Fin (Module.finrank 𝕜 E + 1) → E),
      (∀ i, z i ∈ s) ∧ ∑ i, ω.weights i • z i = x := by
  obtain ⟨x₀, hx₀⟩ := convexHull_nonempty_iff.1 ⟨x, hx⟩
  obtain ⟨κ, _, z, w, hz, hind, hw, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
  -- extend the Carathéodory combination by zero weights, along an embedding `e`
  have hcard : Fintype.card κ ≤ Fintype.card (Fin (Module.finrank 𝕜 E + 1)) :=
    hind.card_le_finrank_succ.trans
      (by rw [Fintype.card_fin]; exact Nat.succ_le_succ (Submodule.finrank_le _))
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let w' := Function.extend e w 0
  have hw'0 : ∀ j ∉ Set.range e, w' j = 0 := fun j hj ↦ Function.extend_apply' _ _ _ hj
  have hw'e : ∀ i, w' (e i) = w i := e.injective.extend_apply _ _
  let ω : StdSimplex 𝕜 (Fin (Module.finrank 𝕜 E + 1)) :=
    { weights := Finsupp.equivFunOnFinite.symm w'
      nonneg := fun j ↦ by
        by_cases hj : j ∈ Set.range e
        · obtain ⟨i, rfl⟩ := hj
          simpa [hw'e] using (hw i).le
        · simp [hw'0 j hj]
      total := by
        rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl, ← hw1]
        exact (Fintype.sum_of_injective e e.injective _ _ hw'0 fun i ↦ (hw'e i).symm).symm }
  refine ⟨ω, Function.extend e z fun _ ↦ x₀, fun j ↦ ?_,
    (Fintype.sum_of_injective e e.injective _ _ (fun j hj ↦ by simp [ω, hw'0 j hj])
      fun i ↦ by simp [ω, hw'e, e.injective.extend_apply]).symm⟩
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    simpa [e.injective.extend_apply] using hz (Set.mem_range_self i)
  · simpa [Function.extend_apply' _ _ _ hj] using hx₀

/-- **The convex hull of a compact set is compact** in a finite-dimensional real topological vector
space. -/
theorem IsCompact.convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E] {s : Set E}
    (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  set n := Module.finrank ℝ E + 1
  let f : StdSimplex ℝ (Fin n) × (Fin n → E) → E := fun p ↦ ∑ i, p.1.weights i • p.2 i
  have hf : Continuous f := continuous_finsetSum _ fun i _ ↦
    ((StdSimplex.continuous_weights_apply ℝ i).comp continuous_fst).smul
      ((continuous_apply i).comp continuous_snd)
  suffices _root_.convexHull ℝ s = f '' (Set.univ ×ˢ Set.univ.pi fun _ ↦ s) from
    this ▸ (isCompact_univ.prod (isCompact_univ_pi fun _ ↦ hs)).image hf
  refine Set.Subset.antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨ω, z, hz, rfl⟩ := exists_stdSimplex_fin_of_mem_convexHull hx
    exact ⟨(ω, z), ⟨Set.mem_univ _, fun i _ ↦ hz i⟩, rfl⟩
  · rintro _ ⟨⟨w, z⟩, ⟨-, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ ↦ w.weights_nonneg i) w.total_of_fintype
      fun i _ ↦ subset_convexHull ℝ s (hz i (Set.mem_univ _))
