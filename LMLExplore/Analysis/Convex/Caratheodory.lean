/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Carathéodory's theorem with weights in a standard simplex

In a finite-dimensional vector space over an ordered field `𝕜`, Carathéodory's theorem
(`eq_pos_convex_span_of_mem_convexHull`) writes every point of the convex hull of `s` as a
positive convex combination of affinely independent points of `s`, so of at most `finrank + 1`
of them. Padding with zero weights gives a convex combination of exactly `finrank + 1` points of
`s`, with weights in Mathlib's standard simplex `StdSimplex 𝕜 (Fin (finrank + 1))`.

This is the step behind the compactness of the convex hull of a compact set in finite dimension,
Tau Ceti's `IsCompact.convexHull`: the convex hull is the image of the compact set
`StdSimplex 𝕜 (Fin (finrank + 1)) × s ^ (finrank + 1)` by the continuous map
`(w, z) ↦ ∑ i, w i • z i`.

## Main statements

* `LMLExplore.exists_stdSimplex_fin_of_mem_convexHull`: in a finite-dimensional space, every
  point of the convex hull of `s` is a convex combination of `finrank + 1` points of `s`.

The proof follows `isCompact_convexHull` of the `colt-2026-83` project (Rémy Degenne,
<https://github.com/RemyDegenne/colt-2026-83>).
-/

public section

open Convexity

namespace LMLExplore

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

end LMLExplore
