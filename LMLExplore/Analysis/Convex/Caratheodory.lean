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

* `IsCompact.convexHull`: the convex hull of a compact set in a finite-dimensional real
  topological vector space is compact.

The proof follows `isCompact_convexHull` of the `colt-2026-83` project (Rémy Degenne,
<https://github.com/RemyDegenne/colt-2026-83>).
-/

public section

open Convexity

/-- **The convex hull of a compact set is compact** in a finite-dimensional real topological vector
space. By Carathéodory's theorem, it is the image of the compact set `StdSimplex ℝ (Fin n) × sⁿ`,
with `n = finrank + 1`, by the continuous map `(w, z) ↦ ∑ i, w i • z i`. -/
theorem IsCompact.convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E] {s : Set E}
    (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  set n := Module.finrank ℝ E + 1
  let f : StdSimplex ℝ (Fin n) × (Fin n → E) → E := fun p ↦ ∑ i, p.1.weights i • p.2 i
  have hf : Continuous f := continuous_finsetSum _ fun i _ ↦
    ((StdSimplex.continuous_weights_apply ℝ i).comp continuous_fst).smul
      ((continuous_apply i).comp continuous_snd)
  suffices _root_.convexHull ℝ s = f '' (Set.univ ×ˢ Set.univ.pi fun _ ↦ s) from
    this ▸ (isCompact_univ.prod (isCompact_univ_pi fun _ ↦ hs)).image hf
  refine (Set.Subset.antisymm ?_ ?_)
  · intro x hx
    obtain ⟨κ, _, z, w, hz, hind, hw, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
    -- extend the Carathéodory combination by zero weights to `n` points
    have hcard : Fintype.card κ ≤ Fintype.card (Fin n) := hind.card_le_finrank_succ.trans
      (by rw [Fintype.card_fin]; exact Nat.succ_le_succ (Submodule.finrank_le _))
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    let w' : Fin n → ℝ := Function.extend e w 0
    let z' : Fin n → E := Function.extend e z fun _ ↦ x₀
    have hw'0 : ∀ j ∉ Set.range e, w' j = 0 := fun j hj ↦ Function.extend_apply' _ _ _ hj
    have hw'nonneg : ∀ j, 0 ≤ w' j := fun j ↦ by
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simpa [w', e.injective.extend_apply] using (hw i).le
      · rw [hw'0 j hj]
    have hsum : ∀ g : Fin n → E, (∀ j ∉ Set.range e, g j = 0) →
        ∑ j, g j = ∑ i, g (e i) := fun g hg ↦
      (Fintype.sum_of_injective e e.injective _ _ hg fun _ ↦ rfl).symm
    let ω : StdSimplex ℝ (Fin n) :=
      { weights := Finsupp.equivFunOnFinite.symm w'
        nonneg := fun j ↦ by simpa using hw'nonneg j
        total := by
          rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl, ← hw1]
          exact (Fintype.sum_of_injective e e.injective _ _ hw'0 fun i ↦
            (e.injective.extend_apply _ _ i).symm).symm }
    refine ⟨(ω, z'), ⟨Set.mem_univ _, fun j _ ↦ ?_⟩, ?_⟩
    · by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        simpa [z', e.injective.extend_apply] using hz (Set.mem_range_self i)
      · simpa [z', Function.extend_apply' _ _ _ hj] using hx₀
    · simp only [f, ω, Finsupp.coe_equivFunOnFinite_symm]
      rw [hsum _ fun j hj ↦ by rw [hw'0 j hj, zero_smul]]
      simp [w', z', e.injective.extend_apply]
  · rintro _ ⟨⟨w, z⟩, ⟨-, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ ↦ w.weights_nonneg i) w.total_of_fintype
      fun i _ ↦ subset_convexHull ℝ s (hz i (Set.mem_univ _))
