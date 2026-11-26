/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Finitely supported probability measures: supports and the simplex

Mathlib's `Convexity.StdSimplex R X` is the type of finitely supported probability measures on
`X`, and `Convexity.convexCombPair s t _ _ _ w w'` is the convex combination `s • w + t • w'` of
two of them (`Convexity.StdSimplex.weights_convexCombPair`). Its support is contained in the union
of the supports of `w` and `w'`: the measures supported in a set `𝒜` form a convex subset of
`StdSimplex R X`. This is what makes the designs on a set of vectors, and their design operators,
a convex set.

A finitely supported probability measure supported in the image `f '' S` of a set is the image by
`f` of one supported in `S`, with no more support points: a design on the features of a set of arms
is the image of a design on these arms.

On a finite type `α`, the weight vectors of the finitely supported probability measures are
exactly the vectors of `LMLExplore.simplex α`, the vectors with nonnegative entries summing to `1`.

## Main statements

* `Convexity.StdSimplex.weights_pos_of_mem_support`: the points of the support have positive
  weight.
* `Convexity.StdSimplex.support_weights_map_subset`: the support of the image of a finitely
  supported probability measure by a map is contained in the image of its support;
  `Convexity.StdSimplex.support_weights_map_subset_range`: hence in the range of the map.
* `Convexity.StdSimplex.exists_map_eq_of_support_subset_image`: a finitely supported probability
  measure supported in the image `f '' S` is the image by `f` of one supported in `S`, with at most
  as many support points.
* `Convexity.StdSimplex.support_weights_convexCombPair_subset`: the support of a convex combination
  of two finitely supported probability measures is contained in the union of their supports.
* `Convexity.StdSimplex.weights_sum_mul_add_const`, `Convexity.StdSimplex.sum_mul_weights_sum_mul`:
  expectations `w.weights.sum fun x r ↦ r * f x` under a finitely supported probability measure
  are affine in `f`.
* `Convexity.StdSimplex.weights_mem_simplex`, `LMLExplore.simplex_eq_range_weights`: on a finite
  type `α`, the weight vectors of the finitely supported probability measures are exactly the
  vectors of `LMLExplore.simplex α`, so that a vector of the simplex (an allocation of samples to
  finitely many arms) is a finitely supported probability measure on the arms, whose image by a
  feature map is a design.
-/

public section

open scoped Finset

namespace Convexity.StdSimplex

variable {R X Y : Type*} [PartialOrder R] [Semiring R]

/-- The points of the support of a finitely supported probability measure have positive weight. -/
theorem weights_pos_of_mem_support {w : StdSimplex R X} {x : X} (hx : x ∈ w.weights.support) :
    0 < w.weights x :=
  (w.nonneg x).lt_of_ne (Finsupp.mem_support_iff.1 hx).symm

variable [IsStrictOrderedRing R]

/-- The support of the image of a finitely supported probability measure by `f` is contained in
the image by `f` of its support. -/
theorem support_weights_map_subset (f : X → Y) (w : StdSimplex R X) :
    ((w.map f).weights.support : Set Y) ⊆ f '' ↑w.weights.support := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
  exact Set.mem_image_of_mem f hx

/-- The support of the image of a finitely supported probability measure by `f` is contained in
the range of `f`. -/
theorem support_weights_map_subset_range (f : X → Y) (w : StdSimplex R X) :
    ((w.map f).weights.support : Set Y) ⊆ Set.range f :=
  (support_weights_map_subset f w).trans (Set.image_subset_range _ _)

/-- A finitely supported probability measure `π` on `Y` supported in the image `f '' S` is the
image by `f` of a finitely supported probability measure on `X` supported in `S`, with at most as
many support points as `π`. -/
theorem exists_map_eq_of_support_subset_image {f : X → Y} {S : Set X} {π : StdSimplex R Y}
    (hπ : ↑π.weights.support ⊆ f '' S) :
    ∃ w : StdSimplex R X, ↑w.weights.support ⊆ S ∧ w.map f = π ∧
      #w.weights.support ≤ #π.weights.support := by
  classical
  -- a section `g` of `f` on `f '' S` with values in `S`
  have hsec : ∀ y ∈ f '' S, ∃ x ∈ S, f x = y := fun y ⟨x, hx, hy⟩ ↦ ⟨x, hx, hy⟩
  have : Nonempty X := by
    obtain ⟨y, hy⟩ := π.support_weights_nonempty
    obtain ⟨x, -, -⟩ := hπ hy
    exact ⟨x⟩
  choose! g hgS hgf using hsec
  refine ⟨π.map g, fun x hx ↦ ?_, ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := support_weights_map_subset g π hx
    exact hgS y (hπ hy)
  · rw [← weights_inj, map_map, weights_map,
      Finsupp.mapDomain_congr rfl fun y hy ↦ hgf y (hπ hy)]
    exact Finsupp.mapDomain_id
  · exact (Finset.card_le_card Finsupp.mapDomain_support).trans Finset.card_image_le

/-- The support of a convex combination of two finitely supported probability measures is
contained in the union of their supports. -/
theorem support_weights_convexCombPair_subset (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) (w w' : StdSimplex R X) :
    ((convexCombPair s t hs ht hst w w').weights.support : Set X) ⊆
      ↑w.weights.support ∪ ↑w'.weights.support := by
  rw [weights_convexCombPair]
  exact (LMLExplore.convex_setOf_nonneg_support_subset_sum_eq_one _
    ⟨w.nonneg, Set.subset_union_left, w.total⟩ ⟨w'.nonneg, Set.subset_union_right, w'.total⟩
    hs ht hst).2.1

/-- The weight vector of a finitely supported probability measure on a finite type lies in the
simplex. -/
theorem weights_mem_simplex [Fintype X] (w : StdSimplex ℝ X) : ⇑w.weights ∈ LMLExplore.simplex X :=
  LMLExplore.mem_simplex_iff.2 ⟨w.weights_nonneg, w.total_of_fintype⟩

section Expectation

/-! ### Expectations

The expectation of `f : X → R` under `w : StdSimplex R X` is `w.weights.sum fun x r ↦ r * f x`. -/

variable {R X ι : Type*} [CommSemiring R] [PartialOrder R]

/-- The expectation of `f + c` is the expectation of `f` plus `c`. -/
theorem weights_sum_mul_add_const (w : StdSimplex R X) (f : X → R) (c : R) :
    (w.weights.sum fun x r ↦ r * (f x + c)) = (w.weights.sum fun x r ↦ r * f x) + c := by
  have h := w.total
  simp only [Finsupp.sum] at h ⊢
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, h, one_mul]

/-- Expectations commute with finite linear combinations. -/
theorem sum_mul_weights_sum_mul (w : StdSimplex R X) (s : Finset ι) (c : ι → R)
    (f : ι → X → R) :
    ∑ i ∈ s, c i * (w.weights.sum fun x r ↦ r * f i x) =
      w.weights.sum fun x r ↦ r * ∑ i ∈ s, c i * f i x := by
  simp only [Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

end Expectation

end Convexity.StdSimplex

namespace LMLExplore

open Convexity

/-- The simplex of a finite type is the set of weight vectors of the finitely supported probability
measures on it. -/
theorem simplex_eq_range_weights {α : Type*} [Fintype α] :
    simplex α = Set.range (fun w : StdSimplex ℝ α ↦ ⇑w.weights) := by
  rw [StdSimplex.range_toFun_comp_weights]
  ext
  simp [mem_simplex_iff]

end LMLExplore
