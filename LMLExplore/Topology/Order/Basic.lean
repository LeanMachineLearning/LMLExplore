/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Boxes in neighbourhoods of a product of ordered spaces

A complement to the lemmas `pi_Icc_mem_nhds` of `Mathlib/Topology/Order/Basic.lean`, which show
that boxes `Icc a b` with `a < x < b` coordinatewise are neighbourhoods of `x`: conversely, every
neighbourhood of `x` in a product of densely ordered spaces without extremal elements contains
such a box. Its corners `a` and `b` then lie in the neighbourhood, which is used for instance to
keep empirical means in a box inside a neighbourhood of a model, with the box corners themselves
admissible models.

## Main statements

* `LMLExplore.exists_pi_Icc_subset_of_mem_nhds`: a neighbourhood of `x : ∀ i, X i` contains a box
  `Icc a b` with `a i < x i < b i` for all `i`.
-/

public section

open Set Filter Topology

namespace LMLExplore

variable {ι : Type*} {X : ι → Type*} [∀ i, LinearOrder (X i)] [∀ i, TopologicalSpace (X i)]
  [∀ i, OrderTopology (X i)] [∀ i, DenselyOrdered (X i)] [∀ i, NoMinOrder (X i)]
  [∀ i, NoMaxOrder (X i)]

/-- A neighbourhood `s` of `x` in a product of densely ordered spaces without extremal elements
contains a box `Icc a b` with `a i < x i < b i` for all `i`. -/
theorem exists_pi_Icc_subset_of_mem_nhds {x : ∀ i, X i} {s : Set (∀ i, X i)} (hs : s ∈ 𝓝 x) :
    ∃ a b : ∀ i, X i, (∀ i, a i < x i) ∧ (∀ i, x i < b i) ∧ Icc a b ⊆ s := by
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨I, t, ht, hts⟩ := hs
  -- In each coordinate, a closed interval around `x i` inside `t i`.
  have h (i : ι) : ∃ ab : X i × X i, ab.1 < x i ∧ x i < ab.2 ∧ Icc ab.1 ab.2 ⊆ t i := by
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 (ht i)
    obtain ⟨l', hl', hl'x⟩ := exists_between hl
    obtain ⟨u', hxu', hu'⟩ := exists_between hu
    exact ⟨(l', u'), hl'x, hxu', (Icc_subset_Ioo hl' hu').trans hlu⟩
  choose ab hab using h
  exact ⟨fun i ↦ (ab i).1, fun i ↦ (ab i).2, fun i ↦ (hab i).1, fun i ↦ (hab i).2.1,
    fun y hy ↦ hts fun i _ ↦ (hab i).2.2 ⟨hy.1 i, hy.2 i⟩⟩

end LMLExplore
