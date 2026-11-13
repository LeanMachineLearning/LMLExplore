/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Order.OrderClosed

/-!
# Maximal indices of finitely many continuous functions

Let `g i` be finitely many functions, continuous at `x`, with values in a linear order with the
order-closed topology. An index that is not maximal at `x` is beaten by another index at `x`, hence
also near `x`. So near `x`, every index at which `g · x'` is maximal is already maximal at `x`: the
set of the maximal indices can only shrink near `x`. This is the upper hemicontinuity of the
correspondence `x ↦ argmax_i g i x`, used for instance for the answers of largest value in a
game.

## Main statements

* `eventually_setOf_forall_le_subset`: near `x` within `s`, the indices at which finitely many
  functions continuous within `s` at `x` are maximal are maximal at `x`.
-/

public section

open Filter Topology

namespace LMLExplore

variable {α ι δ : Type*} [TopologicalSpace α] [Finite ι] [LinearOrder δ] [TopologicalSpace δ]
  [OrderClosedTopology δ] {g : ι → α → δ} {s : Set α} {x : α}

/-- Let `g i` be finitely many functions, continuous within `s` at `x`, with values in a linear
order. Near `x` within `s`, every index `i` at which `g i x'` is maximal is an index at which
`g i x` is maximal. -/
lemma eventually_setOf_forall_le_subset (hg : ∀ i, ContinuousWithinAt (g i) s x) :
    ∀ᶠ x' in 𝓝[s] x, {i | ∀ j, g j x' ≤ g i x'} ⊆ {i | ∀ j, g j x ≤ g i x} := by
  -- An index that is not maximal at `x` is beaten by another one near `x`.
  have h : ∀ i, ∀ᶠ x' in 𝓝[s] x, (∀ j, g j x ≤ g i x) ∨ ∃ j, g i x' < g j x' := by
    intro i
    by_cases hi : ∀ j, g j x ≤ g i x
    · exact .of_forall fun _ ↦ .inl hi
    · obtain ⟨j, hj⟩ := not_forall.1 hi
      filter_upwards [(hg i).tendsto.eventually_lt (hg j).tendsto (not_le.1 hj)] with x' hx'
      exact .inr ⟨j, hx'⟩
  filter_upwards [eventually_all.2 h] with x' hx' i hi
  exact (hx' i).resolve_right fun ⟨j, hj⟩ ↦ (hi j).not_gt hj

end LMLExplore
