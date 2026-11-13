/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Uniform neighbourhoods for lower semicontinuity along a compact set

Let `f : X × Y → β` be lower semicontinuous within `univ ×ˢ s` at every point `(x, y)` with `y` in
a compact set `C`, and let `c < f (x, y)` for all `y ∈ C`. By compactness of `C`, the inequality
`c < f (x', y)` holds uniformly for `x'` near `x` and `y ∈ s` in a thickening of `C`. For a
singleton `C = {y}`, this is the lower semicontinuity of `f` at `(x, y)` with a product
neighbourhood `U × ball y η`.

## Main statements

* `IsCompact.exists_forall_mem_thickening_lt_of_lowerSemicontinuousWithinAt`: a neighbourhood `U`
  of `x` and `η > 0` such that `c < f (x', y)` for all `x' ∈ U` and `y ∈ s ∩ thickening η C`.
-/

public section

open Filter Topology Metric

variable {X Y β : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] [Preorder β]

/-- Let `f : X × Y → β` be lower semicontinuous within `univ ×ˢ s` at every point `(x, y)` with
`y` in the compact set `C`, and let `c < f (x, y)` for all `y ∈ C`. Then `c < f (x', y)` for all
`x'` in a neighbourhood of `x` and all `y ∈ s` in some thickening of `C`. -/
theorem IsCompact.exists_forall_mem_thickening_lt_of_lowerSemicontinuousWithinAt {C s : Set Y}
    (hC : IsCompact C) {f : X × Y → β} {x : X} {c : β}
    (hf : ∀ y ∈ C, LowerSemicontinuousWithinAt f (Set.univ ×ˢ s) (x, y))
    (hc : ∀ y ∈ C, c < f (x, y)) :
    ∃ U ∈ 𝓝 x, ∃ η > 0, ∀ x' ∈ U, ∀ y ∈ s, y ∈ thickening η C → c < f (x', y) := by
  have h_mem : {q : X × Y | q.2 ∈ s → c < f q} ∈ 𝓝 x ×ˢ 𝓝ˢ C := by
    refine hC.mem_prod_nhdsSet_of_forall fun y hy ↦ ?_
    have h_ev : ∀ᶠ q : X × Y in 𝓝 (x, y), q ∈ Set.univ ×ˢ s → c < f q :=
      eventually_nhdsWithin_iff.1 (hf y hy c (hc y hy))
    rw [nhds_prod_eq] at h_ev
    exact h_ev.mono fun q hq hq2 ↦ hq ⟨Set.mem_univ _, hq2⟩
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.1 h_mem
  obtain ⟨η, hη, hηV⟩ := (hasBasis_nhdsSet_thickening hC).mem_iff.1 hV
  exact ⟨U, hU, η, hη, fun x' hx' y hy hyC ↦ hUV (Set.mk_mem_prod hx' (hηV hyC)) hy⟩
