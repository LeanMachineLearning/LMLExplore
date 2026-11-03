/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Hemicontinuity of images, unions and selections

Complements to Mathlib's `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`: the image of an
upper hemicontinuous correspondence by a continuous map is upper hemicontinuous, a union of
finitely many upper hemicontinuous correspondences over a set of indices that can only shrink near
the point is upper hemicontinuous, and a selection of an upper hemicontinuous
correspondence is continuous at the points where the correspondence has a single value.

Together with Mathlib's `UpperHemicontinuousWithinAt.const` and
`LowerHemicontinuousWithinAt.const`, the image lemma `UpperHemicontinuousWithinAt.image` is what is
needed to apply Berge's maximum theorem (`LMLExplore/Topology/Semicontinuity/Berge.lean`) to a
supremum over a fixed compact subset `K` of a space, by working in the subtype `K` with the
constant correspondence `univ` and mapping the maximizers back to the space.

The union lemma `UpperHemicontinuousWithinAt.biUnion_of_eventually_subset` applies to
correspondences `x ↦ ⋃ i ∈ I x, f i x` where `I x` is the set of the indices `i` maximizing
finitely many continuous values `g i x` (`eventually_setOf_forall_le_subset`,
`LMLExplore/Topology/Order/OrderClosed.lean`): for instance the maximizers of `y ↦ max_i φ_i(x, y)`,
which are the maximizers of the functions `φ_i(x, ·)` whose supremum is largest.

The selection lemma `UpperHemicontinuousAt.continuousAt_of_eventually_mem` turns the upper
hemicontinuity of a set of maximizers, as given by Berge's theorem, into the continuity of a
maximizer at the points where that set has a single element.

## Main statements

* `UpperHemicontinuousWithinAt.image`: the image of an upper hemicontinuous correspondence by a
  continuous map is upper hemicontinuous.
* `UpperHemicontinuousWithinAt.of_eventually_subset`: a correspondence whose values near `x` are
  contained in its value at `x` is upper hemicontinuous at `x`.
* `UpperHemicontinuousWithinAt.biUnion_of_eventually_subset`: the union `⋃ i ∈ I x, f i x` of
  upper hemicontinuous correspondences over finite sets of indices `I x' ⊆ I x` near `x` is upper
  hemicontinuous at `x`.
* `UpperHemicontinuousAt.continuousAt_of_eventually_mem`: a selection of a correspondence that is
  upper hemicontinuous at `x`, with at most one value at `x`, is continuous at `x`.
-/

public section

open Set Filter Topology

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  {f : α → Set β} {s : Set α} {x : α}

/-- The image of an upper hemicontinuous correspondence by a continuous map is upper
hemicontinuous. -/
lemma UpperHemicontinuousWithinAt.image (hf : UpperHemicontinuousWithinAt f s x) {g : β → γ}
    (hg : Continuous g) : UpperHemicontinuousWithinAt (fun x ↦ g '' f x) s x := by
  refine .of_forall_isOpen fun u hu hfu ↦ ?_
  filter_upwards [hf.forall_isOpen _ (hu.preimage hg) (image_subset_iff.1 hfu)] with x' hx'
  exact image_subset_iff.2 hx'

/-- A correspondence whose values near `x` within `s` are contained in its value at `x` is upper
hemicontinuous within `s` at `x`. -/
lemma UpperHemicontinuousWithinAt.of_eventually_subset (h : ∀ᶠ x' in 𝓝[s] x, f x' ⊆ f x) :
    UpperHemicontinuousWithinAt f s x :=
  .of_forall_isOpen fun _ _ hfu ↦ h.mono fun _ hx' ↦ hx'.trans hfu

/-- Let `f i` be correspondences upper hemicontinuous within `s` at `x` for the indices `i` of a
finite set `I x`. If near `x` within `s` the sets of indices `I x'` are contained in `I x`, then the
union `x' ↦ ⋃ i ∈ I x', f i x'` is upper hemicontinuous within `s` at `x`. -/
lemma UpperHemicontinuousWithinAt.biUnion_of_eventually_subset {ι : Type*} {f : ι → α → Set β}
    {I : α → Set ι} (hI_fin : (I x).Finite)
    (hf : ∀ i ∈ I x, UpperHemicontinuousWithinAt (f i) s x) (hI : ∀ᶠ x' in 𝓝[s] x, I x' ⊆ I x) :
    UpperHemicontinuousWithinAt (fun x' ↦ ⋃ i ∈ I x', f i x') s x := by
  refine .of_forall_isOpen fun u hu hfu ↦ ?_
  have h : ∀ i ∈ I x, ∀ᶠ x' in 𝓝[s] x, f i x' ⊆ u := fun i hi ↦
    (hf i hi).forall_isOpen u hu ((subset_biUnion_of_mem (u := fun i ↦ f i x) hi).trans hfu)
  filter_upwards [hI, hI_fin.eventually_all.2 h] with x' hIx' hx'
  exact iUnion₂_subset fun i hi ↦ hx' i (hIx' hi)

/-- A selection `g` of a correspondence `f` that is upper hemicontinuous at `x`, with at most one
value at `x`, is continuous at `x`: for every open set `u` containing `g x`, the values `f x'`
near `x`, hence their elements `g x'`, lie in `u`. -/
lemma UpperHemicontinuousAt.continuousAt_of_eventually_mem {f : α → Set β} {x : α}
    (hf : UpperHemicontinuousAt f x) (hfx : (f x).Subsingleton) {g : α → β}
    (hg : ∀ᶠ x' in 𝓝 x, g x' ∈ f x') : ContinuousAt g x := by
  rw [← upperHemicontinuousAt_singleton_iff]
  refine .of_forall_isOpen fun u hu hgu ↦ ?_
  have hfu : f x ⊆ u := fun y hy ↦ hfx hy hg.self_of_nhds ▸ hgu rfl
  filter_upwards [hf.forall_isOpen u hu hfu, hg] with x' hx' hgx'
  exact singleton_subset_iff.2 (hx' hgx')
