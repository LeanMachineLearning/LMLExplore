/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Hemicontinuity of images and of selections

Complements to Mathlib's `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`: the image of an
upper hemicontinuous correspondence by a continuous map is upper hemicontinuous, and a selection
of an upper hemicontinuous correspondence is continuous at the points where the correspondence has
a single value.

Together with Mathlib's `UpperHemicontinuousWithinAt.const` and
`LowerHemicontinuousWithinAt.const`, this is what is needed to apply Berge's maximum theorem
(`LMLExplore/Topology/Semicontinuity/Berge.lean`) to a supremum over a fixed compact subset `K` of
a space, by working in the subtype `K` with the constant correspondence `univ` and mapping the
maximizers back to the space.

## Main statements

* `UpperHemicontinuousWithinAt.image`: the image of an upper hemicontinuous correspondence by a
  continuous map is upper hemicontinuous.
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
