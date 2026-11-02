/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Hemicontinuity of images

Complement to Mathlib's `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`: the image of an
upper hemicontinuous correspondence by a continuous map is upper hemicontinuous.

Together with Mathlib's `UpperHemicontinuousWithinAt.const` and
`LowerHemicontinuousWithinAt.const`, this is what is needed to apply Berge's maximum theorem
(`LMLExplore/Topology/Semicontinuity/Berge.lean`) to a supremum over a fixed compact subset `K` of
a space, by working in the subtype `K` with the constant correspondence `univ` and mapping the
maximizers back to the space.

## Main statements

* `UpperHemicontinuousWithinAt.image`: the image of an upper hemicontinuous correspondence by a
  continuous map is upper hemicontinuous.
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
