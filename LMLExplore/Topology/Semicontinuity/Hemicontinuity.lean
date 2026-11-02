/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Hemicontinuity of constant correspondences and of images

Complements to Mathlib's `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`: a constant
correspondence is upper and lower hemicontinuous, and the image of an upper hemicontinuous
correspondence by a continuous map is upper hemicontinuous.

These are the facts needed to apply Berge's maximum theorem
(`LMLExplore/Topology/Semicontinuity/Berge.lean`) to a supremum over a fixed compact subset `K` of
a space, by working in the subtype `K` with the constant correspondence `univ` and mapping the
maximizers back to the space.

## Main statements

* `upperHemicontinuousWithinAt_const`, `lowerHemicontinuousWithinAt_const`: a constant
  correspondence is upper and lower hemicontinuous.
* `UpperHemicontinuousWithinAt.image`: the image of an upper hemicontinuous correspondence by a
  continuous map is upper hemicontinuous.
-/

public section

open Set Filter Topology

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  {f : α → Set β} {s : Set α} {x : α}

/-- A constant correspondence is upper hemicontinuous. -/
lemma upperHemicontinuousWithinAt_const (K : Set β) :
    UpperHemicontinuousWithinAt (fun _ : α ↦ K) s x :=
  upperHemicontinuousWithinAt_iff.2 fun _ h ↦ Eventually.of_forall fun _ ↦ h

/-- A constant correspondence is lower hemicontinuous. -/
lemma lowerHemicontinuousWithinAt_const (K : Set β) :
    LowerHemicontinuousWithinAt (fun _ : α ↦ K) s x :=
  lowerHemicontinuousWithinAt_iff.2 fun _ _ h ↦ Eventually.of_forall fun _ ↦ h

/-- The image of an upper hemicontinuous correspondence by a continuous map is upper
hemicontinuous. -/
lemma UpperHemicontinuousWithinAt.image (hf : UpperHemicontinuousWithinAt f s x) {g : β → γ}
    (hg : Continuous g) : UpperHemicontinuousWithinAt (fun x ↦ g '' f x) s x := by
  refine .of_forall_isOpen fun u hu hfu ↦ ?_
  filter_upwards [hf.forall_isOpen _ (hu.preimage hg) (image_subset_iff.1 hfu)] with x' hx'
  exact image_subset_iff.2 hx'
