/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.Order.Filter.CountableInter

/-!
# The quasi-sure filter of a set of measures

A property holds `S`-quasi-surely when it holds `P`-almost surely for every member `P` of the null
`S : Set (Measure Ω)`. This file defines the filter `ProbabilityTheory.quasiSure S`, the supremum
of the filters `ae P` over `P ∈ S`, so that "almost surely under every member" is written
`∀ᶠ ω in quasiSure S, p ω`, `f =ᶠ[quasiSure S] g` and `f ≤ᶠ[quasiSure S] g`. The null is any set
of measures, with no domination: the quasi-sure filter of a dominated null is the almost
everywhere filter of a dominating mixture, but no such measure exists in general.

The congruence and monotonicity lemmas of e-variables, p-variables, conditional e-variables,
nonnegative supermartingales and e-processes are stated with this filter, in the files of those
notions.

## Main definitions

* `ProbabilityTheory.quasiSure S`: the quasi-sure filter of a null.

## Main statements

* `ProbabilityTheory.eventually_quasiSure_iff`: a property holds quasi-surely exactly when it holds
  almost surely under every member of the null; `eventuallyEq_quasiSure_iff` and
  `eventuallyLE_quasiSure_iff` are the forms for `=ᶠ` and `≤ᶠ`.
* `ProbabilityTheory.quasiSure_mono`, `quasiSure_union`, `quasiSure_singleton`,
  `quasiSure_empty`: the quasi-sure filter is monotone in the null, takes unions to suprema, and
  is the almost everywhere filter for a simple null.
* `ProbabilityTheory.countableInterFilter_quasiSure`: the quasi-sure filter is closed under
  countable intersections.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Definitions 1.2 and 7.3.

The definition and `eventually_quasiSure_iff` follow the prototypes of `notes/book/Suggested.lean`
(commit `88fb487`) in the paper project `RemyDegenne/evalues_research` (Apache 2.0).
-/

public section

open MeasureTheory Filter Set

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S T : Set (Measure Ω)} {P : Measure Ω}

/-- The quasi-sure filter of a null `S`: the sets that have a null complement under every member
of `S`. A property holds eventually for it exactly when it holds almost surely under every member
of `S` (`eventually_quasiSure_iff`). -/
def quasiSure (S : Set (Measure Ω)) : Filter Ω :=
  ⨆ P ∈ S, ae P

@[simp]
theorem eventually_quasiSure_iff {p : Ω → Prop} :
    (∀ᶠ ω in quasiSure S, p ω) ↔ ∀ P ∈ S, ∀ᵐ ω ∂P, p ω := by
  simp only [quasiSure, eventually_iSup]

@[simp]
theorem mem_quasiSure_iff {s : Set Ω} : s ∈ quasiSure S ↔ ∀ P ∈ S, s ∈ ae P :=
  eventually_quasiSure_iff

theorem eventuallyEq_quasiSure_iff {β : Type*} {f g : Ω → β} :
    f =ᶠ[quasiSure S] g ↔ ∀ P ∈ S, f =ᵐ[P] g :=
  eventually_quasiSure_iff

theorem eventuallyLE_quasiSure_iff {β : Type*} [LE β] {f g : Ω → β} :
    f ≤ᶠ[quasiSure S] g ↔ ∀ P ∈ S, f ≤ᵐ[P] g :=
  eventually_quasiSure_iff

/-- The almost everywhere filter of a member is finer than the quasi-sure filter: a quasi-sure
property holds almost surely under each member. -/
theorem ae_le_quasiSure (hP : P ∈ S) : ae P ≤ quasiSure S :=
  le_biSup ae hP

/-- The universal property of the quasi-sure filter as a supremum: it is finer than a filter `f`
exactly when the almost everywhere filter of every member is. -/
theorem quasiSure_le_iff {f : Filter Ω} : quasiSure S ≤ f ↔ ∀ P ∈ S, ae P ≤ f :=
  iSup₂_le_iff

/-- A property that holds quasi-surely holds almost surely under every member. -/
theorem ae_of_eventually_quasiSure {p : Ω → Prop} (h : ∀ᶠ ω in quasiSure S, p ω) (hP : P ∈ S) :
    ∀ᵐ ω ∂P, p ω :=
  eventually_quasiSure_iff.1 h P hP

/-- A larger null has a coarser (larger) quasi-sure filter: fewer properties hold quasi-surely. -/
@[gcongr]
theorem quasiSure_mono (hST : S ⊆ T) : quasiSure S ≤ quasiSure T :=
  biSup_mono fun _ hP ↦ hST hP

@[simp]
theorem quasiSure_empty : quasiSure (∅ : Set (Measure Ω)) = ⊥ := by
  simp [quasiSure]

@[simp]
theorem quasiSure_singleton : quasiSure {P} = ae P := by
  simp [quasiSure]

theorem quasiSure_union : quasiSure (S ∪ T) = quasiSure S ⊔ quasiSure T :=
  iSup_union

/-- A countable intersection of quasi-sure sets is quasi-sure: a countable family of properties
holds quasi-surely together as soon as each does (`Filter.eventually_countable_forall`). -/
instance countableInterFilter_quasiSure : CountableInterFilter (quasiSure S) :=
  ⟨fun _ hs hmem ↦ mem_quasiSure_iff.2 fun P hP ↦
    (countable_sInter_mem hs).2 fun t ht ↦ mem_quasiSure_iff.1 (hmem t ht) P hP⟩

end ProbabilityTheory
