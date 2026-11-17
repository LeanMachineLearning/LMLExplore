/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Order.Filter.Extr

/-!
# Measurable selections of maximizers in a finite type

A measurable map `s` from a measurable space into the subsets of a finite type `β`, whose values
are nonempty, has a measurable selection that maximizes a given function on each value: the
choice of a maximizer is a function of the value `s a`, and every function on the subsets of a
finite type is measurable.

In multiple testing, `s a` is a finite family of candidate rejection sets, and the selection is
the step from simultaneous to post-hoc error control [XSF+26, Lemma 4]; see
`MeasureTheory.lintegral_biSup_eq_iSup_lintegral`.

## Main statements

* `MeasureTheory.exists_measurable_forall_mem_isMaxOn`: a measurable map into the nonempty subsets
  of a finite type has a measurable selection maximizing a given function on each value.

## References

* [XSF+26] Z. Xu, A. Solari, L. Fischer, R. de Heide, A. Ramdas and J. Goeman, *Bringing closure
  to false discovery rate control: a general principle for multiple testing*,
  arXiv:2509.02517v3, Lemma 4.
-/

public section

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} [MeasurableSpace β] [Finite β]
  {s : α → Set β}

/-- A measurable map `s` into the nonempty subsets of a finite type has a measurable selection
`σ`, with `σ a ∈ s a`, that maximizes `g` on `s a` for every `a`. -/
theorem exists_measurable_forall_mem_isMaxOn [LinearOrder γ] (hs : Measurable s)
    (hne : ∀ a, (s a).Nonempty) (g : β → γ) :
    ∃ σ : α → β, Measurable σ ∧ ∀ a, σ a ∈ s a ∧ IsMaxOn g (s a) (σ a) := by
  have hmax (t : {t : Set β // t.Nonempty}) : ∃ b ∈ t.1, IsMaxOn g t.1 b := by
    obtain ⟨b, hb, hgb⟩ := Set.exists_max_image t.1 g t.1.toFinite t.2
    exact ⟨b, hb, isMaxOn_iff.2 hgb⟩
  -- The maximizer is chosen as a function of the value `s a`; every function on the subsets of
  -- a finite type is measurable.
  exact ⟨fun a ↦ (hmax ⟨s a, hne a⟩).choose,
    (Measurable.of_discrete (f := fun t ↦ (hmax t).choose)).comp hs.subtype_mk,
    fun a ↦ (hmax ⟨s a, hne a⟩).choose_spec⟩

end MeasureTheory
