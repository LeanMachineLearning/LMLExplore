/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.Filter.Extr

/-!
# Measurable selections of maximizers in a finite type

A measurable map `s` from a measurable space into the subsets of a finite type `β`, whose values
are nonempty, has a measurable selection that maximizes a given function on each value: the
choice of a maximizer is a function of the value `s a`, and every function on the subsets of a
finite type is measurable. Integrating, the lower Lebesgue integral of `a ↦ ⨆ b ∈ s a, g b` is
the supremum of the integrals of `g` along the measurable selections of `s`: choosing the element
of `s a` after seeing `a`, in a measurable way, achieves the integral of the maximum.

This is the measure-theoretic content of the equivalence between simultaneous and post-hoc error
control in multiple testing, where `s a` is a finite family of candidate rejection sets [XSF+26,
Lemma 4].

## Main statements

* `MeasureTheory.exists_measurable_forall_mem_isMaxOn`: a measurable map into the nonempty subsets
  of a finite type has a measurable selection maximizing a given function on each value.
* `MeasureTheory.lintegral_biSup_eq_iSup_lintegral`: the integral of the maximum of `g` over
  `s a` is the supremum of the integrals of `g` along the measurable selections of `s`.

## References

* [XSF+26] Z. Xu, A. Solari, L. Fischer, R. de Heide, A. Ramdas and J. Goeman, *Bringing closure
  to false discovery rate control: a general principle for multiple testing*,
  arXiv:2509.02517v3, Lemma 4.
-/

public section

open scoped ENNReal

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

/-- For a measurable map `s` into the nonempty subsets of a finite type, the integral of the
maximum of `g` over `s a` is the supremum of the integrals of `g` along the measurable selections
of `s`: the supremum is attained by a selection that maximizes `g`. -/
theorem lintegral_biSup_eq_iSup_lintegral (hs : Measurable s) (hne : ∀ a, (s a).Nonempty)
    (g : β → ℝ≥0∞) (μ : Measure α) :
    ∫⁻ a, ⨆ b ∈ s a, g b ∂μ =
      ⨆ (σ : α → β) (_ : Measurable σ) (_ : ∀ a, σ a ∈ s a), ∫⁻ a, g (σ a) ∂μ := by
  refine le_antisymm ?_ <| iSup₂_le fun σ _ ↦ iSup_le fun hσ ↦
    lintegral_mono fun a ↦ le_iSup₂_of_le (σ a) (hσ a) le_rfl
  obtain ⟨σ, hσ, hσs⟩ := exists_measurable_forall_mem_isMaxOn hs hne g
  have hσg (a : α) : ⨆ b ∈ s a, g b = g (σ a) :=
    le_antisymm (iSup₂_le fun b hb ↦ isMaxOn_iff.1 (hσs a).2 b hb)
      (le_iSup₂_of_le (σ a) (hσs a).1 le_rfl)
  simp_rw [hσg]
  exact le_iSup₂_of_le σ hσ <| le_iSup_of_le (fun a ↦ (hσs a).1) le_rfl

end MeasureTheory
