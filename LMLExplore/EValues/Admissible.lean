/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import Statlib.EValues.Product

/-!
# Admissible e-variables

An e-variable for a null `S` is admissible when no e-variable is larger in a way that the null can
see: every e-variable that dominates it almost surely under every member of the null is equal to
it almost surely under every member of the null. This file defines admissible and strongly
admissible e-variables and proves their first properties: a strongly admissible e-variable is
admissible, an exact e-variable is strongly admissible, for a simple null the admissible
e-variables are the exact ones, which are the likelihood ratios, and products of strongly
admissible e-variables are strongly admissible for the product null.

Following Statlib, the null is an arbitrary set of measures and e-variables are `ℝ≥0∞`-valued. The
statements that compare integrals assume that the members of the null are finite measures; exact
means `∫⁻ E ∂P = P univ`, which is expectation one for a probability measure.

## Main definitions

* `ProbabilityTheory.IsAdmissibleEVar E S`: `E` is an admissible e-variable for `S`.
* `ProbabilityTheory.IsStronglyAdmissibleEVar E S`: `E` is an e-variable for `S` such that every
  measurable set charged by a member of `S` is charged by a member under which `E` is exact.

## Main statements

* `ProbabilityTheory.isAdmissibleEVar_iff_forall_le`: admissibility can be tested on the
  e-variables that dominate `E` everywhere.
* `ProbabilityTheory.IsStronglyAdmissibleEVar.isAdmissibleEVar`: a strongly admissible e-variable
  for a null of finite measures is admissible.
* `ProbabilityTheory.IsExactEVar.isAdmissibleEVar`: so is an exact e-variable.
* `ProbabilityTheory.isAdmissibleEVar_singleton_iff`: for a simple null `{P}` with `P` finite,
  admissible and exact coincide.
* `ProbabilityTheory.isExactEVar_singleton_iff_exists_rnDeriv`: the exact e-variables for `{P}`
  are the likelihood ratios `Q.rnDeriv P` of the measures `Q ≪ P` with the mass of `P`.
* `ProbabilityTheory.IsStronglyAdmissibleEVar.prod`: the product of two strongly admissible
  e-variables is strongly admissible for the null of the product measures.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Definition 2.11, Proposition 2.12, Corollary 2.15 (a)
  and Proposition 2.17.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {S : Set (Measure Ω)} {T : Set (Measure Ω')} {E F : Ω → ℝ≥0∞} {P : Measure Ω}

/-! ### Admissible e-variables -/

/-- An e-variable `E` for `S` is **admissible** when every e-variable for `S` that is at least `E`
almost surely under every member of `S` is at most `E` almost surely under every member of `S`
[RW, Definition 2.11]. It is enough to test the e-variables that dominate `E` everywhere:
`isAdmissibleEVar_iff_forall_le`. -/
structure IsAdmissibleEVar (E : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop extends IsEVar E S where
  ae_le_of_ae_le : ∀ F, IsEVar F S → (∀ P ∈ S, E ≤ᵐ[P] F) → ∀ P ∈ S, F ≤ᵐ[P] E

namespace IsAdmissibleEVar

/-- An e-variable that dominates an admissible e-variable almost surely under every member of the
null is at most it almost surely under every member of the null. -/
theorem ae_le (hE : IsAdmissibleEVar E S) (hF : IsEVar F S) (hEF : ∀ P ∈ S, E ≤ᵐ[P] F)
    (hP : P ∈ S) : F ≤ᵐ[P] E :=
  hE.ae_le_of_ae_le F hF hEF P hP

/-- An e-variable that dominates an admissible e-variable almost surely under every member of the
null is equal to it almost surely under every member of the null. -/
theorem ae_eq (hE : IsAdmissibleEVar E S) (hF : IsEVar F S) (hEF : ∀ P ∈ S, E ≤ᵐ[P] F)
    (hP : P ∈ S) : F =ᵐ[P] E :=
  (hE.ae_le hF hEF hP).antisymm (hEF P hP)

/-- A measurable function equal to an admissible e-variable almost surely under every member of
the null is an admissible e-variable. -/
theorem congr (hE : IsAdmissibleEVar E S) (hF : Measurable F) (hEF : ∀ P ∈ S, E =ᵐ[P] F) :
    IsAdmissibleEVar F S where
  toIsEVar := hE.toIsEVar.congr hF hEF
  ae_le_of_ae_le _ hG hFG P hP :=
    (hE.ae_le hG (fun P hP ↦ (hEF P hP).le.trans (hFG P hP)) hP).trans (hEF P hP).le

end IsAdmissibleEVar

/-- An e-variable is admissible exactly when every e-variable that is at least it everywhere is
equal to it almost surely under every member of the null: the definition of
[RW, Definition 2.11]. -/
theorem isAdmissibleEVar_iff_forall_le :
    IsAdmissibleEVar E S ↔ IsEVar E S ∧ ∀ F, IsEVar F S → E ≤ F → ∀ P ∈ S, F =ᵐ[P] E := by
  refine ⟨fun h ↦ ⟨h.toIsEVar, fun F hF hEF P hP ↦ h.ae_eq hF (fun _ _ ↦ .of_forall hEF) hP⟩,
    fun ⟨hE, h⟩ ↦ ⟨hE, fun F hF hEF P hP ↦ ?_⟩⟩
  -- the maximum of `E` and `F` is an e-variable, equal to `F` almost surely, that dominates `E`
  have h_max : IsEVar (fun ω ↦ max (E ω) (F ω)) S :=
    hF.congr (hE.measurable.max hF.measurable)
      fun P hP ↦ (hEF P hP).mono fun ω hω ↦ (max_eq_right hω).symm
  filter_upwards [h _ h_max (fun ω ↦ le_max_left _ _) P hP] with ω hω
  exact (le_max_right _ _).trans hω.le

/-! ### Strongly admissible e-variables -/

/-- An e-variable `E` for `S` is **strongly admissible** when every measurable set charged by some
member of `S` is charged by a member `P` of `S` with `∫⁻ E ∂P = P univ`: the sufficient condition
for admissibility of [RW, Corollary 2.15 (a)]. -/
structure IsStronglyAdmissibleEVar (E : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop
    extends IsEVar E S where
  exists_lintegral_eq : ∀ A, MeasurableSet A → (∃ P ∈ S, P A ≠ 0) →
    ∃ P ∈ S, P A ≠ 0 ∧ ∫⁻ ω, E ω ∂P = P univ

/-- A strongly admissible e-variable for a null of finite measures is admissible
[RW, Corollary 2.15 (a)]. -/
theorem IsStronglyAdmissibleEVar.isAdmissibleEVar (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hE : IsStronglyAdmissibleEVar E S) : IsAdmissibleEVar E S where
  toIsEVar := hE.toIsEVar
  ae_le_of_ae_le F hF hEF P₀ hP₀ := by
    by_contra h_not
    have hA : MeasurableSet {ω | E ω < F ω} := measurableSet_lt hE.measurable hF.measurable
    have hP₀A : P₀ {ω | E ω < F ω} ≠ 0 :=
      fun h0 ↦ h_not (ae_iff.2 (by simpa only [not_le] using h0))
    -- under a member of the null that charges `{E < F}` and under which `E` is exact, `F` has
    -- integral at most that of `E`
    obtain ⟨P, hP, hPA, hPE⟩ := hE.exists_lintegral_eq _ hA ⟨P₀, hP₀, hP₀A⟩
    have := hS P hP
    have h_sub : ∫⁻ ω, F ω - E ω ∂P = 0 := by
      rw [lintegral_sub hE.measurable (by rw [hPE]; exact measure_ne_top P univ) (hEF P hP), hPE]
      exact tsub_eq_zero_of_le (hF.lintegral_le_measure_univ P hP)
    rw [lintegral_eq_zero_iff (f := fun ω ↦ F ω - E ω) (hF.measurable.sub hE.measurable)]
      at h_sub
    have h_le : ∀ᵐ ω ∂P, ¬ E ω < F ω := by
      filter_upwards [h_sub] with ω hω
      exact not_lt.2 (tsub_eq_zero_iff_le.1 hω)
    exact hPA (by simpa only [not_not] using ae_iff.1 h_le)

/-- An exact e-variable is strongly admissible. -/
theorem IsExactEVar.isStronglyAdmissibleEVar (hE : IsExactEVar E S) :
    IsStronglyAdmissibleEVar E S where
  toIsEVar := hE.toIsEVar
  exists_lintegral_eq _ _ := fun ⟨P, hP, hPA⟩ ↦ ⟨P, hP, hPA, hE.lintegral_eq_measure_univ P hP⟩

/-- An exact e-variable for a null of finite measures is admissible. -/
theorem IsExactEVar.isAdmissibleEVar (hS : ∀ P ∈ S, IsFiniteMeasure P) (hE : IsExactEVar E S) :
    IsAdmissibleEVar E S :=
  hE.isStronglyAdmissibleEVar.isAdmissibleEVar hS

/-! ### Simple nulls -/

/-- An admissible e-variable for a simple null `{P}`, with `P` finite, is exact: otherwise adding
a positive constant gives a larger e-variable [RW, Proposition 2.12]. -/
theorem IsAdmissibleEVar.isExactEVar_singleton [IsFiniteMeasure P]
    (hE : IsAdmissibleEVar E {P}) : IsExactEVar E {P} where
  toIsEVar := hE.toIsEVar
  lintegral_eq_measure_univ := by
    simp only [mem_singleton_iff, forall_eq]
    by_contra h_ne
    have h_lt : ∫⁻ ω, E ω ∂P < P univ :=
      lt_of_le_of_ne (hE.toIsEVar.lintegral_le_measure_univ P rfl) h_ne
    have hP0 : P univ ≠ 0 := (bot_le.trans_lt h_lt).ne'
    set c : ℝ≥0∞ := (P univ - ∫⁻ ω, E ω ∂P) / P univ with hc
    have hc0 : c ≠ 0 := (ENNReal.div_pos (tsub_pos_of_lt h_lt).ne' (measure_ne_top P univ)).ne'
    have hF : IsEVar (fun ω ↦ E ω + c) {P} := by
      refine .of_lintegral_le_measure_univ (by simpa) (hE.measurable.add_const c) ?_
      simp only [mem_singleton_iff, forall_eq]
      rw [lintegral_add_right _ measurable_const, lintegral_const, hc,
        ENNReal.div_mul_cancel hP0 (measure_ne_top P univ), add_tsub_cancel_of_le h_lt.le]
    have h_false : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.ae_le hF (fun _ _ ↦ .of_forall fun ω ↦ le_self_add) (mem_singleton P),
        hE.toIsEVar.ae_lt_top (mem_singleton P)] with ω h_le h_top
      have : c ≤ 0 := (ENNReal.add_le_add_iff_left h_top.ne).1 (by simpa using h_le)
      exact hc0 (le_zero_iff.1 this)
    have hP : P = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 h_false)
    exact hP0 (by simp [hP])

/-- For a simple null `{P}` with `P` finite, the admissible e-variables are the exact ones
[RW, Proposition 2.12]. -/
theorem isAdmissibleEVar_singleton_iff [IsFiniteMeasure P] :
    IsAdmissibleEVar E {P} ↔ IsExactEVar E {P} :=
  ⟨fun h ↦ h.isExactEVar_singleton, fun h ↦ h.isAdmissibleEVar (by simpa)⟩

/-- The exact e-variables for a simple null `{P}`, with `P` finite, are the likelihood ratios
`Q.rnDeriv P` of the measures `Q ≪ P` with the total mass of `P`, up to `P`-almost sure equality
[RW, Proposition 2.12]. -/
theorem isExactEVar_singleton_iff_exists_rnDeriv [IsFiniteMeasure P] :
    IsExactEVar E {P} ↔
      Measurable E ∧ ∃ Q : Measure Ω, Q ≪ P ∧ Q univ = P univ ∧ E =ᵐ[P] Q.rnDeriv P := by
  refine ⟨fun hE ↦ ⟨hE.measurable, P.withDensity E, withDensity_absolutelyContinuous P E, ?_,
    (Measure.rnDeriv_withDensity P hE.measurable).symm⟩, fun ⟨hE, Q, hQP, hQ, hEQ⟩ ↦ ?_⟩
  · rw [withDensity_apply _ .univ, Measure.restrict_univ]
    exact hE.lintegral_eq_measure_univ P rfl
  · have : IsFiniteMeasure Q := ⟨by rw [hQ]; exact measure_lt_top P univ⟩
    refine (isExactEVar_rnDeriv hQP hQ).congr hE ?_
    simp only [mem_singleton_iff, forall_eq]
    exact hEQ.symm

/-! ### Products -/

/-- The product of two strongly admissible e-variables, for nulls of finite measures, is strongly
admissible for the null of the product measures [RW, Proposition 2.17]. -/
theorem IsStronglyAdmissibleEVar.prod {F : Ω' → ℝ≥0∞} (hE : IsStronglyAdmissibleEVar E S)
    (hF : IsStronglyAdmissibleEVar F T) (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hT : ∀ P ∈ T, IsFiniteMeasure P) :
    IsStronglyAdmissibleEVar (fun p : Ω × Ω' ↦ E p.1 * F p.2) (image2 Measure.prod S T) where
  toIsEVar := hE.toIsEVar.prod hF.toIsEVar hS hT
  exists_lintegral_eq A hA := by
    rintro ⟨_, ⟨P, hP, P', hP', rfl⟩, hPA⟩
    have := hS P hP
    have := hT P' hP'
    -- replace the first factor by a member of `S` under which `E` is exact
    have hB := measurable_measure_prodMk_left (ν := P') hA
    obtain ⟨P₁, hP₁, hP₁B, hP₁E⟩ := hE.exists_lintegral_eq _
      (hB (measurableSet_singleton 0).compl)
      ⟨P, hP, ((lintegral_pos_iff_support hB).1
        (by rwa [← Measure.prod_apply hA, pos_iff_ne_zero])).ne'⟩
    have := hS P₁ hP₁
    have hP₁A : (P₁.prod P') A ≠ 0 := by
      rw [Measure.prod_apply hA]
      exact ((lintegral_pos_iff_support hB).2 (pos_iff_ne_zero.2 hP₁B)).ne'
    -- then the second factor by a member of `T` under which `F` is exact
    have hC := measurable_measure_prodMk_right (μ := P₁) hA
    obtain ⟨P₂, hP₂, hP₂C, hP₂F⟩ := hF.exists_lintegral_eq _
      (hC (measurableSet_singleton 0).compl)
      ⟨P', hP', ((lintegral_pos_iff_support hC).1
        (by rwa [← Measure.prod_apply_symm hA, pos_iff_ne_zero])).ne'⟩
    have := hT P₂ hP₂
    refine ⟨P₁.prod P₂, ⟨P₁, hP₁, P₂, hP₂, rfl⟩, ?_, ?_⟩
    · rw [Measure.prod_apply_symm hA]
      exact ((lintegral_pos_iff_support hC).2 (pos_iff_ne_zero.2 hP₂C)).ne'
    · rw [lintegral_prod_mul hE.measurable.aemeasurable hF.measurable.aemeasurable, hP₁E, hP₂F,
        ← univ_prod_univ, Measure.prod_prod]

end ProbabilityTheory
