/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# P-variables

A p-variable for a null hypothesis `S : Set (Measure Ω)` is a measurable `p : Ω → ℝ≥0∞` with
`P {ω | p ω ≤ α} ≤ α` for every member `P` of the null and every level `α`: rejecting when
`p ≤ α` is a level-`α` test for every `α` at once. As for Statlib's e-variables, the null is an
arbitrary set of measures and p-variables are `ℝ≥0∞`-valued; values above `1` carry no evidence.
This file defines p-variables and exact p-variables, and proves that, for a null of probability
measures, the inverse `E⁻¹` of an e-variable is a p-variable (the e-to-p calibration, with
`0⁻¹ = ∞` and no truncation at `1`).

## Main definitions

* `ProbabilityTheory.IsPVar p S`: `p` is a p-variable for `S`.
* `ProbabilityTheory.IsExactPVar p S`: `p` is a p-variable for `S` with `P {ω | p ω ≤ α} = α` for
  every `P ∈ S` and every `α ≤ 1`.

## Main statements

* `ProbabilityTheory.IsEVar.isPVar_inv`: for a null of probability measures, the inverse of an
  e-variable is a p-variable.
* `ProbabilityTheory.isExactPVar_ofReal_volume`: the identity of `[0, 1]` under Lebesgue measure is
  an exact p-variable, and `ProbabilityTheory.isExactPVar_ofReal_of_map_eq`: so is every random
  variable uniformly distributed on `[0, 1]` under every member of the null.
* `ProbabilityTheory.IsExactPVar.ae_le_one`: an exact p-variable is almost surely at most `1`
  under every probability measure of the null.

## References

* A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Definition 1.2 and Proposition 2.1.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓨 : MeasurableSpace 𝓨}
  {S T : Set (Measure Ω)} {p q : Ω → ℝ≥0∞} {E : Ω → ℝ≥0∞} {P : Measure Ω}

/-- A measurable `p : Ω → ℝ≥0∞` is a **p-variable** for the null `S` when
`P {ω | p ω ≤ α} ≤ α` for every `P ∈ S` and every level `α`. -/
structure IsPVar (p : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop where
  measurable : Measurable p := by fun_prop
  measure_le_le : ∀ P ∈ S, ∀ α : ℝ≥0∞, P {ω | p ω ≤ α} ≤ α

/-- For a simple null `{P}`, a p-variable is a measurable `p` with `P {p ≤ α} ≤ α` for every
`α`. -/
theorem isPVar_singleton_iff :
    IsPVar p {P} ↔ Measurable p ∧ ∀ α : ℝ≥0∞, P {ω | p ω ≤ α} ≤ α :=
  ⟨fun h ↦ ⟨h.measurable, h.measure_le_le P rfl⟩, fun h ↦ ⟨h.1, fun _ hQ ↦ hQ ▸ h.2⟩⟩

theorem IsPVar.anti_set (hST : S ⊆ T) (hp : IsPVar p T) : IsPVar p S where
  measurable := hp.measurable
  measure_le_le P hP := hp.measure_le_le P (hST hP)

theorem IsPVar.union (hS : IsPVar p S) (hT : IsPVar p T) : IsPVar p (S ∪ T) where
  measurable := hS.measurable
  measure_le_le P hP := hP.elim (hS.measure_le_le P) (hT.measure_le_le P)

theorem isPVar_union_iff : IsPVar p (S ∪ T) ↔ IsPVar p S ∧ IsPVar p T :=
  ⟨fun h ↦ ⟨h.anti_set subset_union_left, h.anti_set subset_union_right⟩,
    fun h ↦ h.1.union h.2⟩

/-- A measurable function almost surely at least a p-variable, under every member of the null, is a
p-variable. -/
theorem IsPVar.mono (hp : IsPVar p S) (hq : Measurable q) (hpq : ∀ P ∈ S, p ≤ᵐ[P] q) :
    IsPVar q S where
  measurable := hq
  measure_le_le P hP α := by
    refine le_trans (measure_mono_ae ?_) (hp.measure_le_le P hP α)
    filter_upwards [hpq P hP] with ω hω hqα using hω.trans hqα

theorem IsPVar.congr (hp : IsPVar p S) (hq : Measurable q) (hpq : ∀ P ∈ S, p =ᵐ[P] q) :
    IsPVar q S :=
  hp.mono hq fun P hP ↦ (hpq P hP).le

/-- The composition of a p-variable with a measurable map is a p-variable for the null of the
measures whose image is in the original null. -/
theorem IsPVar.comp {q : 𝓨 → ℝ≥0∞} {φ : Ω → 𝓨} (hφ : Measurable φ)
    (h : IsPVar q {P.map φ | P ∈ S}) : IsPVar (q ∘ φ) S where
  measurable := h.measurable.comp hφ
  measure_le_le P hP α := by
    have h_le := h.measure_le_le (P.map φ) ⟨P, hP, rfl⟩ α
    rwa [Measure.map_apply hφ (measurableSet_le h.measurable measurable_const)] at h_le

/-- **E-to-p calibration**: for a null of probability measures, the inverse `E⁻¹` of an
e-variable `E` is a p-variable. -/
theorem IsEVar.isPVar_inv (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hE : IsEVar E S) :
    IsPVar (fun ω ↦ (E ω)⁻¹) S where
  measurable := hE.measurable.inv
  measure_le_le P hP α := by
    have := hS P hP
    have h_set : {ω | (E ω)⁻¹ ≤ α} = {ω | α⁻¹ ≤ E ω} :=
      Set.ext fun _ ↦ ENNReal.inv_le_iff_inv_le
    rw [h_set]
    exact hE.measure_inv_le_le hP α

/-! ### Exact p-variables -/

/-- A p-variable `p` for `S` is **exact** when `P {ω | p ω ≤ α} = α` for every `P ∈ S` and every
`α ≤ 1`: under a probability measure of the null, `p` is then almost surely at most `1`
(`IsExactPVar.ae_le_one`) and uniformly distributed on `[0, 1]`. -/
structure IsExactPVar (p : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop extends IsPVar p S where
  measure_le_eq : ∀ P ∈ S, ∀ α ≤ 1, P {ω | p ω ≤ α} = α

theorem IsExactPVar.anti_set (hST : S ⊆ T) (hp : IsExactPVar p T) : IsExactPVar p S where
  toIsPVar := hp.toIsPVar.anti_set hST
  measure_le_eq P hP := hp.measure_le_eq P (hST hP)

theorem IsExactPVar.congr (hp : IsExactPVar p S) (hq : Measurable q)
    (hpq : ∀ P ∈ S, p =ᵐ[P] q) : IsExactPVar q S where
  toIsPVar := hp.toIsPVar.congr hq hpq
  measure_le_eq P hP α hα := by
    refine (measure_congr ?_).trans (hp.measure_le_eq P hP α hα)
    filter_upwards [hpq P hP] with ω hω
    simp [hω]

/-- The composition of an exact p-variable with a measurable map is an exact p-variable for the
null of the measures whose image is in the original null. -/
theorem IsExactPVar.comp {q : 𝓨 → ℝ≥0∞} {φ : Ω → 𝓨} (hφ : Measurable φ)
    (h : IsExactPVar q {P.map φ | P ∈ S}) : IsExactPVar (q ∘ φ) S where
  toIsPVar := h.toIsPVar.comp hφ
  measure_le_eq P hP α hα := by
    have h_eq := h.measure_le_eq (P.map φ) ⟨P, hP, rfl⟩ α hα
    rwa [Measure.map_apply hφ (measurableSet_le h.measurable measurable_const)] at h_eq

/-- An exact p-variable is almost surely at most `1` under every probability measure of the
null. -/
theorem IsExactPVar.ae_le_one (hp : IsExactPVar p S) (hP : P ∈ S) [IsProbabilityMeasure P] :
    ∀ᵐ ω ∂P, p ω ≤ 1 := by
  rw [ae_iff_measure_eq (measurableSet_le hp.measurable measurable_const).nullMeasurableSet,
    hp.measure_le_eq P hP 1 le_rfl, measure_univ]

/-- The identity of `[0, 1]`, under the Lebesgue measure on `[0, 1]`, is an exact p-variable. -/
theorem isExactPVar_ofReal_volume :
    IsExactPVar (fun x : ℝ ↦ ENNReal.ofReal x) {volume.restrict (Icc 0 1)} := by
  -- the distribution function of the uniform law: `{x ∈ [0, 1] | x ≤ α}` has measure `min α 1`
  have h_eq (α : ℝ≥0∞) :
      volume.restrict (Icc (0 : ℝ) 1) {x | ENNReal.ofReal x ≤ α} = min α 1 := by
    rcases eq_or_ne α ∞ with rfl | hα
    · simp
    have h_set : {x : ℝ | ENNReal.ofReal x ≤ α} ∩ Icc 0 1 = Icc 0 (min α.toReal 1) := by
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, le_min_iff,
        ENNReal.ofReal_le_iff_le_toReal hα]
      tauto
    rw [Measure.restrict_apply (measurableSet_le ENNReal.measurable_ofReal measurable_const), h_set]
    simp [ENNReal.ofReal_min, hα]
  refine ⟨⟨ENNReal.measurable_ofReal, fun P hP α ↦ ?_⟩, fun P hP α hα ↦ ?_⟩
  · rw [mem_singleton_iff.1 hP, h_eq]
    exact min_le_left α 1
  · rw [mem_singleton_iff.1 hP, h_eq, min_eq_left hα]

/-- A real random variable `U` uniformly distributed on `[0, 1]` under every member of the null
`S` is an exact p-variable for `S`. -/
theorem isExactPVar_ofReal_of_map_eq {U : Ω → ℝ} (hU : Measurable U)
    (hU_law : ∀ P ∈ S, P.map U = volume.restrict (Icc 0 1)) :
    IsExactPVar (fun ω ↦ ENNReal.ofReal (U ω)) S := by
  refine IsExactPVar.comp (q := fun x : ℝ ↦ ENNReal.ofReal x) hU
    (isExactPVar_ofReal_volume.anti_set ?_)
  rintro _ ⟨P, hP, rfl⟩
  exact hU_law P hP

end ProbabilityTheory
