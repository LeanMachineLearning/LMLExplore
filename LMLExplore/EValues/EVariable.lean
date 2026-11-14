/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import LMLExplore.Probability.Independence.Integration
public import Statlib.EValues.EVariable

/-!
# Exact e-variables, Markov's inequality and products of independent e-variables

An e-variable for a null hypothesis `S : Set (Measure Ω)` (Statlib's `ProbabilityTheory.IsEVar`)
is a measurable `E : Ω → ℝ≥0∞` with `∫ᵉ ω, E ω - 1 ∂P ≠ ⊥` and `∫ᵉ ω, E ω - 1 ∂P ≤ 0` for every
`P ∈ S`. For a null of finite measures this says `∫⁻ E ∂P ≤ P univ` for every `P ∈ S`
(`ProbabilityTheory.IsEVar.of_lintegral_le_measure_univ`,
`ProbabilityTheory.IsEVar.lintegral_le_measure_univ`), that is, `E` has expectation at most one
under every probability measure of `S`. This file develops the first properties of e-variables
that hypothesis testing uses:

* the exact e-variables, with `∫⁻ E ∂P = P univ` for every `P ∈ S`;
* Markov's inequality, which makes `{α⁻¹ ≤ E}` the rejection region of a level-`α` test, and its
  smoothed form `min (α * E) 1`;
* products of e-variables from a family that is independent under every member of the null.

Following Statlib, the null is an arbitrary set of measures, with no dominating measure, and
e-variables are `ℝ≥0∞`-valued.

## Main definitions

* `ProbabilityTheory.IsExactEVar E S`: `E` is an e-variable for `S` with `∫⁻ E ∂P = P univ` for
  every `P ∈ S`, that is, with expectation exactly one under every probability measure of `S`.

## Main statements

* `ProbabilityTheory.IsEVar.lintegral_le_one`: an e-variable has expectation at most one under
  every probability measure of the null.
* `ProbabilityTheory.isEVar_iff_lintegral_le_one`, `ProbabilityTheory.isExactEVar_iff`: for a null
  of probability measures, the e-variables and the exact e-variables in terms of `∫⁻`.
* `ProbabilityTheory.isExactEVar_rnDeriv`: for a finite measure `P`, a likelihood ratio
  `Q.rnDeriv P` with `Q ≪ P` and `Q univ = P univ` is an exact e-variable for `{P}`.
* `ProbabilityTheory.IsEVar.measure_inv_le_le`: **Markov's inequality** for e-variables,
  `P {ω | α⁻¹ ≤ E ω} ≤ α`.
* `ProbabilityTheory.IsEVar.lintegral_min_mul_le`: `∫⁻ ω, min (α * E ω) 1 ∂P ≤ α`.
* `ProbabilityTheory.isEVar_finsetProd`, `ProbabilityTheory.isExactEVar_finsetProd`: a finite
  product of (exact) e-variables, from a family that is independent under every member of the
  null, is an (exact) e-variable. Statlib's `ProbabilityTheory.IsEVar.prod` treats the two
  coordinates of a product space, where independence holds by construction.

## References

* A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Definition 1.2, Fact 1.3 and Proposition 2.1.
* V. Vovk and R. Wang, *E-values: calibration, combination and applications*, Ann. Statist. 49
  (2021).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓨 : MeasurableSpace 𝓨}
  {S T : Set (Measure Ω)} {E F : Ω → ℝ≥0∞} {P : Measure Ω}

/-- An e-variable has expectation at most one under every probability measure of the null. -/
theorem IsEVar.lintegral_le_one (hE : IsEVar E S) (hP : P ∈ S) [IsProbabilityMeasure P] :
    ∫⁻ ω, E ω ∂P ≤ 1 := by
  simpa using hE.lintegral_le_measure_univ P hP

/-- For a null of probability measures, `E` is an e-variable exactly when it is measurable and has
expectation at most one under every member of the null. -/
theorem isEVar_iff_lintegral_le_one (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    IsEVar E S ↔ Measurable E ∧ ∀ P ∈ S, ∫⁻ ω, E ω ∂P ≤ 1 := by
  refine ⟨fun hE ↦ ⟨hE.measurable, fun P hP ↦ ?_⟩,
    fun h ↦ IsEVar.of_lintegral_le_one hS h.1 h.2⟩
  have := hS P hP
  exact hE.lintegral_le_one hP

/-! ### Exact e-variables -/

/-- An e-variable `E` for `S` is **exact** when `∫⁻ E ∂P = P univ` for every `P ∈ S`: for a null of
probability measures, its expectation is exactly one under every member of the null. The
normalization by `P univ` matches the one of Statlib's `IsEVar`, which asks
`∫⁻ E ∂P ≤ P univ` for a finite measure `P`. -/
structure IsExactEVar (E : Ω → ℝ≥0∞) (S : Set (Measure Ω)) : Prop extends IsEVar E S where
  lintegral_eq_measure_univ : ∀ P ∈ S, ∫⁻ ω, E ω ∂P = P univ

/-- An exact e-variable has expectation one under every probability measure of the null. -/
theorem IsExactEVar.lintegral_eq_one (hE : IsExactEVar E S) (hP : P ∈ S)
    [IsProbabilityMeasure P] :
    ∫⁻ ω, E ω ∂P = 1 := by
  simpa using hE.lintegral_eq_measure_univ P hP

/-- For a null of probability measures, `E` is an exact e-variable exactly when it is measurable
and has expectation one under every member of the null. -/
theorem isExactEVar_iff (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    IsExactEVar E S ↔ Measurable E ∧ ∀ P ∈ S, ∫⁻ ω, E ω ∂P = 1 := by
  refine ⟨fun hE ↦ ⟨hE.measurable, fun P hP ↦ have := hS P hP; hE.lintegral_eq_one hP⟩,
    fun h ↦ ⟨IsEVar.of_lintegral_le_one hS h.1 fun P hP ↦ (h.2 P hP).le, fun P hP ↦ ?_⟩⟩
  have := hS P hP
  simpa using h.2 P hP

theorem IsExactEVar.of_lintegral_eq_one (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : Measurable E) (h : ∀ P ∈ S, ∫⁻ ω, E ω ∂P = 1) :
    IsExactEVar E S :=
  (isExactEVar_iff hS).2 ⟨hE, h⟩

/-- The constant `1` is an exact e-variable for every null. -/
theorem isExactEVar_one (S : Set (Measure Ω)) : IsExactEVar 1 S where
  toIsEVar := isEVar_one S
  lintegral_eq_measure_univ P _ := by simp

theorem IsExactEVar.anti_set (hST : S ⊆ T) (hE : IsExactEVar E T) : IsExactEVar E S where
  toIsEVar := hE.toIsEVar.anti_set hST
  lintegral_eq_measure_univ P hP := hE.lintegral_eq_measure_univ P (hST hP)

theorem IsExactEVar.congr (hE : IsExactEVar E S) (hF : Measurable F)
    (hEF : ∀ P ∈ S, E =ᵐ[P] F) : IsExactEVar F S where
  toIsEVar := hE.toIsEVar.congr hF hEF
  lintegral_eq_measure_univ P hP := by
    rw [← lintegral_congr_ae (hEF P hP), hE.lintegral_eq_measure_univ P hP]

/-- The composition of an exact e-variable with a measurable map is an exact e-variable for the
null of the measures whose image is in the original null. -/
theorem IsExactEVar.comp {Y : 𝓨 → ℝ≥0∞} {φ : Ω → 𝓨} (hφ : Measurable φ)
    (h : IsExactEVar Y {P.map φ | P ∈ S}) : IsExactEVar (Y ∘ φ) S where
  toIsEVar := h.toIsEVar.comp hφ
  lintegral_eq_measure_univ P hP := by
    have h_eq := h.lintegral_eq_measure_univ (P.map φ) ⟨P, hP, rfl⟩
    rwa [lintegral_map h.measurable hφ, Measure.map_apply hφ .univ, preimage_univ] at h_eq

/-- A likelihood ratio `Q.rnDeriv P`, for `Q ≪ P` with the same finite total mass, is an exact
e-variable for the simple null `{P}`. -/
theorem isExactEVar_rnDeriv {Q : Measure Ω} [IsFiniteMeasure P] [Q.HaveLebesgueDecomposition P]
    (hQP : Q ≪ P) (hQ : Q univ = P univ) :
    IsExactEVar (Q.rnDeriv P) {P} where
  toIsEVar := .of_lintegral_le_measure_univ (by simpa) (Measure.measurable_rnDeriv Q P)
    (by simp [Measure.lintegral_rnDeriv hQP, hQ])
  lintegral_eq_measure_univ := by simp [Measure.lintegral_rnDeriv hQP, hQ]

/-! ### Markov's inequality -/

/-- **Markov's inequality** for e-variables: for every probability measure `P` of the null and
every level
`α`, the e-variable reaches `α⁻¹` with probability at most `α`. -/
theorem IsEVar.measure_inv_le_le (hE : IsEVar E S) (hP : P ∈ S) [IsProbabilityMeasure P]
    (α : ℝ≥0∞) :
    P {ω | α⁻¹ ≤ E ω} ≤ α := by
  rcases eq_or_ne α 0 with rfl | hα₀
  · -- at level `0`, the event is `{E = ∞}`, which is null since `E` is almost surely finite
    refine (measure_eq_zero_iff_ae_notMem.2 ?_).le
    filter_upwards [hE.ae_lt_top hP] with ω hω
    simpa using hω.ne
  rcases eq_or_ne α ∞ with rfl | hα_top
  · exact le_top
  calc P {ω | α⁻¹ ≤ E ω}
  _ ≤ (∫⁻ ω, E ω ∂P) / α⁻¹ :=
    meas_ge_le_lintegral_div hE.measurable.aemeasurable (by simpa) (by simpa)
  _ ≤ 1 / α⁻¹ := by
    gcongr
    exact hE.lintegral_le_one hP
  _ = α := by simp

/-- The test that rejects when an e-variable reaches `α⁻¹` has level `α` under every probability
measure of the null. -/
theorem IsEVar.lintegral_indicator_le (hE : IsEVar E S) (hP : P ∈ S) [IsProbabilityMeasure P]
    (α : ℝ≥0∞) :
    ∫⁻ ω, {ω | α⁻¹ ≤ E ω}.indicator 1 ω ∂P ≤ α := by
  rw [lintegral_indicator_one (measurableSet_le measurable_const hE.measurable)]
  exact hE.measure_inv_le_le hP α

/-- The randomized test `min (α * E) 1` of an e-variable `E` has expectation at most `α` under
every probability measure of the null. -/
theorem IsEVar.lintegral_min_mul_le (hE : IsEVar E S) (hP : P ∈ S) [IsProbabilityMeasure P]
    (α : ℝ≥0∞) :
    ∫⁻ ω, min (α * E ω) 1 ∂P ≤ α :=
  calc ∫⁻ ω, min (α * E ω) 1 ∂P
  _ ≤ ∫⁻ ω, α * E ω ∂P := lintegral_mono fun _ ↦ min_le_left _ _
  _ = α * ∫⁻ ω, E ω ∂P := lintegral_const_mul α hE.measurable
  _ ≤ α * 1 := by
    gcongr
    exact hE.lintegral_le_one hP
  _ = α := mul_one α

/-! ### Products of independent e-variables -/

/-- A finite product `∏ i ∈ s, E i` of e-variables is an e-variable when the whole family `E` is
independent under every member of the null, which makes the null a set of probability
measures. -/
theorem isEVar_finsetProd {ι : Type*} {E : ι → Ω → ℝ≥0∞} (s : Finset ι)
    (hE : ∀ i ∈ s, IsEVar (E i) S) (hind : ∀ P ∈ S, iIndepFun E P) :
    IsEVar (fun ω ↦ ∏ i ∈ s, E i ω) S := by
  have hS : ∀ P ∈ S, IsProbabilityMeasure P := fun P hP ↦ (hind P hP).isProbabilityMeasure
  refine .of_lintegral_le_one hS (Finset.measurable_fun_prod s fun i hi ↦ (hE i hi).measurable)
    fun P hP ↦ ?_
  have := hS P hP
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun' s (hind P hP)
    fun i hi ↦ (hE i hi).measurable]
  exact Finset.prod_le_one fun i hi ↦ (hE i hi).lintegral_le_one hP

/-- A finite product `∏ i ∈ s, E i` of exact e-variables is an exact e-variable when the whole
family `E` is independent under every member of the null, which makes the null a set of
probability measures. -/
theorem isExactEVar_finsetProd {ι : Type*} {E : ι → Ω → ℝ≥0∞} (s : Finset ι)
    (hE : ∀ i ∈ s, IsExactEVar (E i) S) (hind : ∀ P ∈ S, iIndepFun E P) :
    IsExactEVar (fun ω ↦ ∏ i ∈ s, E i ω) S := by
  have hS : ∀ P ∈ S, IsProbabilityMeasure P := fun P hP ↦ (hind P hP).isProbabilityMeasure
  refine .of_lintegral_eq_one hS (Finset.measurable_fun_prod s fun i hi ↦ (hE i hi).measurable)
    fun P hP ↦ ?_
  have := hS P hP
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun' s (hind P hP)
    fun i hi ↦ (hE i hi).measurable]
  exact Finset.prod_eq_one fun i hi ↦ (hE i hi).lintegral_eq_one hP

end ProbabilityTheory
