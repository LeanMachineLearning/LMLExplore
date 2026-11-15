/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EffectiveSet
public import LMLExplore.EValues.EVariable
public import LMLExplore.MeasureTheory.Measure.AbsolutelyContinuousSet

/-!
# Identifying numeraires through the effective null

The numeraire of a null `S` under an alternative `Q` is Statlib's `IsNumeraire X S Q`: the
e-variable `X` for which `∫⁻ Y / X ∂Q` is at most the `Q`-mass of `{0 < X < ∞}` for every
e-variable `Y`, which is the log-optimal e-variable. Statlib proves that it exists and is unique;
this file gives a way to recognise it. To an e-variable `X` that is `Q`-almost surely finite
associate the measure `Q.withDensity X⁻¹`, under which every e-variable `Y` has expectation
`∫⁻ Y / X ∂Q`. Then `X` is the numeraire exactly when this measure belongs to the effective null
`effectiveSet S`, and, when the members of `S` are finite measures, it is then Statlib's reverse
information projection `ripr Q S` [LRR25, Theorem 4.1]. When `Q` is absolutely continuous with
respect to a null of finite measures, the numeraire is the only e-variable that is the likelihood
ratio of `Q` against an element of the effective null equivalent to `Q` [RW, Theorem 6.15].

The finiteness of `X` is automatic when `Q` is absolutely continuous with respect to the null,
`Q.AbsolutelyContinuousSet S`, defined in
`LMLExplore.MeasureTheory.Measure.AbsolutelyContinuousSet`: every measurable set that is null for
every member of `S` is `Q`-null. This holds exactly when every e-variable for `S` is `Q`-almost
surely finite (`ProbabilityTheory.absolutelyContinuousSet_iff_forall_isEVar_ae_ne_top`, in
`LMLExplore.EValues.EVariable`) [LRR25, Theorem 2.6].

The verification theorem turns the search for the numeraire into checking one integral inequality
per e-variable, or per member of the null. For a likelihood ratio `Q.rnDeriv R` against a member
`R` of the effective null with `Q ≪ R`, it suffices that the likelihood ratio is an e-variable;
with densities `q`, `p` and `r` with respect to a reference measure, this is the dominated
criterion `∫⁻ p / r ∂Q ≤ 1` for every `P ∈ S` [LRR25, Theorem 4.7]; and for a null described by
a generating family of e-variables, it suffices to check the generating family [LRR25,
Corollary 4.2]. The simple null `{P}` with `Q ≪ P`, whose numeraire is the likelihood ratio
`Q.rnDeriv P` [RW, Theorem 3.20], is the first instance. No dominating measure, convexity or
topology is assumed, except in the dominated criterion, which names its reference measure.

## Main statements

* `ProbabilityTheory.withDensity_inv_mem_effectiveSet_iff`: `Q.withDensity X⁻¹` is in the
  effective null exactly when `∫⁻ Y / X ∂Q ≤ 1` for every e-variable `Y`.
* `ProbabilityTheory.isNumeraire_iff_withDensity_inv_mem_effectiveSet`: **the verification
  theorem** [LRR25, Theorem 4.1]: a `Q`-almost surely finite e-variable `X` is the numeraire
  exactly when `Q.withDensity X⁻¹` is in the effective null.
* `ProbabilityTheory.IsNumeraire.ripr_eq_withDensity`: for a finite `Q` and a null of finite
  measures, the reverse information projection is then `Q.withDensity X⁻¹`, and, for `Q`
  absolutely continuous with respect to the null, `Q` is absolutely continuous with respect to it
  (`MeasureTheory.Measure.AbsolutelyContinuousSet.absolutelyContinuous_ripr`).
* `ProbabilityTheory.isNumeraire_iff_exists_ae_eq_rnDeriv`: for `Q` absolutely continuous with
  respect to a null of finite measures, the numeraire is the only e-variable that is `Q`-almost
  surely the likelihood ratio of `Q` against an element of the effective null equivalent to `Q`
  [RW, Theorem 6.15].
* `ProbabilityTheory.isNumeraire_iff_isEVar_of_ae_eq_rnDeriv`,
  `ProbabilityTheory.isNumeraire_rnDeriv_iff`, `ProbabilityTheory.ripr_eq_of_isEVar_rnDeriv`:
  for `R` in the effective null with `Q ≪ R`, a function `Q`-almost surely equal to the likelihood
  ratio `Q.rnDeriv R` is the numeraire as soon as it is an e-variable, and `R` is then the reverse
  information projection when `R ≪ Q` and the members of `S` are finite measures.
* `ProbabilityTheory.isNumeraire_rnDeriv_singleton`: the likelihood ratio `Q.rnDeriv P` is the
  numeraire of the simple null `{P}` when `Q ≪ P` [RW, Theorem 3.20]. Its expected logarithm is
  Statlib's `maxUtility_singleton_eq_klDiv`.
* `ProbabilityTheory.isNumeraire_div_rnDeriv_iff`: **the dominated criterion** [LRR25,
  Theorem 4.7].
* `ProbabilityTheory.IsEVar.isNumeraire_of_generating`: **the criterion with a generating family**
  [LRR25, Corollary 4.2].

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 2.6, Theorem 4.1,
  Corollary 4.2 and Theorem 4.7.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Theorems 3.20 and 6.15.
-/

public section

open MeasureTheory Set

open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {P Q R : Measure Ω}
  {X : Ω → ℝ≥0∞}

namespace ProbabilityTheory

open Measure

/-! ### The verification theorem -/

/-- The measure `Q.withDensity X⁻¹` is in the effective null exactly when every e-variable `Y`
has `∫⁻ Y / X ∂Q ≤ 1`: under `Q.withDensity X⁻¹`, `Y` has expectation `∫⁻ Y / X ∂Q`. -/
theorem withDensity_inv_mem_effectiveSet_iff (hX : Measurable X) :
    Q.withDensity X⁻¹ ∈ effectiveSet S ↔ ∀ Y, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂Q ≤ 1 := by
  refine forall₂_congr fun Y hY ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hX.inv hY.measurable]
  simp [ENNReal.div_eq_inv_mul]

/-- The measure `Q.withDensity X⁻¹` of a numeraire `X` is in the effective null. -/
theorem IsNumeraire.withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hX : IsNumeraire X S Q) : Q.withDensity X⁻¹ ∈ effectiveSet S :=
  (withDensity_inv_mem_effectiveSet_iff hX.isEVar.measurable).mpr fun _ ↦ hX.lintegral_div_le_one

/-- A `Q`-almost surely finite e-variable `X` for which `Q.withDensity X⁻¹` is in the effective
null is the numeraire. -/
theorem isNumeraire_of_withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) (h : Q.withDensity X⁻¹ ∈ effectiveSet S) :
    IsNumeraire X S Q := by
  have h_div := (withDensity_inv_mem_effectiveSet_iff hX.measurable).mp h
  -- The expectation of `X⁻¹` is finite, so that `X` is almost surely positive.
  have hX_zero : ∀ᵐ ω ∂Q, X ω ≠ 0 := by
    have h_inv : ∫⁻ ω, (X ω)⁻¹ ∂Q ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (by simpa using h_div 1 (isEVar_one S))
    filter_upwards [ae_lt_top hX.measurable.inv h_inv] with ω hω
    simpa using hω.ne
  have h_supp : Q X.fsupport = 1 := by
    rw [← prob_compl_eq_zero_iff hX.measurable_fsupport, Function.fsupport_compl,
      ← nonpos_iff_eq_zero]
    refine (measure_union_le _ _).trans ?_
    simp only [nonpos_iff_eq_zero, add_eq_zero]
    exact ⟨by simpa using ae_iff.mp hX_top, by simpa using ae_iff.mp hX_zero⟩
  exact isNumeraire_of_lintegral_div_le hX (by simp [h_supp]) fun Y hY ↦ h_supp ▸ h_div Y hY

/-- **The verification theorem** [LRR25, Theorem 4.1]: a `Q`-almost surely finite e-variable `X`
is the numeraire exactly when `Q.withDensity X⁻¹` is in the effective null. For `Q` absolutely
continuous with respect to the null, every e-variable is `Q`-almost surely finite
(`MeasureTheory.Measure.AbsolutelyContinuousSet.ae_ne_top`). -/
theorem isNumeraire_iff_withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) :
    IsNumeraire X S Q ↔ Q.withDensity X⁻¹ ∈ effectiveSet S :=
  ⟨IsNumeraire.withDensity_inv_mem_effectiveSet,
    isNumeraire_of_withDensity_inv_mem_effectiveSet hX hX_top⟩

/-- A `Q`-almost surely finite `X` for which `Q.withDensity X⁻¹` lies below a member of the
effective null is the numeraire as soon as it is an e-variable. -/
theorem isNumeraire_iff_isEVar_of_withDensity_inv_le [IsProbabilityMeasure Q]
    (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) (hR : R ∈ effectiveSet S) (h : Q.withDensity X⁻¹ ≤ R) :
    IsNumeraire X S Q ↔ IsEVar X S :=
  ⟨IsNumeraire.isEVar, fun hX ↦ isNumeraire_of_withDensity_inv_mem_effectiveSet hX hX_top
    (mem_effectiveSet_of_le hR h)⟩

/-- For a finite measure `Q` and a null `S` of finite measures, the reverse information
projection of `Q` onto `S` is `Q.withDensity X⁻¹` for the numeraire `X` [LRR25, Theorem 4.1]. -/
theorem IsNumeraire.ripr_eq_withDensity [IsFiniteMeasure Q] (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hX : IsNumeraire X S Q) : ripr Q S = Q.withDensity X⁻¹ := by
  rw [ripr]
  exact withDensity_congr_ae <| (hX.ae_eq_numeraire hS).symm.mono fun ω hω ↦ by simp [hω]

/-- For `Q` absolutely continuous with respect to `S`, `Q` is absolutely continuous with respect
to its reverse information projection onto `S`. The reverse `ripr Q S ≪ Q` holds because
`ripr Q S` is a measure with density with respect to `Q` (`withDensity_absolutelyContinuous`). -/
theorem _root_.MeasureTheory.Measure.AbsolutelyContinuousSet.absolutelyContinuous_ripr
    (hQS : Q.AbsolutelyContinuousSet S) : Q ≪ ripr Q S :=
  absolutelyContinuous_ripr_of_ae_ne_top (hQS.ae_ne_top (isEVar_numeraire Q S))

/-! ### Likelihood ratios against the effective null -/

/-- For `R` in the effective null with `Q ≪ R`, a function `X` that is `Q`-almost surely the
likelihood ratio `Q.rnDeriv R` is the numeraire exactly when it is an e-variable. -/
theorem isNumeraire_iff_isEVar_of_ae_eq_rnDeriv [IsProbabilityMeasure Q] (hR : R ∈ effectiveSet S)
    (hQR : Q ≪ R) (hXR : X =ᵐ[Q] Q.rnDeriv R) : IsNumeraire X S Q ↔ IsEVar X S := by
  have := isFiniteMeasure_of_mem_effectiveSet hR
  have hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞ := by
    filter_upwards [hXR, hQR.ae_le (rnDeriv_ne_top Q R)] with ω h h_top
    rwa [h]
  -- `Q.withDensity X⁻¹ = Q.withDensity (R.rnDeriv Q)` lies below `R`.
  exact isNumeraire_iff_isEVar_of_withDensity_inv_le hX_top hR
    ((withDensity_congr_ae (f := X⁻¹) (g := R.rnDeriv Q)
      ((hXR.fun_comp Inv.inv).trans (inv_rnDeriv hQR))).trans_le (withDensity_rnDeriv_le R Q))

/-- For `R` in the effective null with `Q ≪ R`, the likelihood ratio `Q.rnDeriv R` is the
numeraire exactly when it is an e-variable. -/
theorem isNumeraire_rnDeriv_iff [IsProbabilityMeasure Q] (hR : R ∈ effectiveSet S)
    (hQR : Q ≪ R) : IsNumeraire (Q.rnDeriv R) S Q ↔ IsEVar (Q.rnDeriv R) S :=
  isNumeraire_iff_isEVar_of_ae_eq_rnDeriv hR hQR .rfl

/-- For a null `S` of finite measures and `R` in the effective null equivalent to `Q`, if the
likelihood ratio `Q.rnDeriv R` is an e-variable, then `R` is the reverse information projection
of `Q` onto `S`. -/
theorem ripr_eq_of_isEVar_rnDeriv [IsProbabilityMeasure Q] (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hR : R ∈ effectiveSet S) (hQR : Q ≪ R) (hRQ : R ≪ Q) (hX : IsEVar (Q.rnDeriv R) S) :
    ripr Q S = R := by
  have := isFiniteMeasure_of_mem_effectiveSet hR
  rw [((isNumeraire_rnDeriv_iff hR hQR).mpr hX).ripr_eq_withDensity hS,
    withDensity_congr_ae (inv_rnDeriv hQR), withDensity_rnDeriv_eq R Q hRQ]

/-- For `Q` absolutely continuous with respect to a null of finite measures, the numeraire is the
only e-variable that is `Q`-almost surely the likelihood ratio of `Q` against an element of the
effective null equivalent to `Q` [LRR25, Theorem 4.1; RW, Theorem 6.15]. -/
theorem isNumeraire_iff_exists_ae_eq_rnDeriv [IsProbabilityMeasure Q]
    (hS : ∀ P ∈ S, IsFiniteMeasure P) (hQS : Q.AbsolutelyContinuousSet S) :
    IsNumeraire X S Q ↔
      IsEVar X S ∧ ∃ R ∈ effectiveSet S, Q ≪ R ∧ R ≪ Q ∧ X =ᵐ[Q] Q.rnDeriv R := by
  refine ⟨fun hX ↦ ⟨hX.isEVar, ripr Q S, ripr_mem_effectiveSet Q hS, hQS.absolutelyContinuous_ripr,
    by rw [ripr]; exact withDensity_absolutelyContinuous _ _, ?_⟩,
    fun ⟨hX, R, hR, hQR, _, hXR⟩ ↦ (isNumeraire_iff_isEVar_of_ae_eq_rnDeriv hR hQR hXR).mpr hX⟩
  exact (hX.ae_eq_numeraire hS).trans
    (rnDeriv_ripr hS (hQS.ae_ne_top (isEVar_numeraire Q S))).symm

/-- **The likelihood ratio is the numeraire of a simple null** [RW, Theorem 3.20]: for
probability measures `Q ≪ P`, `Q.rnDeriv P` is the numeraire of `{P}` under `Q`. Its expected
logarithm, the maximal expected logarithm of an e-variable for `{P}`, is `klDiv Q P` (Statlib's
`ProbabilityTheory.maxUtility_singleton_eq_klDiv`). -/
theorem isNumeraire_rnDeriv_singleton [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (hQP : Q ≪ P) : IsNumeraire (Q.rnDeriv P) {P} Q :=
  (isNumeraire_rnDeriv_iff (subset_effectiveSet (by simp) rfl) hQP).mpr
    (isExactEVar_rnDeriv hQP (by simp)).toIsEVar

/-- For probability measures `Q ≪ P` with `P ≪ Q`, the reverse information projection of `Q`
onto `{P}` is `P`. -/
theorem ripr_singleton_eq [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hQP : Q ≪ P)
    (hPQ : P ≪ Q) : ripr Q {P} = P :=
  ripr_eq_of_isEVar_rnDeriv (by rintro _ rfl; infer_instance)
    (subset_effectiveSet (by simp) rfl) hQP hPQ (isExactEVar_rnDeriv hQP (by simp)).toIsEVar

/-! ### The dominated criterion -/

/-- **The dominated criterion** [LRR25, Theorem 4.7]. Let `Q` and the members of a null `S` of
probability measures be absolutely continuous with respect to a σ-finite measure `μ`, with
densities `q` and `p`, and let `R` be a member of the effective null with density `r` and
`Q ≪ R`. Then `q / r` is the numeraire exactly when `∫⁻ p / r ∂Q ≤ 1` for every `P ∈ S`. -/
theorem isNumeraire_div_rnDeriv_iff [IsProbabilityMeasure Q] {μ : Measure Ω} [SigmaFinite μ]
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hSμ : ∀ P ∈ S, P ≪ μ) (hQμ : Q ≪ μ)
    (hR : R ∈ effectiveSet S) (hQR : Q ≪ R) :
    IsNumeraire (fun ω ↦ Q.rnDeriv μ ω / R.rnDeriv μ ω) S Q ↔
      ∀ P ∈ S, ∫⁻ ω, P.rnDeriv μ ω / R.rnDeriv μ ω ∂Q ≤ 1 := by
  have := isFiniteMeasure_of_mem_effectiveSet hR
  have hRμ : R ≪ μ := absolutelyContinuous_of_mem_effectiveSet hR hSμ
  have hX_meas : Measurable fun ω ↦ Q.rnDeriv μ ω / R.rnDeriv μ ω := by fun_prop
  -- `q / r` is `Q`-almost surely the likelihood ratio `Q.rnDeriv R`.
  have h_eq : (fun ω ↦ Q.rnDeriv μ ω / R.rnDeriv μ ω) =ᵐ[Q] Q.rnDeriv R :=
    hQR.ae_le (rnDeriv_eq_div hQμ hRμ).symm
  rw [isNumeraire_iff_isEVar_of_ae_eq_rnDeriv hR hQR h_eq, isEVar_iff_lintegral_le_one hS,
    and_iff_right hX_meas]
  refine forall₂_congr fun P hP ↦ ?_
  have := hS P hP
  -- `∫⁻ q / r ∂P = ∫⁻ p * (q / r) ∂μ = ∫⁻ q * (p / r) ∂μ = ∫⁻ p / r ∂Q`.
  rw [← lintegral_rnDeriv_mul (hSμ P hP) hX_meas.aemeasurable,
    ← lintegral_rnDeriv_mul hQμ
      (by fun_prop : Measurable fun ω ↦ P.rnDeriv μ ω / R.rnDeriv μ ω).aemeasurable]
  simp_rw [div_eq_mul_inv, mul_left_comm (P.rnDeriv μ _)]

/-! ### Generating families -/

/-- **The criterion with a generating family** [LRR25, Corollary 4.2]. Let `𝓔₀` be a family of
measurable functions that generates the null `S`, in the sense that every probability measure
under which each member of `𝓔₀` has expectation at most `1` is in `S`. A `Q`-almost surely finite
e-variable `X` with `∫⁻ X⁻¹ ∂Q = 1` and `∫⁻ Y / X ∂Q ≤ 1` for every `Y ∈ 𝓔₀` is the numeraire,
and `Q.withDensity X⁻¹`, the reverse information projection when `S` consists of finite
measures, belongs to `S`. -/
theorem IsEVar.isNumeraire_of_generating [IsProbabilityMeasure Q] {𝓔₀ : Set (Ω → ℝ≥0∞)}
    (h𝓔₀ : ∀ Y ∈ 𝓔₀, Measurable Y)
    (hS : ∀ P : Measure Ω, IsProbabilityMeasure P → (∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω ∂P ≤ 1) → P ∈ S)
    (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) (hX_inv : ∫⁻ ω, (X ω)⁻¹ ∂Q = 1)
    (hX_div : ∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω / X ω ∂Q ≤ 1) :
    IsNumeraire X S Q ∧ Q.withDensity X⁻¹ ∈ S := by
  have : IsProbabilityMeasure (Q.withDensity X⁻¹) :=
    ⟨by rw [withDensity_apply _ .univ, setLIntegral_univ]; exact hX_inv⟩
  have h_mem : Q.withDensity X⁻¹ ∈ S := hS _ this fun Y hY ↦ by
    rw [lintegral_withDensity_eq_lintegral_mul _ hX.measurable.inv (h𝓔₀ Y hY)]
    simpa [ENNReal.div_eq_inv_mul] using hX_div Y hY
  -- As a probability measure of `S`, `Q.withDensity X⁻¹` is in the effective null.
  refine ⟨isNumeraire_of_withDensity_inv_mem_effectiveSet hX hX_top fun Y hY ↦ ?_, h_mem⟩
  simpa using hY.lintegral_le_measure_univ _ h_mem

end ProbabilityTheory
