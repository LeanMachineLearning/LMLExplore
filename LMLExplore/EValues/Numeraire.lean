/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.RIPr
public import LMLExplore.EValues.EffectiveSet.Basic
public import LMLExplore.EValues.EVariable
public import LMLExplore.MeasureTheory.Measure.AbsolutelyContinuousSet
public import LMLExplore.MeasureTheory.Measure.WithDensity

/-!
# Identifying the numeraire through the effective null

Statlib constructs the numeraire `numeraire Q S` of a null `S` under an alternative `Q` and its
reverse information projection `ripr Q S = Q.withDensity (numeraire Q S)⁻¹`, but an abstract
existence theorem does not say which e-variable is the numeraire. This file gives the verification
criteria of Larsson, Ramdas and Ruf: an e-variable `X` is the numeraire exactly when the measure
`Q.withDensity X⁻¹`, suitably normalized, belongs to the effective null `effectiveSet S`. A
candidate numeraire is therefore checked against the null through one measure, with no
optimization over the e-variables.

Several statements assume that `Q` is absolutely continuous with respect to the null,
`Q.AbsolutelyContinuousSet S` (the `Q ≪ S` of [LRR25]): every measurable set charged by `Q` is
charged by some member of `S`. This holds exactly when every e-variable for `S` is `Q`-almost
surely finite (`ProbabilityTheory.absolutelyContinuousSet_iff_forall_isEVar_ae_ne_top`, in
`LMLExplore.EValues.EVariable`) [LRR25, Theorem 2.6], and the numeraire is then the only
e-variable that is a likelihood ratio of `Q` against an equivalent member of the effective null.
The verification theorem itself only needs the candidate numeraire to be `Q`-almost surely
finite. From `ProbabilityTheory.isNumeraire_iff_withDensity_inv_mem_effectiveSet` on, the members
of the null have mass at most `1`, so that the constant `1` is an e-variable and the numeraire is
almost surely positive.

## Main statements

* `ProbabilityTheory.isNumeraire_iff_smul_withDensity_inv_mem_effectiveSet`: for any finite `Q`
  and any null, an e-variable `X` is the numeraire exactly when `Q.withDensity X⁻¹`, divided by
  the mass under `Q` of the set where `X` is positive and finite, is in the effective null.
* `ProbabilityTheory.withDensity_inv_mem_effectiveSet_iff`: `Q.withDensity X⁻¹` is in the
  effective null exactly when `∫⁻ Y / X ∂Q ≤ 1` for every e-variable `Y`.
* `ProbabilityTheory.isNumeraire_iff_withDensity_inv_mem_effectiveSet`: a `Q`-almost surely
  finite e-variable `X` is the numeraire exactly when `Q.withDensity X⁻¹` is in the effective
  null [LRR25, Theorem 4.1].
* `ProbabilityTheory.IsNumeraire.ripr_eq`, `ProbabilityTheory.absolutelyContinuous_ripr`,
  `ProbabilityTheory.IsNumeraire.eq_withDensity_inv_of_le`: that measure is then the reverse
  information projection, it is equivalent to `Q`, and it is maximal among the members of the
  effective null absolutely continuous with respect to `Q` [LRR25, Theorem 4.1].
* `ProbabilityTheory.isNumeraire_iff_exists_ae_eq_rnDeriv`: for `Q ≪ S`, the numeraire is the
  only e-variable that is a likelihood ratio `Q.rnDeriv μ` against a member `μ` of the effective
  null equivalent to `Q` [LRR25, Theorem 4.1; RW, Theorem 6.15].
* `ProbabilityTheory.ripr_eq_of_isEVar_rnDeriv`, `ProbabilityTheory.ripr_singleton_eq`: a member
  `R` of the effective null equivalent to `Q` whose likelihood ratio `Q.rnDeriv R` is an
  e-variable is the reverse information projection; for a simple null `{P}` with `P` equivalent
  to `Q`, the reverse information projection is `P`.
* `ProbabilityTheory.isNumeraire_div_rnDeriv_iff`: **the dominated criterion** [LRR25,
  Theorem 4.7]: for a null `S` of measures of mass at most one, with densities `q` of `Q` and `p` of
  `P ∈ S` with respect to a σ-finite reference measure, and with `r` the density of a member `R`
  of the effective null with `Q ≪ R`, `q / r` is the numeraire exactly when `∫⁻ p / r ∂Q ≤ 1` for
  every `P ∈ S`.
* `ProbabilityTheory.isNumeraire_of_lintegral_div_le_one`,
  `ProbabilityTheory.ripr_mem_of_lintegral_div_le_one`: for a null `S` containing every
  probability measure under which each member of a family `𝓔₀` has expectation at most `1`, a
  `Q`-almost surely finite e-variable `X` with `∫⁻ X⁻¹ ∂Q = 1` and `∫⁻ Y / X ∂Q ≤ 1` for every
  `Y ∈ 𝓔₀` is the numeraire, and the reverse information projection then belongs to `S` [LRR25,
  Corollary 4.2].
* `ProbabilityTheory.isNumeraire_piecewise_rnDeriv_cond`: the numeraire of a simple null `{P}`
  with no absolute continuity: `∞` on a `P`-null set `N` off which `Q` is absolutely continuous
  with respect to `P`, and the likelihood ratio of `Q[|Nᶜ]` to `P` on `Nᶜ` [LRR25,
  Corollary 3.15]. Its integrals over sets under `P` are
  `ProbabilityTheory.setLIntegral_piecewise_rnDeriv_cond`, and a numeraire of `{P}` that is
  infinite on a measurable set `N` off which `Q` is absolutely continuous with respect to `P` is
  `Q`-almost surely positive and finite exactly off `N`
  (`ProbabilityTheory.IsNumeraire.ae_mem_fsupport_iff_notMem`).
* `ProbabilityTheory.IsNumeraire.nonempty_of_ae_ne_top`: a null with a numeraire that is almost
  surely finite under a nonzero alternative is not empty.
* `ProbabilityTheory.isNumeraire_rnDeriv`: for `Q ≪ P`, the likelihood ratio `Q.rnDeriv P` is the
  numeraire of `{P}` [RW, Theorem 3.20]; its expected logarithm is `klDiv Q P` by Statlib's
  `maxUtility_singleton_eq_klDiv`.
* `ProbabilityTheory.IsNumeraire.eq_of_countable`: on a countable space where `Q` charges every
  point, numeraires are unique everywhere.
* `ProbabilityTheory.isNumeraire_withDensity_of_mem_effectiveSet`,
  `ProbabilityTheory.IsNumeraire.lintegral_ripr_eq_one`,
  `ProbabilityTheory.exists_isNumeraire_ae_ne_top_iff`, `ProbabilityTheory.exists_isNumeraire_iff`:
  **which e-variables are numeraires** [EVR26, Note 42, Theorem 7]: for a null of measures of mass
  at most one, an e-variable `X` is a numeraire against some probability measure exactly when it
  is exact under a member `μ` of the effective null, `∫⁻ X ∂μ = 1`, or infinite at some point. It
  is then a numeraire against `μ.withDensity X`, respectively against the Dirac mass at that point;
  conversely a numeraire that is finite almost surely is exact under the reverse information
  projection.
* `ProbabilityTheory.isNumeraire_withDensity_of_mem_convexHull`: an e-variable is a numeraire
  against its tilt of any mixture of members under which it is exact [EVR26, Note 42,
  Theorem 9 (2)].
* `ProbabilityTheory.IsNumeraire.ae_ne_zero_of_isEVar_const`: a numeraire is almost surely
  positive as soon as some positive constant is an e-variable.

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Lemma 3.3, Theorem 2.6,
  Theorem 3.13, Corollary 3.15, Theorem 4.1, Corollary 4.2 and Theorem 4.7.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Theorems 3.20 and 6.15.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes and Lean
  library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 42, Theorems 7
  and 9, after its file `Results/NumeraireAdmissible.lean`.
-/

public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {Q P R μ : Measure Ω}
  {X : Ω → ℝ≥0∞}

/-! ### The numeraire through the effective null, for any alternative -/

/-- **The numeraire through the effective null.** For a finite measure `Q` and any null `S`, an
e-variable `X` for `S` is the numeraire of `S` under `Q` exactly when the measure of density `X⁻¹`
with respect to `Q`, divided by the mass `Q X.fsupport` of the set where `X` is positive and
finite, belongs to the effective null of `S`. The forward direction is [LRR25, Lemma 3.3,
Theorem 3.13], where `Q X.fsupport` is the mass of the set on which the numeraire is finite. -/
theorem isNumeraire_iff_smul_withDensity_inv_mem_effectiveSet [IsFiniteMeasure Q] :
    IsNumeraire X S Q ↔
      IsEVar X S ∧ (Q X.fsupport)⁻¹ • Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ effectiveSet S := by
  rw [isNumeraire_iff]
  refine and_congr_right fun hX ↦ ⟨fun h Y hY ↦ ?_, fun h Y hY ↦ ?_⟩
  all_goals
    have h_eq : ∫⁻ ω, Y ω ∂((Q X.fsupport)⁻¹ • Q.withDensity fun ω ↦ (X ω)⁻¹)
        = (∫⁻ ω, Y ω / X ω ∂Q) / Q X.fsupport := by
      rw [lintegral_smul_measure, smul_eq_mul,
        lintegral_withDensity_inv_eq_lintegral_div hX.measurable.aemeasurable
          hY.measurable.aemeasurable,
        ENNReal.div_eq_inv_mul]
    have h_iff : (∫⁻ ω, Y ω / X ω ∂Q) / Q X.fsupport ≤ 1 ↔ ∫⁻ ω, Y ω / X ω ∂Q ≤ Q X.fsupport := by
      rw [ENNReal.div_le_iff_le_mul (.inr ENNReal.one_ne_top) (.inr one_ne_zero), one_mul]
  · rw [h_eq, h_iff]
    exact h hY
  · rw [← h_iff, ← h_eq]
    exact h Y hY

/-- The measure of density `X⁻¹` with respect to `Q` is in the effective null when `X` is the
numeraire of `S` under the probability measure `Q` [LRR25, Lemma 3.3]. -/
theorem IsNumeraire.withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hX : IsNumeraire X S Q) : Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ effectiveSet S := by
  refine mem_effectiveSet_of_le
    ((isNumeraire_iff_smul_withDensity_inv_mem_effectiveSet.mp hX).2) fun s ↦ ?_
  rw [smul_apply, smul_eq_mul]
  refine le_mul_of_one_le_left zero_le (ENNReal.one_le_inv.mpr ?_)
  exact prob_le_one

/-- An e-variable `X` for `S` is the numeraire of `S` under a finite measure `Q` when the measure
of density `X⁻¹` with respect to `Q`, divided by `Q X.fsupport`, is setwise below a member of the
effective null. -/
theorem isNumeraire_of_smul_withDensity_inv_le [IsFiniteMeasure Q] (hX : IsEVar X S)
    (hμ : μ ∈ effectiveSet S)
    (hle : (Q X.fsupport)⁻¹ • Q.withDensity (fun ω ↦ (X ω)⁻¹) ≤ μ) :
    IsNumeraire X S Q :=
  isNumeraire_iff_smul_withDensity_inv_mem_effectiveSet.mpr ⟨hX, mem_effectiveSet_of_le hμ hle⟩

/-! ### Almost surely finite e-variables -/

/-- The finite support of a `Q`-almost surely positive and finite function has full measure under
`Q`. -/
theorem measure_fsupport_eq_measure_univ (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞)
    (hX₀ : ∀ᵐ ω ∂Q, X ω ≠ 0) : Q X.fsupport = Q univ :=
  measure_congr <| ae_eq_univ.mpr <| mem_ae_iff.mp <| by
    filter_upwards [hX_top, hX₀] with ω h_top h_zero using ⟨h_top, h_zero⟩

/-- **A null with an almost surely finite numeraire is not empty.** For the empty null, `∞` is an
e-variable, so a numeraire is almost surely infinite under a nonzero alternative `Q`. -/
theorem IsNumeraire.nonempty_of_ae_ne_top [NeZero Q] (hX : IsNumeraire X S Q)
    (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) : S.Nonempty := by
  refine ne_empty_iff_nonempty.1 fun h_empty ↦ ?_
  have hY : IsEVar (fun _ : Ω ↦ ∞) S := ⟨measurable_const, by simp [h_empty]⟩
  have h_false : ∀ᵐ ω ∂Q, False := by
    filter_upwards [hX.ae_eq_top_of_eq_top hY, hX_top] with ω h1 h2 using h2 (h1 rfl)
  exact NeZero.ne Q (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 h_false))

/-- The measure `Q.withDensity X⁻¹` is in the effective null exactly when every e-variable `Y`
has `∫⁻ Y / X ∂Q ≤ 1`: under `Q.withDensity X⁻¹`, `Y` has expectation `∫⁻ Y / X ∂Q`. -/
theorem withDensity_inv_mem_effectiveSet_iff (hX : Measurable X) :
    Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ effectiveSet S ↔
      ∀ Y, IsEVar Y S → ∫⁻ ω, Y ω / X ω ∂Q ≤ 1 :=
  forall₂_congr fun _ hY ↦ by
    rw [lintegral_withDensity_inv_eq_lintegral_div hX.aemeasurable hY.measurable.aemeasurable]

/-- A `Q`-almost surely finite and positive e-variable `X` for which `Q.withDensity X⁻¹` is in the
effective null is the numeraire. -/
theorem isNumeraire_of_ae_ne_zero_of_withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) (hX_zero : ∀ᵐ ω ∂Q, X ω ≠ 0)
    (h : Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ effectiveSet S) :
    IsNumeraire X S Q := by
  have h_div := (withDensity_inv_mem_effectiveSet_iff hX.measurable).mp h
  have h_supp : Q X.fsupport = 1 :=
    (measure_fsupport_eq_measure_univ hX_top hX_zero).trans measure_univ
  exact isNumeraire_of_lintegral_div_le hX (by simp [h_supp]) fun Y hY ↦ h_supp ▸ h_div Y hY

/-- For a null of measures of mass at most `1`, a `Q`-almost surely finite e-variable `X` for
which `Q.withDensity X⁻¹` is in the effective null is the numeraire. -/
theorem isNumeraire_of_withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞)
    (h : Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ effectiveSet S) :
    IsNumeraire X S Q := by
  refine isNumeraire_of_ae_ne_zero_of_withDensity_inv_mem_effectiveSet hX hX_top ?_ h
  -- The expectation of `X⁻¹` is finite, so that `X` is almost surely positive.
  have h_inv : ∫⁻ ω, (X ω)⁻¹ ∂Q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top <| by
    simpa using (withDensity_inv_mem_effectiveSet_iff hX.measurable).mp h 1 (isEVar_one hS)
  filter_upwards [ae_lt_top hX.measurable.inv h_inv] with ω hω
  simpa using hω.ne

/-- **[LRR25, Theorem 4.1].** A `Q`-almost surely finite e-variable `X` for `S` is the numeraire
of `S` under the probability measure `Q` exactly when the measure of density `X⁻¹` with respect to
`Q` belongs to the effective null. When `Q` is absolutely continuous with respect to `S`, every
e-variable is `Q`-almost surely finite (`MeasureTheory.Measure.AbsolutelyContinuousSet.ae_ne_top`).
-/
theorem isNumeraire_iff_withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) :
    IsNumeraire X S Q ↔ Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ effectiveSet S :=
  ⟨IsNumeraire.withDensity_inv_mem_effectiveSet,
    isNumeraire_of_withDensity_inv_mem_effectiveSet hS hX hX_top⟩

/-- For the numeraire `X` among the e-variables of a null of masses at most `1` under a finite
measure `Q`, `∫⁻ X⁻¹ ∂Q` is finite. -/
theorem IsNumeraire.lintegral_inv_ne_top [IsFiniteMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1)
    (hX : IsNumeraire X S Q) : ∫⁻ ω, (X ω)⁻¹ ∂Q ≠ ∞ :=
  ((hX.lintegral_inv_le_measure_fsupport hS).trans_lt (measure_lt_top _ _)).ne

/-! ### Alternatives absolutely continuous with respect to the null -/

/-- The reverse information projection is the measure of density `X⁻¹` with respect to `Q`, for
the numeraire `X` [LRR25, Theorem 4.1]. -/
theorem IsNumeraire.ripr_eq [IsFiniteMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1)
    (hX : IsNumeraire X S Q) : ripr Q S = Q.withDensity fun ω ↦ (X ω)⁻¹ := by
  refine withDensity_congr_ae ?_
  filter_upwards [(isNumeraire_numeraire Q hS).ae_unique hX] with ω hω
  rw [hω]

/-- If `Q` is absolutely continuous with respect to `S`, then `Q` is absolutely continuous with
respect to its reverse information projection on `S`, so that the two are equivalent [LRR25,
Theorem 4.1]. -/
theorem absolutelyContinuous_ripr (hS : ∀ P ∈ S, P univ ≤ 1) (hQS : Q.AbsolutelyContinuousSet S) :
    Q ≪ ripr Q S :=
  absolutelyContinuous_ripr_of_ae_ne_top (hQS.ae_ne_top (isEVar_numeraire Q hS))

/-- **Maximality of the reverse information projection** [LRR25, Theorem 4.1]. If the probability
measure `Q` is absolutely continuous with respect to `S` and `X` is the numeraire, a member of the
effective null that is absolutely continuous with respect to `Q` and setwise above
`Q.withDensity X⁻¹` is equal to it. -/
theorem IsNumeraire.eq_withDensity_inv_of_le [IsProbabilityMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1)
    (hQS : Q.AbsolutelyContinuousSet S) (hX : IsNumeraire X S Q)
    (hμ : μ ∈ effectiveSet S) (hμQ : μ ≪ Q) (hle : Q.withDensity (fun ω ↦ (X ω)⁻¹) ≤ μ) :
    μ = Q.withDensity fun ω ↦ (X ω)⁻¹ := by
  set ν := Q.withDensity fun ω ↦ (X ω)⁻¹
  have hX_meas := hX.isEVar.measurable
  have : IsFiniteMeasure μ := isFiniteMeasure_of_mem_effectiveSet hS hμ
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hle
  -- `X` has expectation `1` under `ν` and at most `1` under `μ = (μ - ν) + ν`
  have h_one : ∫⁻ ω, X ω ∂ν = 1 := by
    rw [lintegral_withDensity_inv_eq_lintegral_div hX_meas.aemeasurable hX_meas.aemeasurable,
      lintegral_div_self_eq_measure_fsupport hX_meas.aemeasurable,
      measure_fsupport_eq_measure_univ (hQS.ae_ne_top hX.isEVar) (hX.ae_ne_zero hS),
      measure_univ]
  have h_add : ∫⁻ ω, X ω ∂(μ - ν) + 1 ≤ 1 := by
    have h_le := hμ X hX.isEVar
    rwa [← Measure.sub_add_cancel_of_le hle, lintegral_add_measure, h_one] at h_le
  have h_zero : ∫⁻ ω, X ω ∂(μ - ν) = 0 := nonpos_iff_eq_zero.mp
    ((ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top h_add).trans_eq (tsub_self 1))
  -- so `X` vanishes `(μ - ν)`-almost everywhere, while it is positive `Q`-almost everywhere
  have h_ac : μ - ν ≪ Q := (Measure.absolutelyContinuous_of_le Measure.sub_le).trans hμQ
  have h_sub : μ - ν = 0 := by
    refine ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp ?_)
    filter_upwards [(lintegral_eq_zero_iff hX_meas).mp h_zero, h_ac.ae_le (hX.ae_ne_zero hS)]
      with ω h₀ h_ne using h_ne h₀
  rw [← Measure.sub_add_cancel_of_le hle, h_sub, zero_add]

/-! ### Likelihood ratios against the effective null -/

/-- For a null of measures of mass at most `1`, a likelihood ratio `Q.rnDeriv μ` against a member
`μ` of the effective null with `Q ≪ μ` is the numeraire, as soon as it is an e-variable
[LRR25, Theorem 4.1; RW, Theorem 6.15]. -/
theorem isNumeraire_of_ae_eq_rnDeriv [IsProbabilityMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1)
    (hX : IsEVar X S) (hμ : μ ∈ effectiveSet S) (hQμ : Q ≪ μ) (hXμ : X =ᵐ[Q] Q.rnDeriv μ) :
    IsNumeraire X S Q := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_mem_effectiveSet hS hμ
  have h_fsupport : Q X.fsupport = 1 := by
    rw [← measure_univ (μ := Q)]
    refine (ae_iff_measure_eq hX.measurable_fsupport.nullMeasurableSet).mp ?_
    filter_upwards [hXμ, Measure.rnDeriv_pos hQμ, hQμ.ae_le (Measure.rnDeriv_lt_top Q μ)]
      with ω hω h_pos h_lt
    exact ⟨hω ▸ h_lt.ne, hω ▸ h_pos.ne'⟩
  refine isNumeraire_of_smul_withDensity_inv_le hX hμ ?_
  rw [h_fsupport, inv_one, one_smul]
  calc Q.withDensity (fun ω ↦ (X ω)⁻¹)
  _ = Q.withDensity (μ.rnDeriv Q) :=
    withDensity_congr_ae ((hXμ.fun_comp (·⁻¹)).trans (Measure.inv_rnDeriv hQμ))
  _ ≤ μ := Measure.withDensity_rnDeriv_le μ Q

/-- **[LRR25, Theorem 4.1; RW, Theorem 6.15].** If the probability measure `Q` is absolutely
continuous with respect to a null `S` of measures of mass at most `1`, an e-variable for `S` is
the numeraire exactly when it is the likelihood ratio of `Q` against a member of the effective
null equivalent to `Q`. -/
theorem isNumeraire_iff_exists_ae_eq_rnDeriv [IsProbabilityMeasure Q]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hQS : Q.AbsolutelyContinuousSet S) (hX : IsEVar X S) :
    IsNumeraire X S Q ↔
      ∃ μ ∈ effectiveSet S, Q ≪ μ ∧ μ ≪ Q ∧ X =ᵐ[Q] Q.rnDeriv μ := by
  refine ⟨fun hXn ↦ ⟨ripr Q S, ripr_mem_effectiveSet Q hS, absolutelyContinuous_ripr hS hQS,
    withDensity_absolutelyContinuous _ _, ?_⟩,
    fun ⟨μ, hμ, hQμ, _, hXμ⟩ ↦ isNumeraire_of_ae_eq_rnDeriv hS hX hμ hQμ hXμ⟩
  exact (hXn.ae_unique (isNumeraire_numeraire Q hS)).trans
    (rnDeriv_ripr hS (hQS.ae_ne_top (isEVar_numeraire Q hS))).symm

/-- For a null `S` of measures of mass at most `1` and a member `R` of the effective null
equivalent to the probability measure `Q`, if the likelihood ratio `Q.rnDeriv R` is an e-variable,
then `R` is the reverse information projection of `Q` onto `S`. -/
theorem ripr_eq_of_isEVar_rnDeriv [IsProbabilityMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1)
    (hR : R ∈ effectiveSet S) (hQR : Q ≪ R) (hRQ : R ≪ Q) (hX : IsEVar (Q.rnDeriv R) S) :
    ripr Q S = R := by
  have := isFiniteMeasure_of_mem_effectiveSet hS hR
  rw [(isNumeraire_of_ae_eq_rnDeriv hS hX hR hQR .rfl).ripr_eq hS]
  calc Q.withDensity (fun ω ↦ (Q.rnDeriv R ω)⁻¹)
  _ = Q.withDensity (R.rnDeriv Q) := withDensity_congr_ae (Measure.inv_rnDeriv hQR)
  _ = R := Measure.withDensity_rnDeriv_eq R Q hRQ

/-- **The dominated criterion** [LRR25, Theorem 4.7]. Let `Q` and the members of a null `S` of
measures of mass at most one be absolutely continuous with respect to a σ-finite measure `μ`, with
densities `q` and `p`, and let `R` be a member of the effective null with density `r` and
`Q ≪ R`. Then `q / r` is the numeraire exactly when `∫⁻ p / r ∂Q ≤ 1` for every `P ∈ S`. -/
theorem isNumeraire_div_rnDeriv_iff [IsProbabilityMeasure Q] [SigmaFinite μ]
    (hS : ∀ P ∈ S, P univ ≤ 1) (hSμ : ∀ P ∈ S, P ≪ μ) (hQμ : Q ≪ μ)
    (hR : R ∈ effectiveSet S) (hQR : Q ≪ R) :
    IsNumeraire (fun ω ↦ Q.rnDeriv μ ω / R.rnDeriv μ ω) S Q ↔
      ∀ P ∈ S, ∫⁻ ω, P.rnDeriv μ ω / R.rnDeriv μ ω ∂Q ≤ 1 := by
  have := isFiniteMeasure_of_mem_effectiveSet hS hR
  have hRμ : R ≪ μ := absolutelyContinuous_of_mem_effectiveSet hR hSμ
  have hX_meas : Measurable fun ω ↦ Q.rnDeriv μ ω / R.rnDeriv μ ω := by fun_prop
  -- `q / r` is `Q`-almost surely the likelihood ratio `Q.rnDeriv R`.
  have h_eq : (fun ω ↦ Q.rnDeriv μ ω / R.rnDeriv μ ω) =ᵐ[Q] Q.rnDeriv R :=
    hQR.ae_le (Measure.rnDeriv_eq_div hQμ hRμ).symm
  rw [show IsNumeraire _ S Q ↔ _ from
      ⟨IsNumeraire.isEVar, fun hX ↦ isNumeraire_of_ae_eq_rnDeriv hS hX hR hQR h_eq⟩,
    isEVar_iff_lintegral_le_one, and_iff_right hX_meas]
  refine forall₂_congr fun P hP ↦ ?_
  have : IsFiniteMeasure P := ⟨(hS P hP).trans_lt ENNReal.one_lt_top⟩
  -- `∫⁻ q / r ∂P = ∫⁻ p * (q / r) ∂μ = ∫⁻ q * (p / r) ∂μ = ∫⁻ p / r ∂Q`.
  rw [← lintegral_rnDeriv_mul (hSμ P hP) hX_meas.aemeasurable,
    ← lintegral_rnDeriv_mul hQμ
      (by fun_prop : Measurable fun ω ↦ P.rnDeriv μ ω / R.rnDeriv μ ω).aemeasurable]
  simp_rw [div_eq_mul_inv, mul_left_comm (P.rnDeriv μ _)]

/-! ### Generated nulls -/

/-- For a null containing every probability measure under which each member of `𝓔₀` has
expectation at most `1`, the measure of density `X⁻¹` with respect to `Q` belongs to the null
when it has mass `1` and gives each member of `𝓔₀` expectation at most `1`. -/
private theorem withDensity_inv_mem_of_lintegral_div_le_one {𝓔₀ : Set (Ω → ℝ≥0∞)}
    (h𝓔₀ : ∀ Y ∈ 𝓔₀, Measurable Y)
    (hS : ∀ P : Measure Ω, IsProbabilityMeasure P → (∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω ∂P ≤ 1) → P ∈ S)
    (hX : Measurable X) (h_one : ∫⁻ ω, (X ω)⁻¹ ∂Q = 1)
    (h_le : ∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω / X ω ∂Q ≤ 1) :
    Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ S := by
  refine hS _ ⟨by rwa [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]⟩ fun Y hY ↦ ?_
  exact (lintegral_withDensity_inv_eq_lintegral_div hX.aemeasurable
    (h𝓔₀ Y hY).aemeasurable).trans_le (h_le Y hY)

/-- **Generated nulls** [LRR25, Corollary 4.2]. Let `S` contain every probability measure under
which each member of a family `𝓔₀` has expectation at most `1`. A `Q`-almost surely finite
e-variable `X` for `S` with `∫⁻ X⁻¹ ∂Q = 1` and `∫⁻ Y / X ∂Q ≤ 1` for every `Y ∈ 𝓔₀` is the
numeraire of `S` under the probability measure `Q`. The finiteness holds when `Q` is absolutely
continuous with respect to `S` (`MeasureTheory.Measure.AbsolutelyContinuousSet.ae_ne_top`). -/
theorem isNumeraire_of_lintegral_div_le_one [IsProbabilityMeasure Q] {𝓔₀ : Set (Ω → ℝ≥0∞)}
    (h𝓔₀ : ∀ Y ∈ 𝓔₀, Measurable Y)
    (hS : ∀ P : Measure Ω, IsProbabilityMeasure P → (∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω ∂P ≤ 1) → P ∈ S)
    (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞)
    (h_one : ∫⁻ ω, (X ω)⁻¹ ∂Q = 1) (h_le : ∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω / X ω ∂Q ≤ 1) :
    IsNumeraire X S Q := by
  have hmem := withDensity_inv_mem_of_lintegral_div_le_one h𝓔₀ hS hX.measurable h_one h_le
  -- `∫⁻ X⁻¹ ∂Q = 1` is finite, so that `X` is almost surely positive.
  have hX_zero : ∀ᵐ ω ∂Q, X ω ≠ 0 := by
    filter_upwards [ae_lt_top hX.measurable.inv (by simp [h_one])] with ω hω
    simpa using hω.ne
  exact isNumeraire_of_ae_ne_zero_of_withDensity_inv_mem_effectiveSet hX hX_top hX_zero
    fun Y hY ↦ hY.lintegral_le_one hmem

/-- **Generated nulls** [LRR25, Corollary 4.2]. Under the hypotheses of
`isNumeraire_of_lintegral_div_le_one`, and if the members of `S` have mass at most `1`, the
reverse information projection of `Q` on `S` belongs to `S`. -/
theorem ripr_mem_of_lintegral_div_le_one [IsProbabilityMeasure Q] {𝓔₀ : Set (Ω → ℝ≥0∞)}
    (h𝓔₀ : ∀ Y ∈ 𝓔₀, Measurable Y)
    (hS : ∀ P : Measure Ω, IsProbabilityMeasure P → (∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω ∂P ≤ 1) → P ∈ S)
    (hS_le : ∀ P ∈ S, P univ ≤ 1) (hX : IsEVar X S) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞)
    (h_one : ∫⁻ ω, (X ω)⁻¹ ∂Q = 1) (h_le : ∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω / X ω ∂Q ≤ 1) :
    ripr Q S ∈ S := by
  rw [(isNumeraire_of_lintegral_div_le_one h𝓔₀ hS hX hX_top h_one h_le).ripr_eq hS_le]
  exact withDensity_inv_mem_of_lintegral_div_le_one h𝓔₀ hS hX.measurable h_one h_le

/-! ### Simple nulls: likelihood ratios -/

/-- **The numeraire of a simple null** [LRR25, Corollary 3.15]. Let `N` be a measurable `P`-null
set off which the finite measure `Q` is absolutely continuous with respect to the probability
measure `P`, for example a `P`-null set carrying the singular part of `Q` in its Lebesgue
decomposition with respect to `P`. The numeraire of `{P}` under `Q` is `∞` on `N`, and the
likelihood ratio of `Q[|Nᶜ]` to `P` on `Nᶜ`. -/
theorem isNumeraire_piecewise_rnDeriv_cond [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    {N : Set Ω} [DecidablePred (· ∈ N)] (hN : MeasurableSet N) (hPN : P N = 0)
    (hQN : Q.restrict Nᶜ ≪ P) :
    IsNumeraire (N.piecewise (fun _ ↦ ∞) ((Q[|Nᶜ]).rnDeriv P)) {P} Q := by
  set ν := Q[|Nᶜ] with hν
  set X := N.piecewise (fun _ ↦ ∞) (ν.rnDeriv P)
  have hX_meas : Measurable X := measurable_const.piecewise hN (Measure.measurable_rnDeriv _ _)
  have h_restrict : Q.restrict Nᶜ = Q Nᶜ • ν := by
    ext t ht
    rw [smul_apply, smul_eq_mul, hν, mul_comm, cond_mul_eq_inter' hN.compl (measure_ne_top _ _),
      Measure.restrict_apply ht, inter_comm]
  have hQν : Q.restrict Nᶜ ≪ ν := by
    rw [h_restrict]
    exact Measure.smul_absolutelyContinuous
  have hνP : ν ≪ P := Measure.smul_absolutelyContinuous.trans hQN
  have hX_ae : X =ᵐ[P] ν.rnDeriv P := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hPN] with ω hω
    simp [X, hω]
  have hX : IsEVar X {P} := ⟨hX_meas, fun μ hμ ↦ by
    obtain rfl : μ = P := hμ
    rw [lintegral_congr_ae hX_ae]
    exact Measure.lintegral_rnDeriv_le.trans prob_le_one⟩
  -- the set where `X` is positive and finite carries all the mass of `Q` off `N`
  have h_fsupport : Q Nᶜ ≤ Q X.fsupport := by
    refine measure_mono_ae ((ae_restrict_iff' hN.compl).mp ?_)
    filter_upwards [ae_restrict_mem hN.compl, hQN.ae_le (Measure.rnDeriv_lt_top ν P),
      hQν.ae_le (Measure.rnDeriv_pos hνP)] with ω hωN h_lt h_pos
    have hX_eq : X ω = ν.rnDeriv P ω := Set.piecewise_eq_of_notMem _ _ _ hωN
    exact ⟨by simpa [hX_eq] using h_lt.ne, by simpa [hX_eq] using h_pos.ne'⟩
  refine isNumeraire_of_smul_withDensity_inv_le hX
    (subset_effectiveSet (mem_singleton P)) fun s ↦ ?_
  -- the measure of density `X⁻¹` is `Q Nᶜ` times that of density `(ν.rnDeriv P)⁻¹` under `ν`
  have h_inv : (fun ω ↦ (X ω)⁻¹) = Nᶜ.indicator fun ω ↦ (ν.rnDeriv P ω)⁻¹ := by
    ext ω
    by_cases hω : ω ∈ N <;> simp [X, hω]
  have h_le : ν.withDensity (fun ω ↦ (ν.rnDeriv P ω)⁻¹) ≤ P :=
    (withDensity_congr_ae (Measure.inv_rnDeriv hνP)).trans_le (Measure.withDensity_rnDeriv_le P ν)
  rw [h_inv, withDensity_indicator hN.compl, h_restrict, withDensity_smul_measure,
    smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc]
  calc (Q X.fsupport)⁻¹ * Q Nᶜ * ν.withDensity (fun ω ↦ (ν.rnDeriv P ω)⁻¹) s
  _ ≤ 1 * P s := by
    gcongr
    calc (Q X.fsupport)⁻¹ * Q Nᶜ ≤ (Q X.fsupport)⁻¹ * Q X.fsupport := by gcongr
    _ ≤ 1 := by rw [mul_comm]; exact ENNReal.mul_inv_le_one _
  _ = P s := one_mul _

/-- The integral under `P`, on a set `A`, of the numeraire of the simple null `{P}` against `Q` of
`isNumeraire_piecewise_rnDeriv_cond` is the mass that `Q` gives to `A` off the `P`-null set `N`,
divided by the mass of `Nᶜ`. -/
theorem setLIntegral_piecewise_rnDeriv_cond [SigmaFinite P] {N : Set Ω} [DecidablePred (· ∈ N)]
    (hN : MeasurableSet N) (hPN : P N = 0) (hQN : Q.restrict Nᶜ ≪ P) (A : Set Ω) :
    ∫⁻ ω in A, N.piecewise (fun _ ↦ ∞) ((Q[|Nᶜ]).rnDeriv P) ω ∂P = (Q Nᶜ)⁻¹ * Q (A \ N) := by
  have hνP : Q[|Nᶜ] ≪ P := Measure.smul_absolutelyContinuous.trans hQN
  have h_ae : N.piecewise (fun _ ↦ ∞) ((Q[|Nᶜ]).rnDeriv P) =ᵐ[P] (Q[|Nᶜ]).rnDeriv P := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPN] with ω hω
    exact piecewise_eq_of_notMem _ _ _ hω
  rw [lintegral_congr_ae (ae_restrict_of_ae h_ae), Measure.setLIntegral_rnDeriv hνP A,
    cond_apply hN.compl Q A, inter_comm, sdiff_eq]

/-- A numeraire `X` of a simple null `{P}`, with `P` of mass at most one, against `Q`, that is
infinite on a measurable set `N` off which `Q` is absolutely continuous with respect to `P`, is
positive and finite exactly off `N`, `Q`-almost surely. -/
theorem IsNumeraire.ae_mem_fsupport_iff_notMem (hX : IsNumeraire X {P} Q) (hP : P univ ≤ 1)
    {N : Set Ω} (hN : MeasurableSet N) (hQN : Q.restrict Nᶜ ≪ P) (hXN : ∀ ω ∈ N, X ω = ∞) :
    ∀ᵐ ω ∂Q, ω ∈ X.fsupport ↔ ω ∉ N := by
  have h_top : ∀ᵐ ω ∂Q, ω ∈ Nᶜ → X ω ≠ ∞ :=
    (ae_restrict_iff' hN.compl).1 (hQN.ae_le (hX.isEVar.ae_ne_top (mem_singleton P)))
  filter_upwards [h_top, hX.ae_ne_zero fun μ hμ ↦ (mem_singleton_iff.1 hμ) ▸ hP]
    with ω hω_top hω_zero
  rw [Function.mem_fsupport]
  exact ⟨fun h hωN ↦ h.1 (hXN ω hωN), fun hωN ↦ ⟨hω_top hωN, hω_zero⟩⟩

/-- **Likelihood ratios are numeraires** [RW, Theorem 3.20]. For probability measures `Q ≪ P`,
the likelihood ratio `Q.rnDeriv P` is the numeraire of the simple null `{P}` under `Q`. By
Statlib's `maxUtility_singleton_eq_klDiv`, its expected logarithm under `Q` is `klDiv Q P`. -/
theorem isNumeraire_rnDeriv [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hQP : Q ≪ P) :
    IsNumeraire (Q.rnDeriv P) {P} Q := by
  classical
  simpa using isNumeraire_piecewise_rnDeriv_cond (Q := Q) MeasurableSet.empty measure_empty
    (by simpa using hQP)

/-- For equivalent probability measures `Q` and `P`, the reverse information projection of `Q`
onto the simple null `{P}` is `P`. -/
theorem ripr_singleton_eq [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hQP : Q ≪ P)
    (hPQ : P ≪ Q) : ripr Q {P} = P :=
  ripr_eq_of_isEVar_rnDeriv (by simp) (subset_effectiveSet (mem_singleton P)) hQP hPQ
    (isNumeraire_rnDeriv hQP).isEVar

/-! ### Which e-variables are numeraires -/

/-- An e-variable `X` whose expectation under a measure `μ` is finite and at least that of every
e-variable is a numeraire against `μ.withDensity X`. -/
theorem isNumeraire_withDensity (hX : IsEVar X S) (hXμ : ∫⁻ ω, X ω ∂μ ≠ ∞)
    (h : ∀ Y, IsEVar Y S → ∫⁻ ω, Y ω ∂μ ≤ ∫⁻ ω, X ω ∂μ) :
    IsNumeraire X S (μ.withDensity X) := by
  have hX_meas := hX.measurable
  -- under `μ.withDensity X`, the finite support of `X` has mass `∫⁻ X ∂μ`
  have h_fsupp : (μ.withDensity X) X.fsupport = ∫⁻ ω, X ω ∂μ := by
    rw [withDensity_apply _ hX.measurable_fsupport, ← lintegral_indicator hX.measurable_fsupport]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_lt_top hX_meas hXμ] with ω hω
    by_cases hω0 : X ω = 0
    · by_cases hωs : ω ∈ X.fsupport <;> simp [hωs, hω0]
    · exact indicator_of_mem (a := ω) (s := X.fsupport) ⟨hω.ne, hω0⟩ X
  refine isNumeraire_of_lintegral_div_le hX (by rw [h_fsupp]; exact hXμ) fun Y hY ↦ ?_
  have h_eq : ∫⁻ ω, Y ω / X ω ∂μ.withDensity X = ∫⁻ ω, X ω * (Y ω / X ω) ∂μ :=
    lintegral_withDensity_eq_lintegral_mul _ hX_meas (hY.measurable.div hX_meas)
  rw [h_fsupp, h_eq]
  exact (lintegral_mono fun ω ↦ ENNReal.mul_div_le).trans (h Y hY)

/-- **An e-variable exact under a member of the effective null is a numeraire** [EVR26, Note 42,
Theorem 7]. If `μ` is in the effective null of `S` and the e-variable `X` has `∫⁻ X ∂μ = 1`, then
`X` is a numeraire of `S` against `μ.withDensity X`, a measure of mass `∫⁻ X ∂μ = 1`. -/
theorem isNumeraire_withDensity_of_mem_effectiveSet (hX : IsEVar X S) (hμ : μ ∈ effectiveSet S)
    (hXμ : ∫⁻ ω, X ω ∂μ = 1) : IsNumeraire X S (μ.withDensity X) :=
  isNumeraire_withDensity hX (by simp [hXμ]) fun Y hY ↦ hXμ ▸ hμ Y hY

/-- **A numeraire is exact under the reverse information projection** [EVR26, Note 42,
Theorem 7]. If the members of `S` have mass at most one and `X` is a numeraire of `S` against a
probability measure `Q`, with `X` finite `Q`-almost surely, then `X` has expectation `1` under the
reverse information projection `ripr Q S`, which is in the effective null of `S`
(`ripr_mem_effectiveSet`). -/
theorem IsNumeraire.lintegral_ripr_eq_one [IsProbabilityMeasure Q] (hS : ∀ P ∈ S, P univ ≤ 1)
    (hX : IsNumeraire X S Q) (hX_top : ∀ᵐ ω ∂Q, X ω ≠ ∞) : ∫⁻ ω, X ω ∂ripr Q S = 1 := by
  have hX_meas : AEMeasurable X Q := hX.measurable.aemeasurable
  rw [hX.ripr_eq hS, lintegral_withDensity_inv_eq_lintegral_div hX_meas hX_meas,
    lintegral_div_self_eq_measure_fsupport hX_meas,
    measure_fsupport_eq_measure_univ hX_top (hX.ae_ne_zero hS), measure_univ]

/-- **Which e-variables are numeraires against an alternative under which they are finite**
[EVR26, Note 42, Theorem 7]. For a null of measures of mass at most one, an e-variable `X` is a
numeraire of `S` against some probability measure under which it is almost surely finite exactly
when some member `μ` of the effective null of `S` has `∫⁻ X ∂μ = 1`. -/
theorem exists_isNumeraire_ae_ne_top_iff (hS : ∀ P ∈ S, P univ ≤ 1) (hX : IsEVar X S) :
    (∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ IsNumeraire X S Q ∧ ∀ᵐ ω ∂Q, X ω ≠ ∞) ↔
      ∃ μ ∈ effectiveSet S, ∫⁻ ω, X ω ∂μ = 1 := by
  refine ⟨fun ⟨Q, _, hXQ, hX_top⟩ ↦ ⟨ripr Q S, ripr_mem_effectiveSet Q hS,
    hXQ.lintegral_ripr_eq_one hS hX_top⟩, fun ⟨μ, hμ, hXμ⟩ ↦ ⟨μ.withDensity X, ?_,
    isNumeraire_withDensity_of_mem_effectiveSet hX hμ hXμ, ?_⟩⟩
  · exact ⟨by rw [withDensity_apply _ .univ, Measure.restrict_univ, hXμ]⟩
  · rw [ae_withDensity_iff hX.measurable]
    filter_upwards [ae_lt_top hX.measurable (by simp [hXμ])] with ω hω _ using hω.ne

/-- **Which e-variables are numeraires** [EVR26, Note 42, Theorem 7]. For a null of measures of
mass at most one, an e-variable `X` is a numeraire of `S` against some probability measure exactly
when it is exact under a member of the effective null, `∫⁻ X ∂μ = 1`, or infinite at some point.
At a point `ω` where `X ω = ∞`, `X` is a numeraire against the Dirac mass at `ω`. -/
theorem exists_isNumeraire_iff (hS : ∀ P ∈ S, P univ ≤ 1) (hX : IsEVar X S) :
    (∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ IsNumeraire X S Q) ↔
      (∃ μ ∈ effectiveSet S, ∫⁻ ω, X ω ∂μ = 1) ∨ ∃ ω, X ω = ∞ := by
  rw [← exists_isNumeraire_ae_ne_top_iff hS hX]
  refine ⟨fun ⟨Q, hQ, hXQ⟩ ↦ ?_, ?_⟩
  · by_cases h_top : ∀ᵐ ω ∂Q, X ω ≠ ∞
    · exact .inl ⟨Q, hQ, hXQ, h_top⟩
    · by_contra h
      push Not at h
      exact h_top (.of_forall h.2)
  rintro (⟨Q, hQ, hXQ, -⟩ | ⟨ω, hω⟩)
  · exact ⟨Q, hQ, hXQ⟩
  · refine ⟨Measure.dirac ω, inferInstance,
      isNumeraire_of_lintegral_div_le hX (measure_ne_top _ _) fun Y hY ↦ ?_⟩
    have hYX : Measurable fun ω ↦ Y ω / X ω := hY.measurable.div hX.measurable
    rw [lintegral_dirac' ω hYX, hω, ENNReal.div_top]
    exact zero_le

/-- **An e-variable is a numeraire against its tilt of a mixture of members under which it is
exact** [EVR26, Note 42, Theorem 9 (2)]. If `μ` is a convex combination of members `P` of the null
with `∫⁻ X ∂P = 1`, then the e-variable `X` is a numeraire of `S` against `μ.withDensity X`. The
null is arbitrary. -/
theorem isNumeraire_withDensity_of_mem_convexHull (hX : IsEVar X S)
    (hμ : μ ∈ convexHull ℝ≥0∞ {P | P ∈ S ∧ ∫⁻ ω, X ω ∂P = 1}) :
    IsNumeraire X S (μ.withDensity X) := by
  -- the measures under which `X` has a finite integral, at least that of every e-variable
  have h_conv : Convex ℝ≥0∞ {μ : Measure Ω | ∫⁻ ω, X ω ∂μ ≠ ∞ ∧
      ∀ Y, IsEVar Y S → ∫⁻ ω, Y ω ∂μ ≤ ∫⁻ ω, X ω ∂μ} := by
    intro μ hμ ν hν a b _ _ hab
    have ha : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
    have hb : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
    simp only [mem_ofPred_eq, lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]
    exact ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ha hμ.1, ENNReal.mul_ne_top hb hν.1⟩,
      fun Y hY ↦ add_le_add (mul_le_mul_right (hμ.2 Y hY) a) (mul_le_mul_right (hν.2 Y hY) b)⟩
  have h_sub : {P | P ∈ S ∧ ∫⁻ ω, X ω ∂P = 1} ⊆
      {μ : Measure Ω | ∫⁻ ω, X ω ∂μ ≠ ∞ ∧ ∀ Y, IsEVar Y S → ∫⁻ ω, Y ω ∂μ ≤ ∫⁻ ω, X ω ∂μ} :=
    fun P ⟨hP, hPX⟩ ↦ ⟨by simp [hPX], fun Y hY ↦ (hY.lintegral_le_one hP).trans_eq hPX.symm⟩
  have h := convexHull_min h_sub h_conv hμ
  exact isNumeraire_withDensity hX h.1 h.2

/-! ### Positivity of numeraires -/

/-- **A numeraire is almost surely positive when a positive constant is an e-variable.** If `X`
is a numeraire of `S` against `Q`, with `Q {0 < X < ∞} < ∞`, and some constant `c ≠ 0` is an
e-variable for `S`, then `X` is `Q`-almost surely positive. Statlib's `IsNumeraire.ae_ne_zero` is
the case `c = 1`, for a null of measures of mass at most one. -/
theorem IsNumeraire.ae_ne_zero_of_isEVar_const (hX : IsNumeraire X S Q) (hQ : Q X.fsupport ≠ ∞)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hcS : IsEVar (fun _ ↦ c) S) : ∀ᵐ ω ∂Q, X ω ≠ 0 := by
  have h : ∫⁻ ω, c / X ω ∂Q ≠ ∞ :=
    ne_top_of_le_ne_top hQ (hX.lintegral_div_le_measure_fsupport hcS)
  filter_upwards [ae_lt_top (f := fun ω ↦ c / X ω) (measurable_const.div hX.measurable) h]
    with ω hω hω0
  rw [hω0, ENNReal.div_zero hc] at hω
  exact lt_irrefl _ hω

/-! ### Uniqueness on a countable space -/

/-- On a countable space where `Q` charges every point, two numeraires of the same null under `Q`
are equal everywhere, not only `Q`-almost surely. -/
theorem IsNumeraire.eq_of_countable [Countable Ω] {Y : Ω → ℝ≥0∞} (hX : IsNumeraire X S Q)
    (hY : IsNumeraire Y S Q) (hQ : ∀ ω, Q {ω} ≠ 0) : X = Y :=
  funext fun ω ↦ ae_iff_of_countable.1 (hX.ae_unique hY) ω (hQ ω)

end ProbabilityTheory
