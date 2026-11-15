/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.RIPr
public import LMLExplore.EValues.EffectiveSet
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

Several statements assume that every measurable set charged by `Q` is charged by some member of
`S`, the absolute continuity `Q ≪ S` of [LRR25]. Under it every e-variable is `Q`-almost surely
finite, and the numeraire is the only e-variable that is a likelihood ratio of `Q` against an
equivalent member of the effective null.

## Main statements

* `ProbabilityTheory.isNumeraire_iff_smul_withDensity_inv_mem_effectiveSet`: for any finite `Q`
  and any null, an e-variable `X` is the numeraire exactly when `Q.withDensity X⁻¹`, divided by
  the mass under `Q` of the set where `X` is positive and finite, is in the effective null.
* `ProbabilityTheory.isNumeraire_iff_withDensity_inv_mem_effectiveSet`: for `Q ≪ S` and a
  `Q`-almost surely positive e-variable `X`, `X` is the numeraire exactly when
  `Q.withDensity X⁻¹` is in the effective null [LRR25, Theorem 4.1].
* `ProbabilityTheory.IsNumeraire.ripr_eq`, `ProbabilityTheory.absolutelyContinuous_ripr`,
  `ProbabilityTheory.IsNumeraire.eq_withDensity_inv_of_le`: that measure is then the reverse
  information projection, it is equivalent to `Q`, and it is maximal among the members of the
  effective null absolutely continuous with respect to `Q` [LRR25, Theorem 4.1].
* `ProbabilityTheory.isNumeraire_iff_exists_ae_eq_rnDeriv`: for `Q ≪ S`, the numeraire is the
  only e-variable that is a likelihood ratio `Q.rnDeriv μ` against a member `μ` of the effective
  null equivalent to `Q` [LRR25, Theorem 4.1; RW, Theorem 6.15].
* `ProbabilityTheory.isNumeraire_of_lintegral_div_le_one`,
  `ProbabilityTheory.ripr_mem_of_lintegral_div_le_one`: for `Q ≪ S` and a null `S` containing
  every probability measure under which each member of a family `𝓔₀` has expectation at most
  `1`, a `Q`-almost surely positive e-variable `X` with `∫⁻ X⁻¹ ∂Q = 1` and `∫⁻ Y / X ∂Q ≤ 1` for
  every `Y ∈ 𝓔₀` is the numeraire, and the reverse information projection then belongs to `S`
  [LRR25, Corollary 4.2].
* `ProbabilityTheory.isNumeraire_piecewise_rnDeriv_cond`: the numeraire of a simple null `{P}`
  with no absolute continuity: `∞` on a `P`-null set `N` off which `Q` is absolutely continuous
  with respect to `P`, and the likelihood ratio of `Q[|Nᶜ]` to `P` on `Nᶜ` [LRR25,
  Corollary 3.15].
* `ProbabilityTheory.isNumeraire_rnDeriv`: for `Q ≪ P`, the likelihood ratio `Q.rnDeriv P` is the
  numeraire of `{P}` [RW, Theorem 3.20]; its expected logarithm is `klDiv Q P` by Statlib's
  `maxUtility_singleton_eq_klDiv`.

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Lemma 3.3, Theorem 3.13,
  Corollary 3.15, Theorem 4.1 and Corollary 4.2.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Theorems 3.20 and 6.15.
-/

public section

open MeasureTheory Set

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Set (Measure Ω)} {Q P μ : Measure Ω}
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

/-! ### Alternatives absolutely continuous with respect to the null -/

/-- If every measurable set charged by `Q` is charged by some member of `S`, every e-variable for
`S` is `Q`-almost surely finite. -/
theorem IsEVar.ae_ne_top_of_forall_measure_eq_zero (hX : IsEVar X S)
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) : ∀ᵐ ω ∂Q, X ω ≠ ∞ := by
  refine ae_iff.mpr (hQS _ ?_ fun P hP ↦ ae_iff.mp (hX.ae_ne_top hP))
  simp only [ne_eq, not_not]
  exact measurableSet_eq_fun hX.measurable measurable_const

/-- If every measurable set charged by `Q` is charged by some member of `S`, the finite support of
a `Q`-almost surely positive e-variable for `S` has full measure under `Q`. -/
theorem IsEVar.measure_fsupport_eq_measure_univ [IsFiniteMeasure Q] (hX : IsEVar X S)
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) (hX₀ : ∀ᵐ ω ∂Q, X ω ≠ 0) :
    Q X.fsupport = Q univ := by
  refine (ae_iff_measure_eq hX.measurable_fsupport.nullMeasurableSet).mp ?_
  filter_upwards [hX.ae_ne_top_of_forall_measure_eq_zero hQS, hX₀] with ω h_top h_zero
  exact ⟨h_top, h_zero⟩

/-- **[LRR25, Theorem 4.1].** If every measurable set charged by the probability measure `Q` is
charged by some member of `S`, a `Q`-almost surely positive e-variable `X` for `S` is the
numeraire of `S` under `Q` exactly when the measure of density `X⁻¹` with respect to `Q` belongs
to the effective null. -/
theorem isNumeraire_iff_withDensity_inv_mem_effectiveSet [IsProbabilityMeasure Q]
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) (hX : IsEVar X S)
    (hX₀ : ∀ᵐ ω ∂Q, X ω ≠ 0) :
    IsNumeraire X S Q ↔ Q.withDensity (fun ω ↦ (X ω)⁻¹) ∈ effectiveSet S := by
  rw [isNumeraire_iff_smul_withDensity_inv_mem_effectiveSet,
    hX.measure_fsupport_eq_measure_univ hQS hX₀, measure_univ, inv_one, one_smul,
    and_iff_right hX]

/-- The reverse information projection is the measure of density `X⁻¹` with respect to `Q`, for
the numeraire `X` [LRR25, Theorem 4.1]. -/
theorem IsNumeraire.ripr_eq [IsFiniteMeasure Q] (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hX : IsNumeraire X S Q) : ripr Q S = Q.withDensity fun ω ↦ (X ω)⁻¹ := by
  refine withDensity_congr_ae ?_
  filter_upwards [(isNumeraire_numeraire Q hS).ae_unique hX] with ω hω
  rw [hω]

/-- If every measurable set charged by `Q` is charged by some member of `S`, then `Q` is
absolutely continuous with respect to its reverse information projection on `S`, so that the two
are equivalent [LRR25, Theorem 4.1]. -/
theorem absolutelyContinuous_ripr
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) : Q ≪ ripr Q S :=
  absolutelyContinuous_ripr_of_ae_ne_top
    ((isEVar_numeraire Q S).ae_ne_top_of_forall_measure_eq_zero hQS)

/-- **Maximality of the reverse information projection** [LRR25, Theorem 4.1]. If every measurable
set charged by the probability measure `Q` is charged by some member of `S` and `X` is the
numeraire, a member of the effective null that is absolutely continuous with respect to `Q` and
setwise above `Q.withDensity X⁻¹` is equal to it. -/
theorem IsNumeraire.eq_withDensity_inv_of_le [IsProbabilityMeasure Q]
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) (hX : IsNumeraire X S Q)
    (hμ : μ ∈ effectiveSet S) (hμQ : μ ≪ Q) (hle : Q.withDensity (fun ω ↦ (X ω)⁻¹) ≤ μ) :
    μ = Q.withDensity fun ω ↦ (X ω)⁻¹ := by
  set ν := Q.withDensity fun ω ↦ (X ω)⁻¹
  have hX_meas := hX.isEVar.measurable
  have : IsFiniteMeasure μ := isFiniteMeasure_of_mem_effectiveSet hμ
  have : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hle
  -- `X` has expectation `1` under `ν` and at most `1` under `μ = (μ - ν) + ν`
  have h_one : ∫⁻ ω, X ω ∂ν = 1 := by
    rw [lintegral_withDensity_inv_eq_lintegral_div hX_meas.aemeasurable hX_meas.aemeasurable,
      lintegral_div_self_eq_measure_fsupport hX_meas.aemeasurable,
      hX.isEVar.measure_fsupport_eq_measure_univ hQS hX.ae_ne_zero, measure_univ]
  have h_add : ∫⁻ ω, X ω ∂(μ - ν) + 1 ≤ 1 := by
    have h_le := hμ X hX.isEVar
    rwa [← Measure.sub_add_cancel_of_le hle, lintegral_add_measure, h_one] at h_le
  have h_zero : ∫⁻ ω, X ω ∂(μ - ν) = 0 := nonpos_iff_eq_zero.mp
    ((ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top h_add).trans_eq (tsub_self 1))
  -- so `X` vanishes `(μ - ν)`-almost everywhere, while it is positive `Q`-almost everywhere
  have h_ac : μ - ν ≪ Q := (Measure.absolutelyContinuous_of_le Measure.sub_le).trans hμQ
  have h_sub : μ - ν = 0 := by
    refine ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp ?_)
    filter_upwards [(lintegral_eq_zero_iff hX_meas).mp h_zero, h_ac.ae_le hX.ae_ne_zero]
      with ω h₀ h_ne using h_ne h₀
  rw [← Measure.sub_add_cancel_of_le hle, h_sub, zero_add]

/-- A likelihood ratio `Q.rnDeriv μ` against a member `μ` of the effective null with `Q ≪ μ` is
the numeraire, as soon as it is an e-variable [LRR25, Theorem 4.1; RW, Theorem 6.15]. -/
theorem isNumeraire_of_ae_eq_rnDeriv [IsProbabilityMeasure Q] (hX : IsEVar X S)
    (hμ : μ ∈ effectiveSet S) (hQμ : Q ≪ μ) (hXμ : X =ᵐ[Q] Q.rnDeriv μ) :
    IsNumeraire X S Q := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_mem_effectiveSet hμ
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

/-- **[LRR25, Theorem 4.1; RW, Theorem 6.15].** If every measurable set charged by the probability
measure `Q` is charged by some member of a null `S` of finite measures, an e-variable for `S` is
the numeraire exactly when it is the likelihood ratio of `Q` against a member of the effective
null equivalent to `Q`. -/
theorem isNumeraire_iff_exists_ae_eq_rnDeriv [IsProbabilityMeasure Q]
    (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) (hX : IsEVar X S) :
    IsNumeraire X S Q ↔
      ∃ μ ∈ effectiveSet S, Q ≪ μ ∧ μ ≪ Q ∧ X =ᵐ[Q] Q.rnDeriv μ := by
  refine ⟨fun hXn ↦ ⟨ripr Q S, ripr_mem_effectiveSet Q hS, absolutelyContinuous_ripr hQS,
    withDensity_absolutelyContinuous _ _, ?_⟩,
    fun ⟨μ, hμ, hQμ, _, hXμ⟩ ↦ isNumeraire_of_ae_eq_rnDeriv hX hμ hQμ hXμ⟩
  exact (hXn.ae_unique (isNumeraire_numeraire Q hS)).trans
    (rnDeriv_ripr hS ((isEVar_numeraire Q S).ae_ne_top_of_forall_measure_eq_zero hQS)).symm

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
which each member of a family `𝓔₀` has expectation at most `1`, and let every measurable set
charged by the probability measure `Q` be charged by some member of `S`. An e-variable `X` for
`S` with `∫⁻ X⁻¹ ∂Q = 1` and `∫⁻ Y / X ∂Q ≤ 1` for every `Y ∈ 𝓔₀` is the numeraire of `S`
under `Q`; the first condition forces `X` to be `Q`-almost surely positive. -/
theorem isNumeraire_of_lintegral_div_le_one [IsProbabilityMeasure Q] {𝓔₀ : Set (Ω → ℝ≥0∞)}
    (h𝓔₀ : ∀ Y ∈ 𝓔₀, Measurable Y)
    (hS : ∀ P : Measure Ω, IsProbabilityMeasure P → (∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω ∂P ≤ 1) → P ∈ S)
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) (hX : IsEVar X S)
    (h_one : ∫⁻ ω, (X ω)⁻¹ ∂Q = 1) (h_le : ∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω / X ω ∂Q ≤ 1) :
    IsNumeraire X S Q := by
  have hX₀ : ∀ᵐ ω ∂Q, X ω ≠ 0 :=
    (ae_lt_top hX.measurable.inv (h_one ▸ ENNReal.one_ne_top)).mono
      fun ω h ↦ (ENNReal.inv_lt_top.mp h).ne'
  have hmem := withDensity_inv_mem_of_lintegral_div_le_one h𝓔₀ hS hX.measurable h_one h_le
  refine (isNumeraire_iff_withDensity_inv_mem_effectiveSet hQS hX hX₀).mpr fun Y hY ↦ ?_
  refine (hY.lintegral_le_measure_univ _ hmem).trans_eq ?_
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, h_one]

/-- **Generated nulls** [LRR25, Corollary 4.2]. Under the hypotheses of
`isNumeraire_of_lintegral_div_le_one`, and if `S` consists of finite measures, the reverse
information projection of `Q` on `S` belongs to `S`. -/
theorem ripr_mem_of_lintegral_div_le_one [IsProbabilityMeasure Q] {𝓔₀ : Set (Ω → ℝ≥0∞)}
    (h𝓔₀ : ∀ Y ∈ 𝓔₀, Measurable Y)
    (hS : ∀ P : Measure Ω, IsProbabilityMeasure P → (∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω ∂P ≤ 1) → P ∈ S)
    (hS_fin : ∀ P ∈ S, IsFiniteMeasure P)
    (hQS : ∀ s, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0) (hX : IsEVar X S)
    (h_one : ∫⁻ ω, (X ω)⁻¹ ∂Q = 1) (h_le : ∀ Y ∈ 𝓔₀, ∫⁻ ω, Y ω / X ω ∂Q ≤ 1) :
    ripr Q S ∈ S := by
  rw [(isNumeraire_of_lintegral_div_le_one h𝓔₀ hS hQS hX h_one h_le).ripr_eq hS_fin]
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
  have hX : IsEVar X {P} := .of_lintegral_le_one (by simpa) hX_meas fun μ hμ ↦ by
    obtain rfl : μ = P := hμ
    rw [lintegral_congr_ae hX_ae]
    exact Measure.lintegral_rnDeriv_le.trans prob_le_one
  -- the set where `X` is positive and finite carries all the mass of `Q` off `N`
  have h_fsupport : Q Nᶜ ≤ Q X.fsupport := by
    refine measure_mono_ae ((ae_restrict_iff' hN.compl).mp ?_)
    filter_upwards [ae_restrict_mem hN.compl, hQN.ae_le (Measure.rnDeriv_lt_top ν P),
      hQν.ae_le (Measure.rnDeriv_pos hνP)] with ω hωN h_lt h_pos
    have hX_eq : X ω = ν.rnDeriv P ω := Set.piecewise_eq_of_notMem _ _ _ hωN
    exact ⟨by simpa [hX_eq] using h_lt.ne, by simpa [hX_eq] using h_pos.ne'⟩
  refine isNumeraire_of_smul_withDensity_inv_le hX
    (subset_effectiveSet (by simp) (mem_singleton P)) fun s ↦ ?_
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

/-- **Likelihood ratios are numeraires** [RW, Theorem 3.20]. For probability measures `Q ≪ P`,
the likelihood ratio `Q.rnDeriv P` is the numeraire of the simple null `{P}` under `Q`. By
Statlib's `maxUtility_singleton_eq_klDiv`, its expected logarithm under `Q` is `klDiv Q P`. -/
theorem isNumeraire_rnDeriv [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hQP : Q ≪ P) :
    IsNumeraire (Q.rnDeriv P) {P} Q := by
  classical
  simpa using isNumeraire_piecewise_rnDeriv_cond (Q := Q) MeasurableSet.empty measure_empty
    (by simpa using hQP)

end ProbabilityTheory
