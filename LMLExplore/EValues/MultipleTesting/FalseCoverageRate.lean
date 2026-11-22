/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Confidence.Set
public import LMLExplore.EValues.MultipleTesting.EClosure
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Add

/-!
# The false coverage rate of the e-BY procedure

For finitely many parameters `i : ι`, `K = Fintype.card ι`, each with its own type `Θ i` and its
own nulls `S i`, a scientist selects after seeing the data, by any rule, a set `R` of parameters
and reports a confidence set for each of them. The false coverage proportion
(`ProbabilityTheory.fcp`) is the proportion of the reported sets that miss the true parameters `θ`,
and its expectation is the false coverage rate. The e-BY procedure at level `δ`
(`ProbabilityTheory.eBY`) of [XWR24] reports for `i ∈ R` the confidence set of level
`δ * #R / K` [RW, Definition 13.6]. For level-free e-confidence sets
(`ProbabilityTheory.IsLevelFreeEConfSet`) it controls the false coverage rate at `δ`, under
arbitrary dependence and for every selection rule, and even post hoc: the expected largest ratio of
the false coverage proportion to `δ`, over all selections and all levels, is at most one
[RW, Theorem 13.7]. Under every measure `P`, the bound is `(∑ i, ∫⁻ E i (θ i) ∂P) / K` for any
almost everywhere measurable statistics, so that it suffices that the expectations of the
statistics at the true parameters sum to at most `K`, as for compound e-values.
This is the analogue for selected confidence sets of the false discovery rate control of e-BH.

## Main definitions

* `ProbabilityTheory.fcp C θ R`: the false coverage proportion of the sets `C i`, `i ∈ R`, at the
  true parameters `θ`.
* `ProbabilityTheory.eBY C δ R ω`: the confidence sets that the e-BY procedure reports at level `δ`
  for the selection `R`.

## Main statements

* `ProbabilityTheory.fcp_eBY_eConfSet_div_le`: pointwise, the false coverage proportion of e-BY
  divided by its level is at most the sum over the selected parameters of the statistics at the
  true parameters, divided by `K`.
* `ProbabilityTheory.lintegral_iSup_fcp_eBY_eConfSet_div_le`: the post-hoc bound
  `(∑ i, ∫⁻ E i (θ i) ∂P) / K` for any almost everywhere measurable statistics.
* `ProbabilityTheory.lintegral_iSup_fcp_eBY_div_le_one`,
  `ProbabilityTheory.lintegral_fcp_eBY_le`: **false coverage rate control by e-BY** for level-free
  e-confidence sets, post hoc and at a fixed level [RW, Theorem 13.7].

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Chapter 13.
* [XWR24] Z. Xu, R. Wang and A. Ramdas, *Post-selection inference for e-value based confidence
  intervals*, Electron. J. Statist. 18(1) (2024), 2292–2338.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### The false coverage proportion and the e-BY procedure -/

section EBY

variable {ι : Type*} [Fintype ι] {Θ : ι → Type*}

/-- **The e-BY procedure** at level `δ` [XWR24; RW, Definition 13.6]: for the selected set `R` of
parameters, it reports for each parameter the set of the family `C i` at the level
`δ * #R / K`, with `K` the number of parameters. Only the sets of the selected parameters enter
the false coverage proportion. -/
noncomputable def eBY (C : ∀ i, ℝ≥0∞ → Ω → Set (Θ i)) (δ : ℝ≥0∞) (R : Finset ι) (ω : Ω) :
    ∀ i, Set (Θ i) :=
  fun i ↦ C i (δ * #R / Fintype.card ι) ω

@[simp]
theorem eBY_apply (C : ∀ i, ℝ≥0∞ → Ω → Set (Θ i)) (δ : ℝ≥0∞) (R : Finset ι) (ω : Ω) (i : ι) :
    eBY C δ R ω i = C i (δ * #R / Fintype.card ι) ω := (rfl)

variable [DecidableEq ι]

/-- The **false coverage proportion** [RW, §13.2] of the sets `C i ⊆ Θ i` reported for the
selected parameters `i ∈ R`, when the true parameters are `θ i`: the proportion of the selected
`i` with `θ i ∉ C i`, and `0` for the empty selection. It is the false discovery proportion of `R`
when the true nulls are the parameters whose sets miss them. -/
noncomputable def fcp (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) (R : Finset ι) : ℝ≥0∞ :=
  fdp (Set.toFinite {i | θ i ∉ C i}).toFinset R

theorem fcp_def (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) (R : Finset ι) :
    fcp C θ R = fdp (Set.toFinite {i | θ i ∉ C i}).toFinset R := (rfl)

@[simp]
theorem fcp_empty (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) : fcp C θ ∅ = 0 :=
  fdp_empty_right _

/-- The false coverage proportion is at most one. -/
theorem fcp_le_one (C : ∀ i, Set (Θ i)) (θ : ∀ i, Θ i) (R : Finset ι) : fcp C θ R ≤ 1 :=
  fdp_le_one _ _

/-- **The false coverage proportion of e-BY, pointwise.** For statistics `E i` and true
parameters `θ`, the false coverage proportion of the e-confidence sets reported by e-BY at level
`δ` for the selection `R`, divided by `δ`, is at most `∑ i ∈ R, E i (θ i) ω / K`. A missed
parameter `i ∈ R` has `K / (δ * #R) ≤ E i (θ i) ω`, so its contribution `1 / #R` to the
proportion is at most `δ * E i (θ i) ω / K`. The bound holds at every level, `0` and `∞`
included. -/
theorem fcp_eBY_eConfSet_div_le (E : ∀ i, Θ i → Ω → ℝ≥0∞) (θ : ∀ i, Θ i) (δ : ℝ≥0∞)
    (R : Finset ι) (ω : Ω) :
    fcp (eBY (fun i ↦ eConfSet (E i)) δ R ω) θ R / δ ≤
      ∑ i ∈ R, E i (θ i) ω / Fintype.card ι := by
  rcases R.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  set N := (Set.toFinite {i | θ i ∉ eBY (fun i ↦ eConfSet (E i)) δ R ω i}).toFinset
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨j⟩).ne'
  have hR : (#R : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_ne_zero_of_mem hj)
  -- Each missed parameter contributes `1 / (#R * δ)`, at most its e-value over `K`.
  have hi : ∀ i ∈ N, (#R : ℝ≥0∞)⁻¹ / δ ≤ E i (θ i) ω / Fintype.card ι := by
    intro i hi
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, eBY_apply, notMem_eConfSet] at hi
    calc (#R : ℝ≥0∞)⁻¹ / δ = (δ * #R / Fintype.card ι)⁻¹ / Fintype.card ι := by
          rw [ENNReal.inv_div (.inl (ENNReal.natCast_ne_top _)) (.inl hK)]
          simp [div_eq_mul_inv, ENNReal.mul_inv, hR, mul_comm, mul_assoc,
            ENNReal.mul_inv_cancel hK (ENNReal.natCast_ne_top _)]
      _ ≤ E i (θ i) ω / Fintype.card ι := by gcongr
  calc fcp (eBY (fun i ↦ eConfSet (E i)) δ R ω) θ R / δ
      = ∑ _ ∈ R ∩ N, (#R : ℝ≥0∞)⁻¹ / δ := by
        rw [fcp_def, fdp_eq_sum_inv_card, ENNReal.sum_div]
    _ ≤ ∑ i ∈ R ∩ N, E i (θ i) ω / Fintype.card ι :=
        sum_le_sum fun i hi' ↦ hi i (mem_inter.1 hi').2
    _ ≤ ∑ i ∈ R, E i (θ i) ω / Fintype.card ι := sum_le_sum_of_subset inter_subset_left

/-- **Post-hoc false coverage rate of e-BY for any statistics.** For statistics `E i` and true
parameters `θ` such that each `E i (θ i)` is almost everywhere measurable for a measure `P`, the
expected largest ratio of the false coverage proportion of the e-confidence sets reported by e-BY
to its level, over all selections and all levels, is at most `(∑ i, ∫⁻ E i (θ i) ∂P) / K`. -/
theorem lintegral_iSup_fcp_eBY_eConfSet_div_le {E : ∀ i, Θ i → Ω → ℝ≥0∞} {θ : ∀ i, Θ i}
    {P : Measure Ω} (hE : ∀ i, AEMeasurable (E i (θ i)) P) :
    ∫⁻ ω, ⨆ (R : Finset ι) (δ : ℝ≥0∞), fcp (eBY (fun i ↦ eConfSet (E i)) δ R ω) θ R / δ ∂P ≤
      (∑ i, ∫⁻ ω, E i (θ i) ω ∂P) / Fintype.card ι :=
  (lintegral_mono fun ω ↦ iSup₂_le fun R δ ↦ (fcp_eBY_eConfSet_div_le E θ δ R ω).trans
    (sum_le_sum_of_subset (subset_univ R))).trans_eq (lintegral_finsetSum_div (fun i _ ↦ hE i) _)

variable {C : ∀ i, ℝ≥0∞ → Ω → Set (Θ i)} {S : ∀ i, Θ i → Set (Measure Ω)} {θ : ∀ i, Θ i}
  {P : Measure Ω}

/-- **Post-hoc false coverage rate control by e-BY** [XWR24; RW, Theorem 13.7]: for level-free
families of e-confidence sets `C i` for the nulls `S i`, and a measure `P` of which every `θ i`
is a true parameter, the expected largest ratio of the false coverage proportion of e-BY to its
level, over all selections `R` and all levels `δ`, is at most one. This holds under arbitrary
dependence between the e-variables, and it covers every selection rule and every level chosen
after seeing the data. -/
theorem lintegral_iSup_fcp_eBY_div_le_one (hC : ∀ i, IsLevelFreeEConfSet (C i) (S i))
    (hP : ∀ i, P ∈ S i (θ i)) :
    ∫⁻ ω, ⨆ (R : Finset ι) (δ : ℝ≥0∞), fcp (eBY C δ R ω) θ R / δ ∂P ≤ 1 := by
  obtain ⟨E, hE, rfl⟩ := forall_isLevelFreeEConfSet_iff.1 hC
  -- the mean of the `K` expectations, each at most one, is at most one
  exact (lintegral_iSup_fcp_eBY_eConfSet_div_le fun i ↦ (hE i (θ i)).measurable.aemeasurable).trans
    (ENNReal.div_le_of_le_mul ((sum_le_sum fun i _ ↦ (hE i (θ i)).lintegral_le_one (hP i)).trans_eq
      (by simp)))

/-- **False coverage rate control by e-BY** [XWR24; RW, Theorem 13.7]: for level-free families of
e-confidence sets `C i` for the nulls `S i`, a measure `P` of which every `θ i` is a true
parameter, any selection rule `R : Ω → Finset ι` and any level `δ`, the false coverage rate of
the e-confidence sets reported by e-BY is at most `δ`. This holds under arbitrary dependence
between the e-variables, with no condition on the selection rule. -/
theorem lintegral_fcp_eBY_le (hC : ∀ i, IsLevelFreeEConfSet (C i) (S i)) (hP : ∀ i, P ∈ S i (θ i))
    (R : Ω → Finset ι) (δ : ℝ≥0∞) :
    ∫⁻ ω, fcp (eBY C δ (R ω) ω) θ (R ω) ∂P ≤ δ := by
  rcases eq_or_ne δ ∞ with rfl | hδ
  · exact le_top
  rcases eq_or_ne δ 0 with rfl | hδ₀
  · -- at level `0` a missed parameter has an infinite e-value, so almost surely nothing is missed
    obtain ⟨E, hE, rfl⟩ := forall_isLevelFreeEConfSet_iff.1 hC
    refine (lintegral_congr_ae ?_).trans_le lintegral_zero.le
    filter_upwards [ae_all_iff.2 fun i ↦ (hE i (θ i)).ae_lt_top (hP i)] with ω hω
    simp [fcp_def, hω]
  -- otherwise `fcp = δ * (fcp / δ)` is at most `δ` times the post-hoc supremum
  calc ∫⁻ ω, fcp (eBY C δ (R ω) ω) θ (R ω) ∂P
      ≤ ∫⁻ ω, δ * ⨆ (R : Finset ι) (δ : ℝ≥0∞), fcp (eBY C δ R ω) θ R / δ ∂P :=
        lintegral_mono fun ω ↦ (ENNReal.mul_div_cancel hδ₀ hδ).symm.le.trans (by
          gcongr; exact le_iSup₂ (f := fun R δ ↦ fcp (eBY C δ R ω) θ R / δ) (R ω) δ)
    _ = δ * ∫⁻ ω, ⨆ (R : Finset ι) (δ : ℝ≥0∞), fcp (eBY C δ R ω) θ R / δ ∂P :=
        lintegral_const_mul' _ _ hδ
    _ ≤ δ * 1 := by gcongr; exact lintegral_iSup_fcp_eBY_div_le_one hC hP
    _ = δ := mul_one δ

end EBY

end ProbabilityTheory
