/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.MultipleTesting.EBH
public import Mathlib.Probability.Independence.Basic
import LMLExplore.Probability.Distributions.Bernoulli
import LMLExplore.Probability.Independence.InverseSum

/-!
# Adaptive e-BH: a null-proportion estimate built from the e-values

For `K` hypotheses with e-values `e k`, a measurable `h : ℝ≥0∞ → ℝ≥0∞` with values in `[0, 1]`
and `q > 0`, the **null-proportion estimate** is
`π̂₀ = (1 + ∑ k, h (e k)) / (K * q)` (`ProbabilityTheory.nullProportionEstimate`). For a level
`t > 1`, the function `h e = (1 - e / t)₊` and `q = 1 - t⁻¹` give the estimate of
[EVR26, Note 33]; every `h` with `1 - e / t ≤ h e` may be used, as `h e = 𝟙{e < t}`.

If the e-values of the true hypotheses are mutually independent, nothing being assumed on the
others, and `q ≤ E[h (E)]` for every null e-value `E`, the e-values divided by `π̂₀` are compound
e-variables (`ProbabilityTheory.isCompoundEVar_div_nullProportionEstimate`; at a level `t`,
`ProbabilityTheory.isCompoundEVar_div_nullProportionEstimate_one_sub_inv`). So every rejection set
that is self-consistent at the level `α / π̂₀`, in particular e-BH at that level, has false
discovery rate at most `α`: this is a null-proportion adaptive e-BH procedure, the analogue for
e-values of Storey's procedure, whose estimate is built from the e-values themselves. The proof
bounds the expectation of `(1 + ∑ j, h (e j))⁻¹` over the other true nulls by the inverse moment
of a binomial variable (`ProbabilityTheory.lintegral_inv_one_add_sum_le`), as [MD26] does for
p-values and [IWR26] for compound e-values.

The **leave-one-out e-values** `F i = K * q * e i / (1 + ∑ j ≠ i, h (e j))`
(`ProbabilityTheory.leaveOneOutEValue`) improve the procedure: under the same hypothesis the
`F i / (1 - (1 - q) ^ K)` are compound e-variables
(`ProbabilityTheory.isCompoundEVar_leaveOneOutEValue_div`; the divisor is `1 - t⁻¹ ^ K` at a level
`t`), they are at least the `e i / π̂₀`, so e-BH applied to them rejects at least what e-BH at
the level `α / π̂₀` rejects (`ProbabilityTheory.eBH_div_nullProportionEstimate_subset`).

The proof of validity uses only that `q ≤ E[h (E)]` for every null e-value `E`. Among the
functions with that property the truncated linear ones are the only ones worth using
(`ProbabilityTheory.forall_one_add_inv_le_or_exists_nullProportionEstimate_le`): either the
estimate built on `g` is more than `1` at all finite e-values, so that the procedure is more
conservative than e-BH at level `α`, or it is at least an estimate of [EVR26, Note 33].

## Main definitions

* `ProbabilityTheory.nullProportionEstimate h q e`: the estimate `(1 + ∑ k, h (e k)) / (K * q)`.
* `ProbabilityTheory.leaveOneOutEValue h q e i`: the leave-one-out e-value
  `K * q * e i / (1 + ∑ j ≠ i, h (e j))`.

## Main statements

* `ProbabilityTheory.sum_lintegral_leaveOneOutEValue_le`: for a set `N` of hypotheses whose
  e-values `E i` are independent, with `E[E i] ≤ 1` and `q ≤ E[h (E i)]` for `i ∈ N`, the
  expectations of the leave-one-out e-values of the hypotheses of `N` sum to at most
  `K * (1 - (1 - q) ^ #N)`.
* `ProbabilityTheory.sum_lintegral_div_nullProportionEstimate_le`: the same with the e-values
  divided by the estimate, at most `K`.
* `ProbabilityTheory.isCompoundEVar_div_nullProportionEstimate`,
  `ProbabilityTheory.lintegral_fdp_le_of_isSelfConsistent_div_nullProportionEstimate`,
  `ProbabilityTheory.lintegral_fdp_eBH_div_nullProportionEstimate_le`: the adaptive e-BH
  procedure controls the false discovery rate [EVR26, Note 33, statement 1].
* `ProbabilityTheory.isCompoundEVar_leaveOneOutEValue_div`,
  `ProbabilityTheory.eBH_div_nullProportionEstimate_subset`: the leave-one-out improvement
  [EVR26, Note 33, statement 4].
* `ProbabilityTheory.one_sub_inv_le_lintegral_comp`: `1 - t⁻¹ ≤ E[h (E)]` for an e-value `E` and
  `h ≥ 1 - · / t`, so that the estimate of a level `t` is valid:
  `ProbabilityTheory.isCompoundEVar_div_nullProportionEstimate_one_sub_inv`,
  `ProbabilityTheory.isCompoundEVar_leaveOneOutEValue_one_sub_inv_div`.
* `ProbabilityTheory.forall_le_or_exists_mul_one_sub_div_le`,
  `ProbabilityTheory.one_add_inv_le_nullProportionEstimate`,
  `ProbabilityTheory.nullProportionEstimate_le_of_mul_one_sub_div_le`,
  `ProbabilityTheory.forall_one_add_inv_le_or_exists_nullProportionEstimate_le`: the functions
  that can replace `h` [EVR26, Note 33, statement 3].

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 33, "A
  Storey-type adaptive e-BH", github.com/RemyDegenne/evalues_research, 2026.
* [MD26] I. Meah and S. Döhler, *Improved null proportion estimators for multiple discrete tests
  with plug-in FDR control*, Comput. Statist. Data Anal. 224 (2026), arXiv:2307.13557.
* [IWR26] N. Ignatiadis, R. Wang and A. Ramdas, *Tiny but uniform improvements of adaptive BH
  procedures via compound e-values*, arXiv:2603.21424.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Fintype ι]

/-! ### The estimate and the leave-one-out e-values -/

section Estimate

variable (h : ℝ≥0∞ → ℝ≥0∞) (q : ℝ≥0∞) (e : ι → ℝ≥0∞)

/-- **The null-proportion estimate** `π̂₀ = (1 + ∑ k, h (e k)) / (K * q)` of the e-values `e`, for
`K` hypotheses [EVR26, Note 33]. -/
noncomputable def nullProportionEstimate : ℝ≥0∞ :=
  (1 + ∑ k, h (e k)) / (Fintype.card ι * q)

theorem nullProportionEstimate_def :
    nullProportionEstimate h q e = (1 + ∑ k, h (e k)) / (Fintype.card ι * q) :=
  (rfl)

/-- **The leave-one-out e-value** `K * q * e i / (1 + ∑ j ≠ i, h (e j))` of the hypothesis `i`
[EVR26, Note 33]. -/
noncomputable def leaveOneOutEValue [DecidableEq ι] (i : ι) : ℝ≥0∞ :=
  Fintype.card ι * q * e i / (1 + ∑ j ∈ univ.erase i, h (e j))

theorem leaveOneOutEValue_def [DecidableEq ι] (i : ι) :
    leaveOneOutEValue h q e i = Fintype.card ι * q * e i / (1 + ∑ j ∈ univ.erase i, h (e j)) :=
  (rfl)

/-- The e-values divided by the null-proportion estimate are at most the leave-one-out
e-values. -/
theorem div_nullProportionEstimate_le_leaveOneOutEValue [DecidableEq ι] {q : ℝ≥0∞}
    (hq : q ≠ ∞) (i : ι) : e i / nullProportionEstimate h q e ≤ leaveOneOutEValue h q e i := by
  rw [nullProportionEstimate_def, leaveOneOutEValue_def, ENNReal.div_eq_inv_mul,
    ENNReal.inv_div (.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hq))
      (.inr (zero_lt_one.trans_le le_self_add).ne'), div_eq_mul_inv,
    div_eq_mul_inv, mul_right_comm]
  gcongr
  exact erase_subset i univ

variable {h} {E : ι → Ω → ℝ≥0∞}

theorem measurable_nullProportionEstimate (hh : Measurable h) (hE : ∀ i, Measurable (E i)) :
    Measurable fun ω ↦ nullProportionEstimate h q (E · ω) := by
  simp_rw [nullProportionEstimate_def]
  exact (measurable_const.add (Finset.measurable_sum _ fun k _ ↦ hh.comp (hE k))).div_const _

theorem measurable_leaveOneOutEValue [DecidableEq ι] (hh : Measurable h)
    (hE : ∀ i, Measurable (E i)) (i : ι) :
    Measurable fun ω ↦ leaveOneOutEValue h q (E · ω) i := by
  simp_rw [leaveOneOutEValue_def]
  exact ((hE i).const_mul _).div
    (measurable_const.add (Finset.measurable_sum _ fun k _ ↦ hh.comp (hE k)))

end Estimate

/-! ### Validity under independent null e-values -/

section Validity

variable {h : ℝ≥0∞ → ℝ≥0∞} {q : ℝ≥0∞} {E : ι → Ω → ℝ≥0∞} [DecidableEq ι]

/-- A lower bound `q` on the expectation of `h (X)` under a probability measure, for `h ≤ 1`, is
at most `1`. -/
private lemma le_one_of_le_lintegral_comp {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ≥0∞} (hh1 : ∀ x, h x ≤ 1) (hq : q ≤ ∫⁻ ω, h (X ω) ∂P) : q ≤ 1 :=
  hq.trans ((lintegral_mono fun ω ↦ hh1 _).trans_eq (by simp))

omit [Fintype ι] in
/-- **The leave-one-out bound for one true null.** If the e-values `E j`, `j ∈ N`, are independent,
`E i` has expectation at most `1` for `i ∈ N`, and `q ≤ E[h (E j)]` for `j ∈ N`, then
`E[E i * (1 + ∑ j ∈ N \ {i}, h (E j))⁻¹] ≤ (1 - (1 - q) ^ #N) / (#N * q)`. -/
private lemma lintegral_mul_inv_one_add_sum_erase_le {P : Measure Ω}
    [IsProbabilityMeasure P] {N : Finset ι} (hE : ∀ i ∈ N, Measurable (E i))
    (hE1 : ∀ i ∈ N, ∫⁻ ω, E i ω ∂P ≤ 1) (hind : iIndepFun (fun i : N ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1) (hq0 : q ≠ 0) (hq1 : q ≤ 1)
    (hq : ∀ i ∈ N, q ≤ ∫⁻ ω, h (E i ω) ∂P) {i : ι} (hi : i ∈ N) :
    ∫⁻ ω, E i ω * (1 + ∑ j ∈ N.erase i, h (E j ω))⁻¹ ∂P ≤
      (1 - (1 - q) ^ #N) / (#N * q) := by
  have hE' : ∀ j : N, Measurable (E j) := fun j ↦ hE j j.property
  have h_sum (ω : Ω) : ∑ j ∈ (univ : Finset N).erase ⟨i, hi⟩, h (E j ω) =
      ∑ j ∈ N.erase i, h (E j ω) := by
    rw [univ_eq_attach]
    exact sum_erase_attach (fun j ↦ h (E j ω)) ⟨i, hi⟩
  have h_meas : Measurable fun v : ((univ : Finset N).erase ⟨i, hi⟩) → ℝ≥0∞ ↦
      (1 + ∑ j, h (v j))⁻¹ :=
    (measurable_const.add (Finset.measurable_sum _ fun j _ ↦
      hh.comp (measurable_pi_apply j))).inv
  have hg_meas : Measurable fun ω ↦ (1 + ∑ j ∈ N.erase i, h (E j ω))⁻¹ :=
    (measurable_const.add (Finset.measurable_sum _ fun j hj ↦
      hh.comp (hE j (mem_of_mem_erase hj)))).inv
  -- `E i` is independent of the e-values of the other true nulls.
  have h_indep : IndepFun (E i) (fun ω ↦ (1 + ∑ j ∈ N.erase i, h (E j ω))⁻¹) P := by
    have := (hind.indepFun_finset {⟨i, hi⟩} ((univ : Finset N).erase ⟨i, hi⟩) (by simp)
      hE').comp (measurable_pi_apply ⟨⟨i, hi⟩, mem_singleton_self _⟩) h_meas
    have h_eq : (fun ω ↦ (1 + ∑ j ∈ N.erase i, h (E j ω))⁻¹) =
        (fun v : ((univ : Finset N).erase ⟨i, hi⟩) → ℝ≥0∞ ↦ (1 + ∑ j, h (v j))⁻¹) ∘
          fun ω (j : ((univ : Finset N).erase ⟨i, hi⟩)) ↦ E j ω := by
      funext ω
      rw [Function.comp_apply, sum_coe_sort ((univ : Finset N).erase ⟨i, hi⟩)
        (fun j ↦ h (E j ω)), h_sum]
    rw [h_eq]
    exact this
  have h_card : #((univ : Finset N).erase ⟨i, hi⟩) + 1 = #N := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_coe,
      Nat.sub_add_cancel (card_pos.2 ⟨i, hi⟩)]
  have h_inv := lintegral_inv_one_add_sum_le (hind.comp (fun _ ↦ h) fun _ ↦ hh)
    ((univ : Finset N).erase ⟨i, hi⟩) (fun j _ ↦ hh.comp (hE' j))
    (fun j _ ↦ ae_of_all _ fun ω ↦ hh1 _) hq0 hq1 fun j _ ↦ hq j j.property
  simp only [Function.comp_apply, h_sum, ← Nat.cast_add_one, h_card] at h_inv
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hE i hi).aemeasurable
    hg_meas.aemeasurable h_indep]
  exact (mul_le_mul' (hE1 i hi) h_inv).trans_eq (one_mul _)

/-- **The leave-one-out e-values of independent null e-values** [EVR26, Note 33, statements 1
and 4]. Let the e-values `E i`, `i ∈ N`, be independent under the probability measure `P`, with
expectations at most `1`, and let `h ≤ 1` be measurable with `q ≤ E[h (E i)]` for `i ∈ N`. Then
the leave-one-out e-values of the hypotheses of `N` have expectations summing to at most
`K * (1 - (1 - q) ^ #N)`. Nothing is assumed on the e-values of the hypotheses outside `N`. -/
theorem sum_lintegral_leaveOneOutEValue_le {P : Measure Ω} [IsProbabilityMeasure P]
    {N : Finset ι} (hE : ∀ i ∈ N, Measurable (E i)) (hE1 : ∀ i ∈ N, ∫⁻ ω, E i ω ∂P ≤ 1)
    (hind : iIndepFun (fun i : N ↦ E i) P) (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1)
    (hq : ∀ i ∈ N, q ≤ ∫⁻ ω, h (E i ω) ∂P) :
    ∑ i ∈ N, ∫⁻ ω, leaveOneOutEValue h q (E · ω) i ∂P ≤
      Fintype.card ι * (1 - (1 - q) ^ #N) := by
  rcases N.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [leaveOneOutEValue_def]
  have hq1 : q ≤ 1 := le_one_of_le_lintegral_comp hh1 (hq i₀ hi₀)
  have hq_top : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  have hN0 : (#N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 ⟨i₀, hi₀⟩).ne'
  calc ∑ i ∈ N, ∫⁻ ω, leaveOneOutEValue h q (E · ω) i ∂P
      ≤ ∑ i ∈ N, ∫⁻ ω, Fintype.card ι * q *
          (E i ω * (1 + ∑ j ∈ N.erase i, h (E j ω))⁻¹) ∂P := by
        refine sum_le_sum fun i hi ↦ lintegral_mono fun ω ↦ ?_
        rw [leaveOneOutEValue_def, div_eq_mul_inv, mul_assoc]
        gcongr
        exact subset_univ N
    _ ≤ ∑ _i ∈ N, Fintype.card ι * q * ((1 - (1 - q) ^ #N) / (#N * q)) := by
        refine sum_le_sum fun i hi ↦ ?_
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hq_top)]
        gcongr
        exact lintegral_mul_inv_one_add_sum_erase_le hE hE1 hind hh hh1 hq0 hq1 hq hi
    _ = Fintype.card ι * (#N * q * ((1 - (1 - q) ^ #N) / (#N * q))) := by
        rw [sum_const, nsmul_eq_mul]
        ring
    _ = Fintype.card ι * (1 - (1 - q) ^ #N) := by
        rw [ENNReal.mul_div_cancel (mul_ne_zero hN0 hq0)
          (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hq_top)]

omit [DecidableEq ι] in
/-- **The adaptive e-values of independent null e-values have total expectation at most `K`**
[EVR26, Note 33, statement 1]: under the hypotheses of `sum_lintegral_leaveOneOutEValue_le`, the
expectations of the e-values of `N` divided by the null-proportion estimate sum to at most `K`. -/
theorem sum_lintegral_div_nullProportionEstimate_le {P : Measure Ω} [IsProbabilityMeasure P]
    {N : Finset ι} (hE : ∀ i ∈ N, Measurable (E i)) (hE1 : ∀ i ∈ N, ∫⁻ ω, E i ω ∂P ≤ 1)
    (hind : iIndepFun (fun i : N ↦ E i) P) (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1)
    (hq : ∀ i ∈ N, q ≤ ∫⁻ ω, h (E i ω) ∂P) :
    ∑ i ∈ N, ∫⁻ ω, E i ω / nullProportionEstimate h q (E · ω) ∂P ≤ Fintype.card ι := by
  classical
  exact (sum_le_sum fun i hi ↦ lintegral_mono fun ω ↦
    div_nullProportionEstimate_le_leaveOneOutEValue h (E · ω)
      (ne_top_of_le_ne_top ENNReal.one_ne_top (le_one_of_le_lintegral_comp hh1 (hq i hi))) i).trans
    ((sum_lintegral_leaveOneOutEValue_le hE hE1 hind hh hh1 hq).trans
      (mul_le_of_le_one_right' tsub_le_self))

end Validity

/-! ### Adaptive e-BH -/

section Adaptive

variable {H : ι → Set (Measure Ω)} {E : ι → Ω → ℝ≥0∞} {h : ℝ≥0∞ → ℝ≥0∞} {q : ℝ≥0∞}

/-- Under every probability measure, the leave-one-out e-values of the true nulls have
expectations summing to at most `K * (1 - (1 - q) ^ K₀)`, with `K₀` the number of true nulls. -/
private lemma sum_lintegral_leaveOneOutEValue_trueNulls_le [DecidableEq ι]
    (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P], iIndepFun (fun i : trueNulls H P ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1)
    (hq : ∀ i (P : Measure Ω) [IsProbabilityMeasure P], P ∈ H i → q ≤ ∫⁻ ω, h (E i ω) ∂P)
    (P : Measure Ω) [IsProbabilityMeasure P] :
    ∑ i ∈ trueNulls H P, ∫⁻ ω, leaveOneOutEValue h q (E · ω) i ∂P ≤
      Fintype.card ι * (1 - (1 - q) ^ #(trueNulls H P)) :=
  sum_lintegral_leaveOneOutEValue_le (fun i _ ↦ (hE i).measurable)
    (fun i hi ↦ (hE i).lintegral_le_one (mem_trueNulls.1 hi)) (hind P) hh hh1
    fun i hi ↦ hq i P (mem_trueNulls.1 hi)

/-- **Adaptive e-values are compound e-variables** [EVR26, Note 33, statement 1]. Let `E i` be
e-variables for the hypotheses `H i` such that, under every probability measure, the e-values of
the true nulls are independent. For a measurable `h ≤ 1` with `q ≤ E_P[h (E i)]` whenever `P` is a
probability measure of `H i`, the e-values divided by the null-proportion estimate
`(1 + ∑ k, h (E k)) / (K * q)` are compound e-variables. The estimate of [EVR26, Note 33] at a
level `t` is `isCompoundEVar_div_nullProportionEstimate_one_sub_inv`. -/
theorem isCompoundEVar_div_nullProportionEstimate (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P], iIndepFun (fun i : trueNulls H P ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1)
    (hq : ∀ i (P : Measure Ω) [IsProbabilityMeasure P], P ∈ H i → q ≤ ∫⁻ ω, h (E i ω) ∂P) :
    IsCompoundEVar (fun i ω ↦ E i ω / nullProportionEstimate h q (E · ω)) H where
  measurable i := (hE i).measurable.div
    (measurable_nullProportionEstimate _ hh fun j ↦ (hE j).measurable)
  sum_lintegral_le P _ := sum_lintegral_div_nullProportionEstimate_le
    (fun i _ ↦ (hE i).measurable) (fun i hi ↦ (hE i).lintegral_le_one (mem_trueNulls.1 hi))
    (hind P) hh hh1 fun i hi ↦ hq i P (mem_trueNulls.1 hi)

/-- **Adaptive e-BH controls the false discovery rate** [EVR26, Note 33, statement 1]: under the
hypotheses of `isCompoundEVar_div_nullProportionEstimate`, every rejection procedure
self-consistent for the e-values `E` at the level `α / π̂₀`, with `π̂₀` the null-proportion
estimate, has false discovery rate at most `α`. -/
theorem lintegral_fdp_le_of_isSelfConsistent_div_nullProportionEstimate [DecidableEq ι]
    (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P], iIndepFun (fun i : trueNulls H P ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1)
    (hq : ∀ i (P : Measure Ω) [IsProbabilityMeasure P], P ∈ H i → q ≤ ∫⁻ ω, h (E i ω) ∂P)
    {α : ℝ≥0∞} {D : Ω → Finset ι}
    (hD : ∀ ω, IsSelfConsistent (E · ω) (α / nullProportionEstimate h q (E · ω)) (D ω))
    (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, fdp (trueNulls H P) (D ω) ∂P ≤ α :=
  (isCompoundEVar_div_nullProportionEstimate hE hind hh hh1 hq).lintegral_fdp_le
    (fun ω ↦ isSelfConsistent_div_iff.1 (hD ω)) P

/-- **False discovery rate control by adaptive e-BH** [EVR26, Note 33, statement 1]: under the
hypotheses of `isCompoundEVar_div_nullProportionEstimate`, e-BH applied at the level `α / π̂₀`,
with `π̂₀` the null-proportion estimate, has false discovery rate at most `α`. -/
theorem lintegral_fdp_eBH_div_nullProportionEstimate_le [DecidableEq ι]
    (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P], iIndepFun (fun i : trueNulls H P ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1)
    (hq : ∀ i (P : Measure Ω) [IsProbabilityMeasure P], P ∈ H i → q ≤ ∫⁻ ω, h (E i ω) ∂P)
    (α : ℝ≥0∞) (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, fdp (trueNulls H P)
      (eBH (E · ω) (α / nullProportionEstimate h q (E · ω))) ∂P ≤ α :=
  lintegral_fdp_le_of_isSelfConsistent_div_nullProportionEstimate hE hind hh hh1 hq
    (fun _ ↦ isSelfConsistent_eBH) P

/-- **The leave-one-out e-values are compound e-variables** [EVR26, Note 33, statement 4]: under
the hypotheses of `isCompoundEVar_div_nullProportionEstimate`, the leave-one-out e-values divided
by `1 - (1 - q) ^ K` are compound e-variables. So e-BH applied to them at level `α` has false
discovery rate at most `α` (`IsCompoundEVar.lintegral_fdp_eBH_le`), and it rejects at least what
adaptive e-BH rejects (`eBH_div_nullProportionEstimate_subset`). -/
theorem isCompoundEVar_leaveOneOutEValue_div [DecidableEq ι] (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P], iIndepFun (fun i : trueNulls H P ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1)
    (hq : ∀ i (P : Measure Ω) [IsProbabilityMeasure P], P ∈ H i → q ≤ ∫⁻ ω, h (E i ω) ∂P) :
    IsCompoundEVar
      (fun i ω ↦ leaveOneOutEValue h q (E · ω) i / (1 - (1 - q) ^ Fintype.card ι)) H where
  measurable i := (measurable_leaveOneOutEValue _ hh (fun j ↦ (hE j).measurable) i).div_const _
  sum_lintegral_le P _ := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp [Finset.eq_empty_of_isEmpty (trueNulls H P)]
    rcases eq_or_ne q 0 with rfl | hq0
    · simp [leaveOneOutEValue_def]
    have hc0 : 1 - (1 - q) ^ Fintype.card ι ≠ 0 :=
      (tsub_pos_of_lt (pow_lt_one₀ zero_le
        (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0) Fintype.card_ne_zero)).ne'
    simp_rw [div_eq_mul_inv]
    rw [sum_congr rfl fun i _ ↦ lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0), ← sum_mul]
    calc (∑ i ∈ trueNulls H P, ∫⁻ ω, leaveOneOutEValue h q (E · ω) i ∂P) *
          (1 - (1 - q) ^ Fintype.card ι)⁻¹
        ≤ Fintype.card ι * (1 - (1 - q) ^ Fintype.card ι) * (1 - (1 - q) ^ Fintype.card ι)⁻¹ := by
          gcongr
          refine (sum_lintegral_leaveOneOutEValue_trueNulls_le hE hind hh hh1 hq P).trans ?_
          gcongr _ * (1 - ?_)
          exact pow_le_pow_right_of_le_one' tsub_le_self (card_le_univ _)
      _ = Fintype.card ι := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hc0 (ENNReal.sub_ne_top ENNReal.one_ne_top),
            mul_one]

/-- **The leave-one-out procedure rejects at least what adaptive e-BH rejects** [EVR26, Note 33,
statement 4]. -/
theorem eBH_div_nullProportionEstimate_subset [DecidableEq ι] (hq : q ≠ ∞) (e : ι → ℝ≥0∞)
    (α : ℝ≥0∞) :
    eBH e (α / nullProportionEstimate h q e) ⊆
      eBH (fun i ↦ leaveOneOutEValue h q e i / (1 - (1 - q) ^ Fintype.card ι)) α := by
  rw [eBH_div]
  refine eBH_mono le_rfl fun i ↦ ?_
  rw [div_eq_mul_inv]
  exact (div_nullProportionEstimate_le_leaveOneOutEValue h e hq i).trans
    (le_mul_of_one_le_right' (ENNReal.one_le_inv.2 tsub_le_self))

end Adaptive

/-! ### Adaptive e-BH with the estimate of a level `t` -/

section Level

variable {H : ι → Set (Measure Ω)} {E : ι → Ω → ℝ≥0∞} {h : ℝ≥0∞ → ℝ≥0∞} {t : ℝ≥0∞}

/-- **A function above `1 - e / t` has expectation at least `1 - t⁻¹`** under an e-value: for
`1 - x / t ≤ h x` and `E[E] ≤ 1`, `1 - t⁻¹ ≤ E[h (E)]`. -/
theorem one_sub_inv_le_lintegral_comp {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hX1 : ∫⁻ ω, X ω ∂P ≤ 1) (hht : ∀ x, 1 - x / t ≤ h x) :
    1 - t⁻¹ ≤ ∫⁻ ω, h (X ω) ∂P := by
  have h_div : ∫⁻ ω, X ω / t ∂P = (∫⁻ ω, X ω ∂P) / t := by
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const _ hX
  calc 1 - t⁻¹ ≤ 1 - (∫⁻ ω, X ω ∂P) / t := by
        gcongr
        exact (ENNReal.div_le_div_right hX1 t).trans_eq (one_div t)
    _ ≤ ∫⁻ ω, (1 - X ω / t) ∂P := by
        rw [tsub_le_iff_right, ← h_div, ← lintegral_add_right _ (hX.div_const t)]
        calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂P := by simp
          _ ≤ ∫⁻ ω, (1 - X ω / t + X ω / t) ∂P := lintegral_mono fun ω ↦ le_tsub_add
    _ ≤ ∫⁻ ω, h (X ω) ∂P := lintegral_mono fun ω ↦ hht _

/-- **Adaptive e-values at a level `t` are compound e-variables** [EVR26, Note 33, statement 1]:
`isCompoundEVar_div_nullProportionEstimate` for `q = 1 - t⁻¹` and a measurable `h ≤ 1` with
`1 - x / t ≤ h x` (as `h x = 1 - x / t`), the estimate being
`(1 + ∑ k, h (E k)) / (K * (1 - t⁻¹))`. For `t ≤ 1` the estimate is `∞`, and only `t > 1` gives a
useful procedure. -/
theorem isCompoundEVar_div_nullProportionEstimate_one_sub_inv (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P], iIndepFun (fun i : trueNulls H P ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1) (hht : ∀ x, 1 - x / t ≤ h x) :
    IsCompoundEVar (fun i ω ↦ E i ω / nullProportionEstimate h (1 - t⁻¹) (E · ω)) H :=
  isCompoundEVar_div_nullProportionEstimate hE hind hh hh1 fun i _ _ hP ↦
    one_sub_inv_le_lintegral_comp (hE i).measurable ((hE i).lintegral_le_one hP) hht

/-- **The leave-one-out e-values at a level `t` are compound e-variables** [EVR26, Note 33,
statement 4]: `isCompoundEVar_leaveOneOutEValue_div` for `q = 1 - t⁻¹` and `1 - x / t ≤ h x`,
where the divisor `1 - (1 - q) ^ K` is `1 - t⁻¹ ^ K`. -/
theorem isCompoundEVar_leaveOneOutEValue_one_sub_inv_div [DecidableEq ι]
    (hE : ∀ i, IsEVar (E i) (H i))
    (hind : ∀ (P : Measure Ω) [IsProbabilityMeasure P], iIndepFun (fun i : trueNulls H P ↦ E i) P)
    (hh : Measurable h) (hh1 : ∀ x, h x ≤ 1) (hht : ∀ x, 1 - x / t ≤ h x) :
    IsCompoundEVar
      (fun i ω ↦ leaveOneOutEValue h (1 - t⁻¹) (E · ω) i / (1 - t⁻¹ ^ Fintype.card ι)) H := by
  have hc : 1 - (1 - (1 - t⁻¹)) ^ Fintype.card ι = 1 - t⁻¹ ^ Fintype.card ι := by
    rcases le_total t⁻¹ 1 with ht | ht
    · rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top ht]
    · rw [tsub_eq_zero_of_le ht, tsub_zero, one_pow, tsub_self,
        tsub_eq_zero_of_le (one_le_pow₀ ht)]
  simpa only [hc] using isCompoundEVar_leaveOneOutEValue_div hE hind hh hh1 fun i _ _ hP ↦
    one_sub_inv_le_lintegral_comp (hE i).measurable ((hE i).lintegral_le_one hP) hht

end Level

/-! ### The functions that can replace `h` -/

section Functions

variable {g : ℝ≥0∞ → ℝ≥0∞} {q : ℝ≥0∞}

/-- **Point masses**: if `q ≤ ∫⁻ x, g x ∂μ` for every probability measure `μ` on `ℝ≥0∞` with
mean at most `1`, then `q ≤ g x` for `x ≤ 1`. -/
private lemma le_of_forall_le_lintegral
    (hg : ∀ μ : Measure ℝ≥0∞, IsProbabilityMeasure μ → ∫⁻ x, x ∂μ ≤ 1 → q ≤ ∫⁻ x, g x ∂μ)
    {x : ℝ≥0∞} (hx : x ≤ 1) : q ≤ g x := by
  simpa [lintegral_dirac] using hg (Measure.dirac x) inferInstance (by simpa using hx)

/-- If `g ≤ 1` and `q ≤ ∫⁻ x, g x ∂μ` for every probability measure `μ` on `ℝ≥0∞` with mean at
most `1`, then `q` is finite. -/
private lemma ne_top_of_forall_le_lintegral (hg1 : ∀ x, g x ≤ 1)
    (hg : ∀ μ : Measure ℝ≥0∞, IsProbabilityMeasure μ → ∫⁻ x, x ∂μ ≤ 1 → q ≤ ∫⁻ x, g x ∂μ) :
    q ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top ((le_of_forall_le_lintegral hg zero_le).trans (hg1 0))

/-- **Two-point laws**: if `q ≤ ∫⁻ x, g x ∂μ` for every probability measure `μ` on `ℝ≥0∞` with
mean at most `1`, then the Bernoulli law on `{a, b}` with mean `1`, for `0 ≤ a < 1 < b`, gives
`(b - a) * q ≤ (b - 1) * g a + (1 - a) * g b`, in real numbers. -/
private lemma sub_mul_toReal_le_of_forall_le_lintegral (hg_top : ∀ x, g x ≠ ∞)
    (hg : ∀ μ : Measure ℝ≥0∞, IsProbabilityMeasure μ → ∫⁻ x, x ∂μ ≤ 1 → q ≤ ∫⁻ x, g x ∂μ)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hb1 : 1 < b) :
    (b - a) * q.toReal ≤
      (b - 1) * (g (ENNReal.ofReal a)).toReal + (1 - a) * (g (ENNReal.ofReal b)).toReal := by
  have hba : 0 < b - a := by linarith
  -- The Bernoulli law with weight `w = (b - 1) / (b - a)` on `a` has mean `1`.
  set w : unitInterval := ⟨(b - 1) / (b - a), div_nonneg (by linarith) hba.le,
    (div_le_one hba).2 (by linarith)⟩
  have hw : (1 : ℝ) - w = (1 - a) / (b - a) := by
    simp only [w]
    field_simp
    ring
  have h_mean : ∫⁻ x, x ∂Ber(ENNReal.ofReal a, ENNReal.ofReal b, w) ≤ 1 := by
    rw [lintegral_id_bernoulliMeasure_ofReal ha0 (by linarith), hw]
    exact ENNReal.ofReal_le_one.2 (le_of_eq (by simp only [w]; field_simp; ring))
  have h := hg _ inferInstance h_mean
  rw [lintegral_bernoulliMeasure] at h
  -- Both summands are finite, so `toReal` passes through the sum.
  have hfin : ∀ (c : ℝ) x, ENNReal.ofReal c * g x ≠ ∞ := fun _ x ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hg_top x)
  have h_real := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin _ _, hfin _ _⟩) h
  rw [ENNReal.toReal_add (hfin _ _) (hfin _ _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal w.property.1, ENNReal.toReal_ofReal (sub_nonneg.2 w.property.2), hw]
    at h_real
  calc (b - a) * q.toReal ≤ (b - a) * ((b - 1) / (b - a) * (g (ENNReal.ofReal a)).toReal +
        (1 - a) / (b - a) * (g (ENNReal.ofReal b)).toReal) :=
        mul_le_mul_of_nonneg_left h_real hba.le
    _ = (b - 1) * (g (ENNReal.ofReal a)).toReal + (1 - a) * (g (ENNReal.ofReal b)).toReal := by
        field_simp

/-- **The functions with a uniform lower bound on their expectation under e-values** [EVR26,
Note 33, statement 3]. Let `g ≤ 1` and `q` be such that `q ≤ E[g (X)]` for every random variable
`X ≥ 0` with `E[X] ≤ 1`, that is `q ≤ ∫⁻ x, g x ∂μ` for every probability measure `μ` on `ℝ≥0∞`
with mean at most `1`. Then either `q ≤ g x` at every finite `x`, or `r * (1 - x / t) ≤ g x`
everywhere, for some `r ≤ 1` and some finite `t > 1` with `q = r * (1 - t⁻¹)`. -/
theorem forall_le_or_exists_mul_one_sub_div_le (hg1 : ∀ x, g x ≤ 1)
    (hg : ∀ μ : Measure ℝ≥0∞, IsProbabilityMeasure μ → ∫⁻ x, x ∂μ ≤ 1 → q ≤ ∫⁻ x, g x ∂μ) :
    (∀ x ≠ ∞, q ≤ g x) ∨
      ∃ r t : ℝ≥0∞, r ≤ 1 ∧ 1 < t ∧ t ≠ ∞ ∧ q = r * (1 - t⁻¹) ∧ ∀ x, r * (1 - x / t) ≤ g x := by
  have hq_top : q ≠ ∞ := ne_top_of_forall_le_lintegral hg1 hg
  rcases eq_or_ne q 0 with hq0 | hq0
  · exact .inl fun x _ ↦ hq0 ▸ zero_le
  -- The real counterparts `Q` of `q` and `G` of `g`.
  set Q := q.toReal
  set G : ℝ → ℝ := fun x ↦ (g (ENNReal.ofReal x)).toReal
  have hg_top (x : ℝ≥0∞) : g x ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hg1 x)
  have hG1 (x : ℝ) : G x ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hg1 _)
  have hG (x : ℝ) : g (ENNReal.ofReal x) = ENNReal.ofReal (G x) :=
    (ENNReal.ofReal_toReal (hg_top _)).symm
  have hQ : q = ENNReal.ofReal Q := (ENNReal.ofReal_toReal hq_top).symm
  have hQ0 : 0 < Q := ENNReal.toReal_pos hq0 hq_top
  -- Point masses at `x ≤ 1` give `Q ≤ G x`; laws on two points `a < 1 < b` with mean `1` bound
  -- the slopes of `G` on both sides of `1` (`sub_mul_toReal_le_of_forall_le_lintegral`).
  have h_small (x : ℝ) (hx1 : x ≤ 1) : Q ≤ G x :=
    (ENNReal.toReal_le_toReal hq_top (hg_top _)).2
      (le_of_forall_le_lintegral hg (ENNReal.ofReal_le_one.2 hx1))
  -- The supremum `β` of the slopes `(Q - G b) / (b - 1)` over `b > 1`.
  set A : Set ℝ := (fun b ↦ (Q - G b) / (b - 1)) '' Set.Ioi 1
  have hA_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) : ∀ y ∈ A, y ≤ (G a - Q) / (1 - a) := by
    rintro _ ⟨b, hb, rfl⟩
    have hb : 1 < b := hb
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [sub_mul_toReal_le_of_forall_le_lintegral hg_top hg ha0 ha1 hb]
  have hA_ne : A.Nonempty := ⟨_, Set.mem_image_of_mem _ (show (2 : ℝ) ∈ Set.Ioi 1 by norm_num)⟩
  have hA_bdd : BddAbove A := ⟨_, hA_le 0 le_rfl zero_lt_one⟩
  set β := sSup A
  have hG_lin (x : ℝ) (hx0 : 0 ≤ x) : Q + β * (1 - x) ≤ G x := by
    rcases lt_trichotomy x 1 with hx | rfl | hx
    · have h := csSup_le hA_ne (hA_le x hx0 hx)
      rw [le_div_iff₀ (by linarith)] at h
      linarith
    · simpa using h_small 1 le_rfl
    · have h := le_csSup hA_bdd (Set.mem_image_of_mem _ (show x ∈ Set.Ioi 1 from hx))
      rw [div_le_iff₀ (by linarith)] at h
      linarith
  rcases le_or_gt β 0 with hβ0 | hβ0
  · refine .inl fun x hx ↦ ?_
    rw [← ENNReal.ofReal_toReal hx, hG, hQ]
    refine ENNReal.ofReal_le_ofReal ?_
    rcases le_or_gt x.toReal 1 with hx1 | hx1
    · exact h_small _ hx1
    · nlinarith [hG_lin x.toReal ENNReal.toReal_nonneg]
  · have hβG : Q + β ≤ G 0 := by simpa using hG_lin 0 le_rfl
    refine .inr ⟨ENNReal.ofReal (Q + β), ENNReal.ofReal ((Q + β) / β),
      ENNReal.ofReal_le_one.2 (hβG.trans (hG1 0)),
      ENNReal.one_lt_ofReal.2 ((one_lt_div hβ0).2 (by linarith)), ENNReal.ofReal_ne_top, ?_,
      fun x ↦ ?_⟩
    · rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_sub _ (by positivity), ← ENNReal.ofReal_mul (by positivity), hQ]
      congr 1
      field_simp
      ring
    rcases eq_or_ne x ∞ with rfl | hx
    · rw [ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, tsub_eq_zero_of_le le_top, mul_zero]
      exact zero_le
    rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_div_of_pos (by positivity),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hG]
    refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans (hG_lin _ ENNReal.toReal_nonneg))
    field_simp
    ring

/-- **An estimate built on a function bounded below is more than `1`**: if `q ≤ g (e k)` for
every `k`, the null-proportion estimate built on `g` is at least `1 + (K * q)⁻¹`. -/
theorem one_add_inv_le_nullProportionEstimate (hq : q ≠ ∞) (e : ι → ℝ≥0∞)
    (hge : ∀ k, q ≤ g (e k)) : 1 + (Fintype.card ι * q)⁻¹ ≤ nullProportionEstimate g q e := by
  rw [nullProportionEstimate_def]
  rcases eq_or_ne ((Fintype.card ι : ℝ≥0∞) * q) 0 with h0 | h0
  · rw [h0, ENNReal.div_zero (zero_lt_one.trans_le le_self_add).ne']
    exact le_top
  have htop : (Fintype.card ι : ℝ≥0∞) * q ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hq
  calc 1 + ((Fintype.card ι : ℝ≥0∞) * q)⁻¹ = (1 + Fintype.card ι * q) / (Fintype.card ι * q) := by
        rw [ENNReal.add_div, ENNReal.div_self h0 htop, one_div, add_comm]
    _ ≤ (1 + ∑ k, g (e k)) / (Fintype.card ι * q) := by
        gcongr
        calc (Fintype.card ι : ℝ≥0∞) * q = ∑ _k : ι, q := by
              rw [sum_const, card_univ, nsmul_eq_mul]
          _ ≤ ∑ k, g (e k) := sum_le_sum fun k _ ↦ hge k

/-- **An estimate built on a function above a truncated linear one** is at least the estimate of
[EVR26, Note 33] at the level `t`: if `r ≤ 1` and `r * (1 - x / t) ≤ g x` for every `x`, the
null-proportion estimate built on `g` and `r * (1 - t⁻¹)` is at least the one built on
`x ↦ 1 - x / t` and `1 - t⁻¹`. -/
theorem nullProportionEstimate_le_of_mul_one_sub_div_le {r t : ℝ≥0∞} (hr : r ≤ 1)
    (hg : ∀ x, r * (1 - x / t) ≤ g x) (e : ι → ℝ≥0∞) :
    nullProportionEstimate (fun x ↦ 1 - x / t) (1 - t⁻¹) e ≤
      nullProportionEstimate g (r * (1 - t⁻¹)) e := by
  rw [nullProportionEstimate_def, nullProportionEstimate_def]
  rcases eq_or_ne ((Fintype.card ι : ℝ≥0∞) * (r * (1 - t⁻¹))) 0 with h0 | h0
  · rw [h0, ENNReal.div_zero (zero_lt_one.trans_le le_self_add).ne']
    exact le_top
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at h0
  have hr_top : r ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hr
  rw [← ENNReal.mul_div_mul_left _ _ hr0 hr_top, mul_left_comm r]
  gcongr ?_ / _
  rw [mul_add, mul_sum]
  exact add_le_add (by simpa using hr) (sum_le_sum fun k _ ↦ hg (e k))

/-- **The functions that can replace `h`** [EVR26, Note 33, statement 3]. Let `g ≤ 1` and `q` be
such that `q ≤ ∫⁻ x, g x ∂μ` for every probability measure `μ` on `ℝ≥0∞` with mean at most `1`,
which is what the validity of the adaptive procedure uses. Then either the null-proportion
estimate built on `g` and `q` is at least `1 + (K * q)⁻¹` at all finite e-values, so that the
procedure rejects less than e-BH at level `α`, or for some finite level `t > 1` it is everywhere at
least the estimate built on `x ↦ 1 - x / t` and `1 - t⁻¹`. -/
theorem forall_one_add_inv_le_or_exists_nullProportionEstimate_le (hg1 : ∀ x, g x ≤ 1)
    (hg : ∀ μ : Measure ℝ≥0∞, IsProbabilityMeasure μ → ∫⁻ x, x ∂μ ≤ 1 → q ≤ ∫⁻ x, g x ∂μ) :
    (∀ e : ι → ℝ≥0∞, (∀ k, e k ≠ ∞) →
        1 + (Fintype.card ι * q)⁻¹ ≤ nullProportionEstimate g q e) ∨
      ∃ t, 1 < t ∧ t ≠ ∞ ∧ ∀ e : ι → ℝ≥0∞,
        nullProportionEstimate (fun x ↦ 1 - x / t) (1 - t⁻¹) e ≤ nullProportionEstimate g q e := by
  have hq_top : q ≠ ∞ := ne_top_of_forall_le_lintegral hg1 hg
  rcases forall_le_or_exists_mul_one_sub_div_le hg1 hg with h | ⟨r, t, hr, ht, ht_top, rfl, h⟩
  · exact .inl fun e he ↦ one_add_inv_le_nullProportionEstimate hq_top e fun k ↦ h _ (he k)
  · exact .inr ⟨t, ht, ht_top, nullProportionEstimate_le_of_mul_one_sub_div_le hr h⟩

end Functions

end ProbabilityTheory
