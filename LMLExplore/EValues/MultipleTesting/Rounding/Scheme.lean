/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Data.Fintype.Fin
public import LMLExplore.EValues.MultipleTesting.EBH
public import LMLExplore.EValues.MultipleTesting.Rounding.Program
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Markov

/-!
# The optimal rounding of e-values for e-BH

A stochastic rounding scheme for e-BH [XR23] replaces the realized e-values `x i` by random
values `S i ≥ 0`, drawn with external randomization, whose conditional means given the data are at
most `x i`, and applies e-BH to them. Each `S i` is then an e-value for its hypothesis, so that
e-BH applied to `S` controls the false discovery rate, and it may reject more than e-BH applied to
`x`. For one realization `x`, a scheme is the law `μ` of the rounded values, a probability measure
on `ι → ℝ≥0∞` with `∫⁻ s, s i ∂μ ≤ x i` for every `i` (`ProbabilityTheory.IsRoundingScheme`).

[XR23, §8] asks which scheme maximizes the expected number of rejections for each realization.
The answer [EVR26, Note 30]: the law of the rejection set of a scheme is a feasible point of the
linear program of `LMLExplore.EValues.MultipleTesting.Rounding.Program` with the budgets
`y i = α * x i / K` (`ProbabilityTheory.roundingBudget`), so the expected number of rejections
is at most its value `V`; and the nested scheme that rejects the `N` hypotheses with the largest
e-values, for the random `N` of the optimal nested point, attains `V`
(`ProbabilityTheory.optimalRoundingScheme`).

U-eBH applies e-BH to `x i / U` for one uniform `U` on `[0, 1]`. A scheme is comonotone when every
rounded value is a nonincreasing function of one common uniform variable; the joint stochastic
rounding of [XR23], which rounds each e-value to one of two grid points around it with the same
uniform variable for all hypotheses (`ProbabilityTheory.stochasticRound`), is one. Every comonotone
scheme rejects, at every value of the uniform variable, a subset of what U-eBH rejects, so U-eBH
dominates every comonotone scheme (U-eBH is not itself one: `x i / U` has an infinite mean). It
does not dominate all schemes: for the e-values
`(8, 2)` at level `1/10`, U-eBH rejects `3/5` hypotheses on average and the optimal scheme `7/10`.

## Main definitions

* `ProbabilityTheory.IsRoundingScheme x μ`: `μ` is the law of a rounding of the e-values `x`.
* `ProbabilityTheory.roundingBudget α x`: the budgets `α * x i / K` of the linear program.
* `ProbabilityTheory.nestedRounding K α k`: the rounded values `K / (α * k)` on the first `k`
  hypotheses and `0` on the others, on which e-BH rejects the first `k` hypotheses.
* `ProbabilityTheory.optimalRoundingScheme α x`: the optimal nested scheme.
* `ProbabilityTheory.stochasticRound a b x u`: the stochastic rounding of `x ∈ [a, b]` to `b` or
  `a` at the value `u` of the uniform variable.

## Main statements

* `ProbabilityTheory.IsRoundingScheme.isRoundingFeasible`,
  `ProbabilityTheory.IsRoundingScheme.lintegral_card_eBH_eq`: the law of the rejection set of a
  scheme is a feasible point of the linear program, with the expected number of rejections as
  objective.
* `ProbabilityTheory.IsRoundingScheme.lintegral_card_eBH_le`: no scheme rejects more than `V` on
  average.
* `ProbabilityTheory.isRoundingScheme_optimalRoundingScheme`,
  `ProbabilityTheory.lintegral_card_eBH_optimalRoundingScheme`,
  `ProbabilityTheory.isGreatest_lintegral_card_eBH`,
  `ProbabilityTheory.isGreatest_lintegral_card_eBH_of_antitone_comp`: the largest expected number
  of rejections of a scheme is `V`, attained by the optimal nested scheme [EVR26, Note 30,
  Theorem].
* `ProbabilityTheory.eBH_subset_eBH_div`,
  `ProbabilityTheory.lintegral_card_eBH_le_lintegral_card_eBH_div`: U-eBH dominates every
  comonotone scheme [EVR26, Note 30, Theorem, Statement 4] (U-eBH is not itself one: `x i / U` has
  an infinite mean); the comonotone schemes include the joint stochastic rounding
  (`ProbabilityTheory.lintegral_card_eBH_stochasticRound_le`).
* `ProbabilityTheory.card_eBH_div_eq_ueBHCount`,
  `ProbabilityTheory.lintegral_card_eBH_div_le`: U-eBH rejects `N_U = max {k : U ≤ k y_(k)}`
  hypotheses, hence at most `V` on average [EVR26, Note 30, Theorem, Statement 3].
* `ProbabilityTheory.lintegral_card_eBH_div_example`,
  `ProbabilityTheory.isGreatest_lintegral_card_eBH_example`: U-eBH is not optimal among all
  schemes.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, Note 30, "The
  optimal stochastic rounding for e-BH", github.com/RemyDegenne/evalues_research, 2026.
* [XR23] Z. Xu and A. Ramdas, *More powerful multiple testing under dependence via
  randomization*, arXiv:2305.11126.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {ι : Type*}

/-! ### Rounding schemes and their budgets -/

/-- A **rounding scheme** of the e-values `x` [XR23; EVR26, Note 30]: the law `μ` of rounded
e-values `S`, drawn given the realization `x`, with mean at most `x i` for every hypothesis `i`.
e-BH applied to `S` rejects on average `∫⁻ s, #(eBH s α) ∂μ` hypotheses. -/
structure IsRoundingScheme (x : ι → ℝ≥0∞) (μ : Measure (ι → ℝ≥0∞)) : Prop where
  /-- The rounded e-values have a probability law. -/
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- Each rounded e-value has mean at most the realized one. -/
  lintegral_le (i : ι) : ∫⁻ s, s i ∂μ ≤ x i

/-- Not rounding, the point mass at the realized e-values, is a rounding scheme. -/
theorem isRoundingScheme_dirac (x : ι → ℝ≥0∞) : IsRoundingScheme x (Measure.dirac x) where
  isProbabilityMeasure := inferInstance
  lintegral_le i := by rw [lintegral_dirac' _ (measurable_pi_apply i)]

variable [Fintype ι]

/-- The budgets `y i = α * x i / K` of the linear program of stochastic rounding, as real
numbers. -/
noncomputable def roundingBudget (α : ℝ≥0∞) (x : ι → ℝ≥0∞) (i : ι) : ℝ :=
  (α * x i / Fintype.card ι).toReal

theorem roundingBudget_def (α : ℝ≥0∞) (x : ι → ℝ≥0∞) (i : ι) :
    roundingBudget α x i = (α * x i / Fintype.card ι).toReal :=
  (rfl)

theorem roundingBudget_nonneg (α : ℝ≥0∞) (x : ι → ℝ≥0∞) (i : ι) : 0 ≤ roundingBudget α x i :=
  ENNReal.toReal_nonneg

/-- For a finite level and finite e-values, the budget `α * x i / K` is finite. -/
private lemma budget_ne_top {α : ℝ≥0∞} {x : ι → ℝ≥0∞} (hα : α ≠ ∞) (hx : ∀ i, x i ≠ ∞) (i : ι) :
    α * x i / Fintype.card ι ≠ ∞ :=
  haveI : Nonempty ι := ⟨i⟩
  ENNReal.div_ne_top (ENNReal.mul_ne_top hα (hx i)) (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem ofReal_roundingBudget {α : ℝ≥0∞} {x : ι → ℝ≥0∞} (hα : α ≠ ∞) (hx : ∀ i, x i ≠ ∞)
    (i : ι) : ENNReal.ofReal (roundingBudget α x i) = α * x i / Fintype.card ι :=
  ENNReal.ofReal_toReal (budget_ne_top hα hx i)

/-- Antitone finite e-values have antitone budgets. -/
theorem antitone_roundingBudget [Preorder ι] {α : ℝ≥0∞} {x : ι → ℝ≥0∞} (hα : α ≠ ∞)
    (hx_top : ∀ i, x i ≠ ∞) (hx : Antitone x) : Antitone (roundingBudget α x) :=
  fun _ _ hij ↦ ENNReal.toReal_mono (budget_ne_top hα hx_top _) (by gcongr; exact hx hij)

/-! ### Every rounding scheme is a feasible point of the linear program -/

section Feasible

variable {K : ℕ} {x : Fin K → ℝ≥0∞} {α : ℝ≥0∞} {μ : Measure (Fin K → ℝ≥0∞)}

/-- An expectation of a function of the rejection set of e-BH is a sum over the rejection sets. -/
private lemma lintegral_comp_eBH (g : Finset (Fin K) → ℝ≥0∞) :
    ∫⁻ s, g (eBH s α) ∂μ = ∑ R, g R * μ.map (eBH · α) {R} := by
  rw [← lintegral_map (measurable_of_finite g) (measurable_eBH_id α), lintegral_fintype]

/-- A rejected hypothesis receives `1 / #R` from the rejection set `R` of e-BH, at most
`α * s i / K`. -/
private lemma ite_mem_eBH_inv_le (s : Fin K → ℝ≥0∞) (i : Fin K) :
    (if i ∈ eBH s α then (#(eBH s α) : ℝ≥0∞)⁻¹ else 0) ≤ α * (s i / K) := by
  have h := isSelfConsistent_eBH.fdp_le (e := s) (α := α) {i}
  rw [sum_singleton, Fintype.card_fin, fdp_def] at h
  split_ifs with hi
  · have hpos : (1 : ℝ≥0∞) ≤ #(eBH s α) := Nat.one_le_cast.2 (card_pos.2 ⟨i, hi⟩)
    rwa [inter_singleton_of_mem hi, card_singleton, Nat.cast_one, max_eq_left hpos,
      one_div] at h
  · exact zero_le

/-- **The law of the rejection set of a rounding scheme is feasible** [EVR26, Note 30, proof of
the Theorem]: with `p R` the probability that e-BH applied to the rounded e-values rejects
exactly `R`, `p` is a feasible point of the linear program with the budgets `α * x i / K`. -/
theorem IsRoundingScheme.isRoundingFeasible (hμ : IsRoundingScheme x μ) (hα : α ≠ ∞)
    (hx : ∀ i, x i ≠ ∞) :
    IsRoundingFeasible (roundingBudget α x) fun R ↦ (μ.map (eBH · α)).real {R} := by
  have := hμ.isProbabilityMeasure
  refine ⟨fun R ↦ measureReal_nonneg, ?_, fun i ↦ ?_⟩
  · rw [sum_measureReal_singleton, coe_univ, probReal_univ]
  · -- in `ℝ≥0∞`, the sum is the expectation of `𝟙{i ∈ R} / #R`, at most `α * x i / K`
    have hle : ∑ R, (if i ∈ R then (#R : ℝ≥0∞)⁻¹ else 0) * μ.map (eBH · α) {R} ≤
        α * x i / K := by
      rw [← lintegral_comp_eBH (fun R ↦ if i ∈ R then (#R : ℝ≥0∞)⁻¹ else 0)]
      calc ∫⁻ s, (if i ∈ eBH s α then (#(eBH s α) : ℝ≥0∞)⁻¹ else 0) ∂μ
          ≤ ∫⁻ s, α * (s i / K) ∂μ := lintegral_mono fun s ↦ ite_mem_eBH_inv_le s i
        _ = α * ((∫⁻ s, s i ∂μ) / K) := by
            simp_rw [div_eq_mul_inv]
            rw [lintegral_const_mul _ ((measurable_pi_apply i).mul_const _),
              lintegral_mul_const _ (measurable_pi_apply i)]
        _ ≤ α * (x i / K) := by gcongr; exact hμ.lintegral_le i
        _ = α * x i / K := (mul_div_assoc ..).symm
    have hfin : ∀ R ∈ (univ : Finset (Finset (Fin K))),
        (if i ∈ R then (#R : ℝ≥0∞)⁻¹ else 0) * μ.map (eBH · α) {R} ≠ ∞ := fun R _ ↦ by
      split_ifs with hR
      · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2
          (card_ne_zero_of_mem hR))) (measure_ne_top _ _)
      · simp
    have hK : (K : ℝ≥0∞) = Fintype.card (Fin K) := by rw [Fintype.card_fin]
    rw [sum_filter, roundingBudget_def, ← hK]
    refine le_of_eq_of_le ?_ (ENNReal.toReal_mono (hK ▸ budget_ne_top hα hx i) hle)
    rw [ENNReal.toReal_sum hfin]
    refine sum_congr rfl fun R _ ↦ ?_
    split_ifs
    · rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, measureReal_def]
      ring
    · simp

/-- **The expected number of rejections of a rounding scheme** is the objective of the law of its
rejection set. -/
theorem IsRoundingScheme.lintegral_card_eBH_eq (hμ : IsRoundingScheme x μ) :
    ∫⁻ s, (#(eBH s α) : ℝ≥0∞) ∂μ =
      ENNReal.ofReal (roundingObjective fun R ↦ (μ.map (eBH · α)).real {R}) := by
  have := hμ.isProbabilityMeasure
  rw [lintegral_comp_eBH (fun R ↦ (#R : ℝ≥0∞)), roundingObjective_def,
    ENNReal.ofReal_sum_of_nonneg fun R _ ↦ mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg]
  refine sum_congr rfl fun R _ ↦ ?_
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **No rounding scheme rejects more than `V` on average** [EVR26, Note 30, Theorem]: for a finite
level and finite e-values in any order, the expected number of rejections of e-BH applied to the
rounded e-values is at most the value of the linear program with the budgets `α * x i / K`, taken
in the order of the indices. The bound is attained when the e-values are antitone
(`isGreatest_lintegral_card_eBH`). -/
theorem IsRoundingScheme.lintegral_card_eBH_le (hμ : IsRoundingScheme x μ) (hα : α ≠ ∞)
    (hx : ∀ i, x i ≠ ∞) :
    ∫⁻ s, (#(eBH s α) : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (roundingValue (roundingBudget α x)) := by
  rw [hμ.lintegral_card_eBH_eq]
  exact ENNReal.ofReal_le_ofReal (le_roundingValue fun j _ ↦
    roundingObjective_le_roundingDual (hμ.isRoundingFeasible hα hx) j)

end Feasible

/-! ### The optimal nested scheme -/

section Optimal

variable {K : ℕ} {x : Fin K → ℝ≥0∞} {α : ℝ≥0∞}

/-- The rounded e-values of the nested scheme that rejects the first `k` hypotheses: `K / (α * k)`
on the hypotheses of index less than `k`, and `0` on the others. -/
noncomputable def nestedRounding (K : ℕ) (α : ℝ≥0∞) (k : ℕ) (i : Fin K) : ℝ≥0∞ :=
  if (i : ℕ) < k then K / (α * k) else 0

@[simp]
theorem nestedRounding_of_lt {k : ℕ} {i : Fin K} (hi : (i : ℕ) < k) :
    nestedRounding K α k i = K / (α * k) :=
  ite_eq_left hi

@[simp]
theorem nestedRounding_of_le {k : ℕ} {i : Fin K} (hi : k ≤ (i : ℕ)) :
    nestedRounding K α k i = 0 :=
  ite_eq_right (not_lt.2 hi)

/-- **e-BH applied to the nested rounding rejects the first `k` hypotheses**, for a level
`α ∉ {0, ∞}`. -/
theorem eBH_nestedRounding (hα0 : α ≠ 0) (hα : α ≠ ∞) {k : ℕ} (hk : k ≤ K) :
    eBH (nestedRounding K α k) α = topRanks k := by
  refine Subset.antisymm (fun i hi ↦ ?_)
    (IsSelfConsistent.subset_eBH (isSelfConsistent_iff.2 fun i hi ↦ ?_))
  · by_contra hik
    have h := mem_eBH_iff_le_mul_card.1 hi
    rw [nestedRounding_of_le (not_lt.1 (mt mem_topRanks.2 hik)), mul_zero, Fintype.card_fin] at h
    exact absurd h (not_le.2 (Nat.cast_pos.2 (Fin.pos i)))
  · have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by have := mem_topRanks.1 hi; omega)
    rw [card_topRanks hk, nestedRounding_of_lt (mem_topRanks.1 hi), Fintype.card_fin,
      ENNReal.mul_div_cancel (mul_ne_zero hα0 hk0)
        (ENNReal.mul_ne_top hα (ENNReal.natCast_ne_top k))]

/-- **The optimal nested scheme** [EVR26, Note 30, Theorem]: the law of the nested rounding at a
random count `N` with the optimal law `P(N = k)` of the linear program with the budgets
`α * x i / K`. For antitone e-values, it rejects the `N` hypotheses with the largest e-values. -/
noncomputable def optimalRoundingScheme (α : ℝ≥0∞) (x : Fin K → ℝ≥0∞) :
    Measure (Fin K → ℝ≥0∞) :=
  ∑ k ∈ range (K + 1), ENNReal.ofReal (optimalRoundingLaw (roundingBudget α x) k) •
    Measure.dirac (nestedRounding K α k)

/-- The probability of a set under the optimal nested scheme is a sum over the counts. -/
theorem optimalRoundingScheme_apply (s : Set (Fin K → ℝ≥0∞)) :
    optimalRoundingScheme α x s = ∑ k ∈ range (K + 1),
      ENNReal.ofReal (optimalRoundingLaw (roundingBudget α x) k) *
        s.indicator 1 (nestedRounding K α k) := by
  simp [optimalRoundingScheme]

/-- An expectation under the optimal nested scheme is a sum over the counts. -/
theorem lintegral_optimalRoundingScheme {f : (Fin K → ℝ≥0∞) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ s, f s ∂optimalRoundingScheme α x =
      ∑ k ∈ range (K + 1),
        ENNReal.ofReal (optimalRoundingLaw (roundingBudget α x) k) * f (nestedRounding K α k) := by
  simp_rw [optimalRoundingScheme, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac' _ hf, smul_eq_mul]

/-- **The optimal nested scheme is a rounding scheme** [EVR26, Note 30, Theorem], for antitone
finite e-values and a level `α ∉ {0, ∞}`. -/
theorem isRoundingScheme_optimalRoundingScheme (hx : Antitone x) (hx_top : ∀ i, x i ≠ ∞)
    (hα0 : α ≠ 0) (hα : α ≠ ∞) : IsRoundingScheme x (optimalRoundingScheme α x) := by
  have hy := antitone_roundingBudget hα hx_top hx
  have hy0 := roundingBudget_nonneg α x
  have hq := optimalRoundingLaw_nonneg hy hy0
  refine ⟨⟨?_⟩, fun i ↦ ?_⟩
  · rw [← lintegral_one, lintegral_optimalRoundingScheme measurable_const]
    simp_rw [mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ hq k, sum_optimalRoundingLaw, ENNReal.ofReal_one]
  · -- the mean of the rounded value of `i` is `(K / α) * ∑_{i < k ≤ K} P(N = k) / k`
    have hKα : (K : ℝ≥0∞) / α ≠ ∞ := ENNReal.div_ne_top (ENNReal.natCast_ne_top K) hα0
    have hterm : ∀ k ∈ range (K + 1),
        ENNReal.ofReal (optimalRoundingLaw (roundingBudget α x) k) * nestedRounding K α k i =
          if (i : ℕ) < k then
            ENNReal.ofReal (optimalRoundingLaw (roundingBudget α x) k / k) * (K / α) else 0 := by
      intro k _
      split_ifs with hik
      · have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
        rw [nestedRounding_of_lt hik, ENNReal.ofReal_div_of_pos hk0, ENNReal.ofReal_natCast,
          ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hα0) (Or.inl hα)]
        simp only [div_eq_mul_inv]
        ring
      · rw [nestedRounding_of_le (not_lt.1 hik), mul_zero]
    have hsum : ∑ k ∈ range (K + 1), (if (i : ℕ) < k then
          ENNReal.ofReal (optimalRoundingLaw (roundingBudget α x) k / k) * (K / α) else 0) =
        ENNReal.ofReal (∑ k ∈ Ioc (i : ℕ) K, optimalRoundingLaw (roundingBudget α x) k / k) *
          (K / α) := by
      rw [← sum_filter, ← sum_mul, ENNReal.ofReal_sum_of_nonneg fun k _ ↦
        div_nonneg (hq k) (Nat.cast_nonneg k)]
      congr 2
      ext k
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    rw [lintegral_optimalRoundingScheme (measurable_pi_apply i), sum_congr rfl hterm, hsum]
    calc ENNReal.ofReal (∑ k ∈ Ioc (i : ℕ) K, optimalRoundingLaw (roundingBudget α x) k / k) *
          (K / α)
        ≤ ENNReal.ofReal (roundingBudget α x i) * (K / α) := by
          gcongr
          exact sum_Ioc_optimalRoundingLaw_div_le hy hy0 i
      _ = x i * (α * α⁻¹) * ((K : ℝ≥0∞)⁻¹ * K) := by
          rw [ofReal_roundingBudget hα hx_top, Fintype.card_fin, div_eq_mul_inv, div_eq_mul_inv]
          ring
      _ = x i := by
          rw [ENNReal.mul_inv_cancel hα0 hα, ENNReal.inv_mul_cancel
            (Nat.cast_ne_zero.2 (Fin.pos i).ne') (ENNReal.natCast_ne_top K), mul_one, mul_one]

/-- **The optimal nested scheme attains `V`** [EVR26, Note 30, Theorem]: for antitone finite
e-values and a level `α ∉ {0, ∞}`, e-BH applied to it rejects on average the value of the linear
program with the budgets `α * x i / K`. -/
theorem lintegral_card_eBH_optimalRoundingScheme (hx : Antitone x) (hx_top : ∀ i, x i ≠ ∞)
    (hα0 : α ≠ 0) (hα : α ≠ ∞) :
    ∫⁻ s, (#(eBH s α) : ℝ≥0∞) ∂optimalRoundingScheme α x =
      ENNReal.ofReal (roundingValue (roundingBudget α x)) := by
  have hy := antitone_roundingBudget hα hx_top hx
  have hq := optimalRoundingLaw_nonneg hy (roundingBudget_nonneg α x)
  rw [lintegral_optimalRoundingScheme (measurable_card_eBH α),
    ← roundingObjective_nestedPoint_optimalRoundingLaw hy (roundingBudget_nonneg α x),
    roundingObjective_nestedPoint,
    ENNReal.ofReal_sum_of_nonneg fun k _ ↦ mul_nonneg (Nat.cast_nonneg k) (hq k)]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [eBH_nestedRounding hα0 hα (Nat.lt_succ_iff.1 (mem_range.1 hk)),
    card_topRanks (Nat.lt_succ_iff.1 (mem_range.1 hk)), ENNReal.ofReal_mul (Nat.cast_nonneg k),
    ENNReal.ofReal_natCast, mul_comm]

/-- At level `0`, the value of the linear program is `0`: every budget vanishes. -/
private lemma roundingValue_roundingBudget_zero (x : Fin K → ℝ≥0∞) :
    roundingValue (roundingBudget 0 x) ≤ 0 := by
  have hb (k : ℕ) : rankBudget (roundingBudget 0 x) k = 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact rankBudget_eq_zero _ (Or.inl rfl)
    rcases le_or_gt k K with hkK | hkK
    · rw [rankBudget_of_pos_of_le _ hk hkK, roundingBudget_def, zero_mul, ENNReal.zero_div,
        ENNReal.toReal_zero]
    · exact rankBudget_eq_zero _ (Or.inr hkK)
  refine (roundingValue_le_roundingDual _ (Nat.zero_le K)).trans_eq ?_
  simp [roundingDual_def, hb]

/-- **The optimal rounding of e-values for e-BH** [EVR26, Note 30, Theorem]: for antitone finite
e-values and a finite level `α`, the largest expected number of rejections of e-BH applied to a
rounding of the e-values is the value `V` of the linear program with the budgets `α * x i / K`,
attained by the optimal nested scheme. -/
theorem isGreatest_lintegral_card_eBH (hx : Antitone x) (hx_top : ∀ i, x i ≠ ∞) (hα : α ≠ ∞) :
    IsGreatest {v | ∃ μ, IsRoundingScheme x μ ∧ ∫⁻ s, (#(eBH s α) : ℝ≥0∞) ∂μ = v}
      (ENNReal.ofReal (roundingValue (roundingBudget α x))) := by
  refine ⟨?_, fun _ ⟨_, hμ, hv⟩ ↦ hv ▸ hμ.lintegral_card_eBH_le hα hx_top⟩
  rcases eq_or_ne α 0 with rfl | hα0
  · -- at level `0`, not rounding attains the value `0`
    refine ⟨_, isRoundingScheme_dirac x, ?_⟩
    simp [ENNReal.ofReal_eq_zero.2 (roundingValue_roundingBudget_zero x)]
  · exact ⟨_, isRoundingScheme_optimalRoundingScheme hx hx_top hα0 hα,
      lintegral_card_eBH_optimalRoundingScheme hx hx_top hα0 hα⟩

/-- Relabelling the hypotheses by a permutation `σ` maps a rounding scheme of `x` to one of
`x ∘ σ`. -/
theorem IsRoundingScheme.map_comp_perm {μ : Measure (Fin K → ℝ≥0∞)} (hμ : IsRoundingScheme x μ)
    (σ : Equiv.Perm (Fin K)) : IsRoundingScheme (x ∘ σ) (μ.map (· ∘ σ)) := by
  have hσ : Measurable fun s : Fin K → ℝ≥0∞ ↦ s ∘ σ :=
    measurable_pi_iff.2 fun i ↦ measurable_pi_apply (σ i)
  have := hμ.isProbabilityMeasure
  refine ⟨inferInstance, fun i ↦ ?_⟩
  rw [lintegral_map (measurable_pi_apply i) hσ]
  exact hμ.lintegral_le (σ i)

/-- Relabelling the rounded e-values by a permutation does not change the expected number of
rejections of e-BH. -/
theorem lintegral_card_eBH_map_comp_perm (μ : Measure (Fin K → ℝ≥0∞)) (σ : Equiv.Perm (Fin K)) :
    ∫⁻ s, (#(eBH s α) : ℝ≥0∞) ∂μ.map (· ∘ σ) = ∫⁻ s, (#(eBH s α) : ℝ≥0∞) ∂μ := by
  rw [lintegral_map (measurable_card_eBH α) (measurable_pi_iff.2 fun i ↦ measurable_pi_apply (σ i))]
  simp_rw [card_eBH_comp_equiv]

/-- **The optimal rounding of e-values in any order** [EVR26, Note 30, Theorem]: for finite
e-values, a finite level `α` and a permutation `σ` that sorts the e-values in nonincreasing
order, the largest expected number of rejections of e-BH applied to a rounding of the e-values is
the value `V` of the linear program with the sorted budgets. -/
theorem isGreatest_lintegral_card_eBH_of_antitone_comp (σ : Equiv.Perm (Fin K))
    (hx : Antitone (x ∘ σ)) (hx_top : ∀ i, x i ≠ ∞) (hα : α ≠ ∞) :
    IsGreatest {v | ∃ μ, IsRoundingScheme x μ ∧ ∫⁻ s, (#(eBH s α) : ℝ≥0∞) ∂μ = v}
      (ENNReal.ofReal (roundingValue (roundingBudget α (x ∘ σ)))) := by
  convert isGreatest_lintegral_card_eBH hx (fun i ↦ hx_top (σ i)) hα using 1
  ext v
  refine ⟨fun ⟨μ, hμ, hv⟩ ↦
      ⟨_, hμ.map_comp_perm σ, (lintegral_card_eBH_map_comp_perm μ σ).trans hv⟩,
    fun ⟨μ, hμ, hv⟩ ↦ ⟨_, ?_, (lintegral_card_eBH_map_comp_perm μ σ.symm).trans hv⟩⟩
  have h := hμ.map_comp_perm σ.symm
  rwa [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] at h

end Optimal

/-! ### U-eBH and the comonotone schemes -/

section Comonotone

variable {x : ι → ℝ≥0∞} {α : ℝ≥0∞}

/-- **U-eBH dominates every comonotone scheme pointwise** [EVR26, Note 30, Theorem, Statement 4]:
if the rounded e-values `f i u` are nonincreasing functions of one uniform variable `u ∈ [0, 1]`
with means at most `x i`, then at every `u ∈ (0, 1]` e-BH applied to them rejects a subset of what
U-eBH, e-BH applied to `x i / u`, rejects. -/
theorem eBH_subset_eBH_div {f : ι → ℝ → ℝ≥0∞} (hf : ∀ i, AntitoneOn (f i) (Set.Icc 0 1))
    (hfx : ∀ i, ∫⁻ u in Set.Icc 0 1, f i u ≤ x i) {u : ℝ} (hu : u ∈ Set.Ioc 0 1) (α : ℝ≥0∞) :
    eBH (f · u) α ⊆ eBH (fun i ↦ x i / ENNReal.ofReal u) α :=
  eBH_mono le_rfl fun i ↦ by
    -- Markov's inequality: `u * f i u ≤ ∫⁻ f i ≤ x i`
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hu.1).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    have h := (hf i).ofReal_sub_mul_le_setLIntegral_Icc ⟨hu.1.le, hu.2⟩
    rw [sub_zero] at h
    exact h.trans (hfx i)

/-- **U-eBH dominates every comonotone scheme** [EVR26, Note 30, Theorem, Statement 4]: e-BH
applied to rounded e-values that are nonincreasing functions of one uniform variable, with means at
most `x i`, rejects on average at most as many hypotheses as U-eBH. U-eBH is not itself a
comonotone scheme: `x i / U` has an infinite mean. -/
theorem lintegral_card_eBH_le_lintegral_card_eBH_div {f : ι → ℝ → ℝ≥0∞}
    (hf : ∀ i, AntitoneOn (f i) (Set.Icc 0 1)) (hfx : ∀ i, ∫⁻ u in Set.Icc 0 1, f i u ≤ x i)
    (α : ℝ≥0∞) :
    ∫⁻ u in Set.Icc 0 1, (#(eBH (f · u) α) : ℝ≥0∞) ≤
      ∫⁻ u in Set.Icc 0 1, (#(eBH (fun i ↦ x i / ENNReal.ofReal u) α) : ℝ≥0∞) := by
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  refine setLIntegral_mono' measurableSet_Ioc fun u hu ↦ ?_
  exact_mod_cast card_le_card (eBH_subset_eBH_div hf hfx hu α)

/-- The **stochastic rounding** of `x ∈ [a, b]` to the grid points `a` and `b`, at the value `u`
of a uniform variable on `[0, 1]` [XR23]: `b` when `u * (b - a) ≤ x - a`, that is with probability
`(x - a) / (b - a)`, and `a` otherwise. The joint stochastic rounding of [XR23] rounds every
e-value with the same `u`. -/
noncomputable def stochasticRound (a b x : ℝ≥0∞) (u : ℝ) : ℝ≥0∞ :=
  if ENNReal.ofReal u * (b - a) ≤ x - a then b else a

theorem stochasticRound_def (a b x : ℝ≥0∞) (u : ℝ) :
    stochasticRound a b x u = if ENNReal.ofReal u * (b - a) ≤ x - a then b else a :=
  (rfl)

/-- The stochastic rounding is `b` when `u * (b - a) ≤ x - a`. -/
theorem stochasticRound_of_le {a b x : ℝ≥0∞} {u : ℝ} (h : ENNReal.ofReal u * (b - a) ≤ x - a) :
    stochasticRound a b x u = b :=
  ite_eq_left h

/-- The stochastic rounding is `a` when `x - a < u * (b - a)`. -/
theorem stochasticRound_of_lt {a b x : ℝ≥0∞} {u : ℝ} (h : x - a < ENNReal.ofReal u * (b - a)) :
    stochasticRound a b x u = a :=
  ite_eq_right (not_le.2 h)

/-- The stochastic rounding is nonincreasing in the uniform variable. -/
theorem antitone_stochasticRound {a b : ℝ≥0∞} (hab : a ≤ b) (x : ℝ≥0∞) :
    Antitone (stochasticRound a b x) := by
  intro u v huv
  by_cases hv : ENNReal.ofReal v * (b - a) ≤ x - a
  · rw [stochasticRound_of_le hv,
      stochasticRound_of_le ((mul_le_mul_left (ENNReal.ofReal_le_ofReal huv) _).trans hv)]
  · rw [stochasticRound_of_lt (not_le.1 hv)]
    by_cases hu : ENNReal.ofReal u * (b - a) ≤ x - a
    · rw [stochasticRound_of_le hu]
      exact hab
    · rw [stochasticRound_of_lt (not_le.1 hu)]

/-- The stochastic rounding of `x ∈ [a, b]`, with `b` finite, has mean `x`. -/
theorem setLIntegral_stochasticRound {a b x : ℝ≥0∞} (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≠ ∞) :
    ∫⁻ u in Set.Icc 0 1, stochasticRound a b x u = x := by
  have ha : a ≠ ∞ := ne_top_of_le_ne_top hb (hax.trans hxb)
  rcases eq_or_lt_of_le (hax.trans hxb) with hab | hab
  · -- `a = b`: the rounding is constant
    subst hab
    have hx : x = a := le_antisymm hxb hax
    subst hx
    simp [stochasticRound_def, Real.volume_Icc]
  · -- the rounding is `a + (b - a) * 𝟙{u ≤ θ}` with `θ = (x - a) / (b - a) ∈ [0, 1]`
    have hba0 : b - a ≠ 0 := (tsub_pos_of_lt hab).ne'
    have hba : b - a ≠ ∞ := ENNReal.sub_ne_top hb
    set θ := (x - a) / (b - a) with hθ
    have hθ1 : θ ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact tsub_le_tsub_right hxb a)
    have hθtop : θ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hθ1
    have hcond (u : ℝ) : ENNReal.ofReal u * (b - a) ≤ x - a ↔ u ≤ θ.toReal := by
      rw [← ENNReal.le_div_iff_mul_le (Or.inl hba0) (Or.inl hba), ← hθ,
        ENNReal.ofReal_le_iff_le_toReal hθtop]
    have hfun : (fun u ↦ stochasticRound a b x u) =
        fun u ↦ a + Set.indicator (Set.Iic θ.toReal) (fun _ ↦ b - a) u := by
      ext u
      by_cases hu : u ≤ θ.toReal
      · rw [stochasticRound_of_le ((hcond u).2 hu), Set.indicator_of_mem (Set.mem_Iic.2 hu),
          add_tsub_cancel_of_le hab.le]
      · rw [stochasticRound_of_lt (not_le.1 (mt (hcond u).1 hu)),
          Set.indicator_of_notMem (by simpa using hu), add_zero]
    have hθr1 : θ.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hθ1)
    have hset : Set.Iic θ.toReal ∩ Set.Icc 0 1 = Set.Icc 0 θ.toReal := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans hθr1⟩⟩
    -- the constant `a` integrates to `a`, and the indicator to `(b - a) * θ = x - a`
    have hconst : ∫⁻ _ in Set.Icc (0 : ℝ) 1, a = a := by simp [Real.volume_Icc]
    have hind : ∫⁻ u in Set.Icc (0 : ℝ) 1, Set.indicator (Set.Iic θ.toReal) (fun _ ↦ b - a) u =
        (b - a) * θ := by
      rw [lintegral_indicator_const measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
        hset]
      simp [Real.volume_Icc, ENNReal.ofReal_toReal hθtop]
    have hmul : (b - a) * θ = x - a := ENNReal.mul_div_cancel hba0 hba
    rw [hfun, lintegral_add_left measurable_const, hconst, hind, hmul, add_tsub_cancel_of_le hax]

/-- **U-eBH dominates the joint stochastic rounding** [EVR26, Note 30, Theorem, Statement 4]: for
grid points `a i ≤ x i ≤ b i` with `b i` finite, e-BH applied to the stochastic roundings of all
the e-values with one common uniform variable rejects on average at most as many hypotheses as
U-eBH. -/
theorem lintegral_card_eBH_stochasticRound_le {a b : ι → ℝ≥0∞} (hax : a ≤ x) (hxb : x ≤ b)
    (hb : ∀ i, b i ≠ ∞) (α : ℝ≥0∞) :
    ∫⁻ u in Set.Icc 0 1, (#(eBH (fun i ↦ stochasticRound (a i) (b i) (x i) u) α) : ℝ≥0∞) ≤
      ∫⁻ u in Set.Icc 0 1, (#(eBH (fun i ↦ x i / ENNReal.ofReal u) α) : ℝ≥0∞) :=
  lintegral_card_eBH_le_lintegral_card_eBH_div
    (fun i ↦ (antitone_stochasticRound ((hax i).trans (hxb i)) (x i)).antitoneOn _)
    (fun i ↦ (setLIntegral_stochasticRound (hax i) (hxb i) (hb i)).le) α

end Comonotone

/-! ### The number of rejections of U-eBH -/

section UeBH

variable {K : ℕ} {x : Fin K → ℝ≥0∞} {α : ℝ≥0∞}

/-- The threshold of U-eBH: `K ≤ α * k * (x j / u)` exactly when `u ≤ k * y j`, for the budget
`y j = α * x j / K`. -/
private lemma le_mul_div_ofReal_iff (hx_top : ∀ i, x i ≠ ∞) (hα : α ≠ ∞) {u : ℝ} (hu : 0 < u)
    (k : ℕ) (j : Fin K) :
    (K : ℝ≥0∞) ≤ α * k * (x j / ENNReal.ofReal u) ↔ u ≤ k * roundingBudget α x j := by
  have hK : (0 : ℝ) < K := by exact_mod_cast Fin.pos j
  have hu' : ENNReal.ofReal u ≠ 0 := (ENNReal.ofReal_pos.2 hu).ne'
  have hfin : α * k * x j ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hα (ENNReal.natCast_ne_top k)) (hx_top j)
  -- in `ℝ≥0∞`, the threshold reads `K * u ≤ α * k * x j`, between finite numbers
  rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hu') (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (ENNReal.natCast_ne_top K)
      ENNReal.ofReal_ne_top) hfin]
  -- in `ℝ`, `K * u ≤ α * k * x j` is `u ≤ k * (α * x j / K)`
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hu.le,
    roundingBudget_def, Fintype.card_fin, ENNReal.toReal_div]
  rw [mul_div_assoc', le_div_iff₀ hK]
  constructor <;> intro h <;> linarith

/-- **The number of rejections of U-eBH** [EVR26, Note 30, Theorem, Statement 3]: for antitone
finite e-values, a finite level and `u > 0`, e-BH applied to `x i / u` rejects
`N_U = max {k : u ≤ k y_(k)}` hypotheses, with the budgets `y i = α * x i / K`. -/
theorem card_eBH_div_eq_ueBHCount (hx : Antitone x) (hx_top : ∀ i, x i ≠ ∞) (hα : α ≠ ∞)
    {u : ℝ} (hu : 0 < u) :
    #(eBH (fun i ↦ x i / ENNReal.ofReal u) α) = ueBHCount (roundingBudget α x) u := by
  have hy := antitone_roundingBudget hα hx_top hx
  -- for `1 ≤ k ≤ K`, at least `k` e-values pass the threshold of `k` iff `u ≤ k y_(k)`
  have key : ∀ k, 0 < k → k ≤ K →
      (k ≤ #{j | (Fintype.card (Fin K) : ℝ≥0∞) ≤ α * k * (x j / ENNReal.ofReal u)} ↔
        u ≤ k * rankBudget (roundingBudget α x) k) := by
    intro k hk0 hkK
    have hk : (0 : ℝ) < k := by exact_mod_cast hk0
    simp_rw [Fintype.card_fin, le_mul_div_ofReal_iff hx_top hα hu, ← div_le_iff₀' hk]
    rw [hy.le_card_filter_le_iff hk0 hkK, rankBudget_of_pos_of_le _ hk0 hkK, div_le_iff₀' hk]
  rw [card_eBH]
  refine le_antisymm ?_ ?_
  · set n := Nat.findGreatest (fun k ↦ k ≤ #{j | (Fintype.card (Fin K) : ℝ≥0∞) ≤
      α * k * (x j / ENNReal.ofReal u)}) (Fintype.card (Fin K))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]
      exact Nat.zero_le _
    have hnK : n ≤ K := (Nat.findGreatest_le _).trans_eq (Fintype.card_fin K)
    exact (le_ueBHCount_iff hn).2 ⟨n, le_rfl, hnK, (key n hn hnK).1 (Nat.findGreatest_spec
      (P := fun k ↦ k ≤ #{j | (Fintype.card (Fin K) : ℝ≥0∞) ≤
        α * k * (x j / ENNReal.ofReal u)}) (Nat.zero_le _) (Nat.zero_le _))⟩
  · rcases Nat.eq_zero_or_pos (ueBHCount (roundingBudget α x) u) with hN | hN
    · rw [hN]
      exact Nat.zero_le _
    obtain ⟨l, hNl, hlK, hl⟩ := (le_ueBHCount_iff hN).1 le_rfl
    exact hNl.trans (Nat.le_findGreatest (hlK.trans_eq (Fintype.card_fin K).symm)
      ((key l (by omega) hlK).2 hl))

/-- The expected number of rejections of U-eBH is the mean of `N_U`. -/
theorem lintegral_card_eBH_div_eq (hx : Antitone x) (hx_top : ∀ i, x i ≠ ∞) (hα : α ≠ ∞) :
    ∫⁻ u in Set.Icc 0 1, (#(eBH (fun i ↦ x i / ENNReal.ofReal u) α) : ℝ≥0∞) =
      ENNReal.ofReal (∫ u in Set.Icc (0 : ℝ) 1, (ueBHCount (roundingBudget α x) u : ℝ)) := by
  have hmeas : Measurable fun u ↦ (ueBHCount (roundingBudget α x) u : ℝ) :=
    measurable_from_nat.comp (measurable_ueBHCount _)
  rw [ofReal_integral_eq_lintegral_ofReal, ← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  · refine setLIntegral_congr_fun measurableSet_Ioc fun u hu ↦ ?_
    rw [card_eBH_div_eq_ueBHCount hx hx_top hα hu.1, ENNReal.ofReal_natCast]
  · refine Integrable.of_bound hmeas.aestronglyMeasurable K (ae_of_all _ fun u ↦ ?_)
    rw [Real.norm_natCast]
    exact_mod_cast ueBHCount_le _ u
  · exact ae_of_all _ fun u ↦ Nat.cast_nonneg _

/-- **U-eBH rejects at most `V` on average** [EVR26, Note 30, Theorem, Statement 3]: for antitone
finite e-values and a finite level, the expected number of rejections of e-BH applied to `x i / U`,
for `U` uniform on `[0, 1]`, is at most the value of the linear program with the budgets
`α * x i / K`, although `x i / U` has an infinite mean. -/
theorem lintegral_card_eBH_div_le (hx : Antitone x) (hx_top : ∀ i, x i ≠ ∞) (hα : α ≠ ∞) :
    ∫⁻ u in Set.Icc 0 1, (#(eBH (fun i ↦ x i / ENNReal.ofReal u) α) : ℝ≥0∞) ≤
      ENNReal.ofReal (roundingValue (roundingBudget α x)) := by
  rw [lintegral_card_eBH_div_eq hx hx_top hα]
  exact ENNReal.ofReal_le_ofReal (integral_ueBHCount_le_roundingValue
    (antitone_roundingBudget hα hx_top hx) (roundingBudget_nonneg α x))

end UeBH

/-! ### U-eBH is not optimal among all schemes -/

/-- The budgets `(2/5, 1/10)` are antitone. -/
private lemma antitone_budget_example : Antitone ![(2 / 5 : ℝ), 1 / 10] := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The budgets `(2/5, 1/10)` are nonnegative. -/
private lemma nonneg_budget_example : ∀ i, 0 ≤ ![(2 / 5 : ℝ), 1 / 10] i := by
  intro i
  fin_cases i <;> norm_num

/-- For `K = 2` and `y = (2/5, 1/10)`, the value of the linear program is `7/10`. -/
private lemma roundingValue_example : roundingValue ![(2 / 5 : ℝ), 1 / 10] = 7 / 10 := by
  have h := isGreatest_roundingObjective_of_sum_le_one antitone_budget_example nonneg_budget_example
    (by norm_num [Fin.sum_univ_two])
  refine (h.unique (isGreatest_roundingObjective antitone_budget_example
    nonneg_budget_example)).symm.trans ?_
  norm_num [Fin.sum_univ_two]

/-- For `K = 2` and `y = (2/5, 1/10)`, U-eBH rejects `3/5` hypotheses on average. -/
private lemma integral_ueBHCount_example :
    ∫ u in Set.Icc (0 : ℝ) 1, (ueBHCount ![(2 / 5 : ℝ), 1 / 10] u : ℝ) = 3 / 5 := by
  set y : Fin 2 → ℝ := ![(2 / 5 : ℝ), 1 / 10]
  have hb1 : rankBudget y 1 = 2 / 5 := by simpa [y] using rankBudget_succ y 0
  have hb2 : rankBudget y 2 = 1 / 10 := by simpa [y] using rankBudget_succ y 1
  -- the count of U-eBH: `2` on `[0, 1/5]`, `1` on `(1/5, 2/5]`, `0` above
  have hN : ∀ u, ueBHCount y u = if u ≤ 1 / 5 then 2 else if u ≤ 2 / 5 then 1 else 0 := by
    intro u
    have hle := ueBHCount_le y u
    have h2 : 2 ≤ ueBHCount y u ↔ u ≤ 1 / 5 := by
      rw [le_ueBHCount_iff (by norm_num)]
      constructor
      · rintro ⟨l, h2l, hl2, hu⟩
        obtain rfl : l = 2 := by omega
        rw [hb2] at hu
        push_cast at hu
        linarith
      · intro hu
        exact ⟨2, le_rfl, le_rfl, by rw [hb2]; push_cast; linarith⟩
    have h1 : 1 ≤ ueBHCount y u ↔ u ≤ 2 / 5 := by
      rw [le_ueBHCount_iff (by norm_num)]
      constructor
      · rintro ⟨l, h1l, hl2, hu⟩
        interval_cases l
        · rw [hb1] at hu
          push_cast at hu
          linarith
        · rw [hb2] at hu
          push_cast at hu
          linarith
      · intro hu
        exact ⟨1, le_rfl, by norm_num, by rw [hb1]; push_cast; linarith⟩
    split_ifs with ha hb
    · have := h2.2 ha
      omega
    · have := h1.2 hb
      have := mt h2.1 ha
      omega
    · have := mt h1.1 hb
      omega
  -- the law of the count: `1/5` at `1` (on `(1/5, 2/5]`) and `1/5` at `2` (on `[0, 1/5]`)
  have hL1 : ueBHLaw y 1 = 1 / 5 := by
    rw [ueBHLaw_def, show {u ∈ Set.Icc (0 : ℝ) 1 | ueBHCount y u = 1} = Set.Ioc (1 / 5) (2 / 5)
      by ext u; simp only [Set.mem_ofPred_eq, hN u, Set.mem_Icc, Set.mem_Ioc]; split_ifs <;> grind,
      Real.volume_real_Ioc_of_le (by norm_num)]
    norm_num
  have hL2 : ueBHLaw y 2 = 1 / 5 := by
    rw [ueBHLaw_def, show {u ∈ Set.Icc (0 : ℝ) 1 | ueBHCount y u = 2} = Set.Icc 0 (1 / 5)
      by ext u; simp only [Set.mem_ofPred_eq, hN u, Set.mem_Icc]; split_ifs <;> grind,
      Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  rw [integral_ueBHCount_eq, roundingObjective_nestedPoint]
  simp only [sum_range_succ, sum_range_zero, hL1, hL2]
  norm_num

/-- The budgets of the e-values `(8, 2)` at level `1/10` are `(2/5, 1/10)`. -/
private lemma roundingBudget_example :
    roundingBudget (10⁻¹ : ℝ≥0∞) ![(8 : ℝ≥0∞), 2] = ![(2 / 5 : ℝ), 1 / 10] := by
  ext i
  fin_cases i <;> norm_num [roundingBudget_def, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

private lemma antitone_example : Antitone ![(8 : ℝ≥0∞), 2] := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num

private lemma ne_top_example : ∀ i, ![(8 : ℝ≥0∞), 2] i ≠ ∞ := by
  intro i
  fin_cases i <;> simp

/-- **U-eBH in the example** [EVR26, Note 30, Theorem, Statement 3]: for the e-values `(8, 2)` at
level `1/10`, U-eBH rejects `3/5` hypotheses on average, less than the `7/10` of the optimal
rounding scheme (`isGreatest_lintegral_card_eBH_example`). -/
theorem lintegral_card_eBH_div_example :
    ∫⁻ u in Set.Icc 0 1,
        (#(eBH (fun i ↦ ![(8 : ℝ≥0∞), 2] i / ENNReal.ofReal u) 10⁻¹) : ℝ≥0∞) =
      ENNReal.ofReal (3 / 5) := by
  rw [lintegral_card_eBH_div_eq antitone_example ne_top_example (by simp), roundingBudget_example,
    integral_ueBHCount_example]

/-- **The optimal rounding in the example** [EVR26, Note 30, Theorem, Statement 3]: for the
e-values `(8, 2)` at level `1/10`, the largest expected number of rejections of a rounding scheme
is `7/10`, more than the `3/5` of U-eBH (`lintegral_card_eBH_div_example`). -/
theorem isGreatest_lintegral_card_eBH_example :
    IsGreatest {v | ∃ μ, IsRoundingScheme ![(8 : ℝ≥0∞), 2] μ ∧
        ∫⁻ s, (#(eBH s 10⁻¹) : ℝ≥0∞) ∂μ = v} (ENNReal.ofReal (7 / 10)) := by
  have h := isGreatest_lintegral_card_eBH (α := 10⁻¹) antitone_example ne_top_example (by simp)
  rwa [roundingBudget_example, roundingValue_example] at h

end ProbabilityTheory
