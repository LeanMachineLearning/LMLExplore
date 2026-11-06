/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-Gaussianity of bounded variables

By Hoeffding's lemma `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, a random variable with
values in `[a, b]` is `((b - a) / 2) ^ 2`-sub-Gaussian around its mean. We record the case
`[0, 1]`, with the constant `1 / 4`, which is the form used by the bandit algorithms for rewards
in `[0, 1]`.

Hoeffding's inequality for sums of independent sub-Gaussian variables
(`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`), applied to the variables
and to their negatives, gives its two-sided form: for independent `c i`-sub-Gaussian variables
`X i`, `i ∈ s`, and `t ≥ 0`, `P(t ≤ |∑ i ∈ s, X i|) ≤ 2 exp (-t² / (2 ∑ i ∈ s, c i))`. With
Hoeffding's lemma, it gives the two-sided Hoeffding inequality for bounded variables: for
independent variables `X i ∈ [l i, u i]`, `i ∈ s`, and `t ≥ 0`,
`P(t ≤ |∑ i ∈ s, (X i - E[X i])|) ≤ 2 exp (-2 t² / ∑ i ∈ s, (u i - l i)²)`.

## Main statements

* `LMLExplore.hasSubgaussianMGF_of_mem_Icc_zero_one`: a random variable with values in `[0, 1]`
  is `1 / 4`-sub-Gaussian around its mean.
* `LMLExplore.measureReal_le_abs_sum_le_of_iIndepFun`: the two-sided Hoeffding inequality for
  independent sub-Gaussian variables.
* `LMLExplore.measureReal_le_abs_sum_sub_integral_le`: the two-sided Hoeffding inequality for
  independent bounded variables.
-/

public section

open MeasureTheory ProbabilityTheory Finset
open Real (exp)
open scoped NNReal

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ}

/-- **Hoeffding's lemma on `[0, 1]`**: a random variable with values in `[0, 1]` is
`1 / 4`-sub-Gaussian around its mean. -/
lemma hasSubgaussianMGF_of_mem_Icc_zero_one (hm : AEMeasurable X μ)
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) (1 / 4) μ := by
  have hσ : (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 = 1 / 4 := by
    ext
    norm_num
  exact hσ ▸ hasSubgaussianMGF_of_mem_Icc hm hb

/-- **Hoeffding's inequality** for sub-Gaussian variables, two-sided: if the `X i`, `i ∈ s`, are
independent and `c i`-sub-Gaussian, then for `t ≥ 0`,
`P(t ≤ |∑ i ∈ s, X i|) ≤ 2 exp (-t² / (2 ∑ i ∈ s, c i))`. -/
theorem measureReal_le_abs_sum_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {c : ι → ℝ≥0} {s : Finset ι}
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤ 2 * exp (-t ^ 2 / (2 * ∑ i ∈ s, c i)) := by
  -- the upper tail of the `X i` and the upper tail of their negatives
  have h_upper := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep h_subG ht
  have h_lower := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (h_indep.comp (g := fun _ (y : ℝ) ↦ -y) fun _ ↦ measurable_neg)
    (fun i hi ↦ (h_subG i hi).neg) ht
  -- a union bound over the two tails
  refine le_trans (measureReal_mono ?_) ((measureReal_union_le _ _).trans
    ((add_le_add h_upper h_lower).trans_eq (two_mul _).symm))
  intro ω (hω : t ≤ _)
  rcases le_abs.1 hω with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [Function.comp_def, sum_neg_distrib] using h)

/-- **Hoeffding's inequality**, two-sided: if the `X i`, `i ∈ s`, are independent with values in
`[l i, u i]`, then for `t ≥ 0` their centered sum satisfies
`P(t ≤ |∑ i ∈ s, (X i - E[X i])|) ≤ 2 exp (-2 t² / ∑ i ∈ s, (u i - l i)²)`. -/
theorem measureReal_le_abs_sum_sub_integral_le {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    {l u : ι → ℝ} (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (l i) (u i)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ s, (X i ω - μ[X i])|} ≤
      2 * exp (-(2 * t ^ 2 / ∑ i ∈ s, (u i - l i) ^ 2)) := by
  -- the centered variables are independent and `((u i - l i) / 2) ^ 2`-sub-Gaussian, by
  -- Hoeffding's lemma
  have h := measureReal_le_abs_sum_le_of_iIndepFun
    (h_indep.comp (g := fun i (y : ℝ) ↦ y - ∫ ω, X i ω ∂μ) fun _ ↦ measurable_sub_const _)
    (fun i hi ↦ hasSubgaussianMGF_of_mem_Icc (hXm i hi) (hX i hi)) ht
  refine h.trans_eq ?_
  congr 2
  push_cast
  simp only [Real.norm_eq_abs, div_pow, sq_abs, ← sum_div]
  ring

end LMLExplore
