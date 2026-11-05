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

Together with Hoeffding's inequality for sums of independent sub-Gaussian variables
(`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`), applied to the centered
variables and to their negatives, it gives the two-sided Hoeffding inequality: for independent
variables `X i ∈ [l, u]`, `i ∈ s`, and `t ≥ 0`,
`P(t ≤ |∑ i ∈ s, (X i - E[X i])|) ≤ 2 exp (-2 t² / (#s (u - l)²))`.

## Main statements

* `LMLExplore.hasSubgaussianMGF_of_mem_Icc_zero_one`: a random variable with values in `[0, 1]`
  is `1 / 4`-sub-Gaussian around its mean.
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

/-- **Hoeffding's inequality**, two-sided: if the `X i`, `i ∈ s`, are independent with values in
`[l, u]`, then for `t ≥ 0` their centered sum satisfies
`P(t ≤ |∑ i ∈ s, (X i - E[X i])|) ≤ 2 exp (-2 t² / (#s (u - l)²))`. -/
theorem measureReal_le_abs_sum_sub_integral_le {ι : Type*} {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ) {l u : ℝ}
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc l u) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ s, (X i ω - μ[X i])|} ≤
      2 * exp (-(2 * t ^ 2 / (#s * (u - l) ^ 2))) := by
  -- the centered variables are independent and `((u - l) / 2) ^ 2`-sub-Gaussian, by Hoeffding's
  -- lemma, and so are their negatives
  have h_indep' : iIndepFun (fun i ω ↦ X i ω - μ[X i]) μ :=
    h_indep.comp (g := fun i (y : ℝ) ↦ y - ∫ ω, X i ω ∂μ) fun _ ↦ measurable_sub_const _
  have h_subG : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) ((‖u - l‖₊ / 2) ^ 2) μ :=
    fun i hi ↦ hasSubgaussianMGF_of_mem_Icc (hXm i hi) (hX i hi)
  have h_exp : exp (-t ^ 2 / (2 * ((∑ i ∈ s, (‖u - l‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) =
      exp (-(2 * t ^ 2 / (#s * (u - l) ^ 2))) := by
    congr 1
    simp only [sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs, div_pow, sq_abs]
    rw [show (2 : ℝ) * (#s * ((u - l) ^ 2 / 2 ^ 2)) = #s * (u - l) ^ 2 / 2 by ring,
      div_div_eq_mul_div]
    ring
  have h_upper := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep' h_subG ht
  have h_lower := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (h_indep'.comp (g := fun _ (y : ℝ) ↦ -y) fun _ ↦ measurable_neg)
    (fun i hi ↦ (h_subG i hi).neg) ht
  rw [h_exp] at h_upper h_lower
  -- a union bound over the two tails
  refine le_trans (measureReal_mono ?_) ((measureReal_union_le _ _).trans
    ((add_le_add h_upper h_lower).trans_eq (two_mul _).symm))
  intro ω (hω : t ≤ _)
  rcases le_abs.1 hω with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa [Function.comp_def, sum_neg_distrib] using h)

end LMLExplore
