/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
import Statlib.Divergence.BretagnolleHuber
import Statlib.Divergence.TotalVariation.Integral

/-!
# The Bretagnolle–Huber inequality

For probability measures `μ` and `ν` and a measurable set `A`,
`μ A + ν Aᶜ ≥ exp (-KL(μ ‖ ν)) / 2`.

Statlib proves the Bretagnolle–Huber inequality in terms of the total variation distance,
`exp (-KL(μ ‖ ν)) ≤ 2 - tvDist μ ν` (`ProbabilityTheory.exp_neg_klDiv_le_two_sub_tvDist`). This file
derives from it the integral form [LS, (14.8)] and the bound on the errors of a test
[LS, Theorem 14.2].

## Main statements

* `LMLExplore.ofReal_exp_neg_klDiv_div_two_le_lintegral_min_rnDeriv`: the stronger form
  `exp (-KL(μ ‖ ν)) / 2 ≤ ∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν`, an integral of the minimum of the two
  densities.
* `LMLExplore.exp_neg_klDiv_div_two_le`: the Bretagnolle–Huber inequality.
* `LMLExplore.lintegral_rnDeriv_rpow_half_le`: the Cauchy–Schwarz bound
  `(∫⁻ √(μ.rnDeriv ν) ∂ν)² ≤ (μ univ + ν univ) ∫⁻ min (μ.rnDeriv ν) 1 ∂ν`.
* `LMLExplore.ofReal_exp_neg_toReal_klDiv_div_two_le_lintegral_rnDeriv_rpow_half`: the Jensen
  bound `exp (-KL(μ ‖ ν) / 2) ≤ ∫⁻ √(μ.rnDeriv ν) ∂ν`.

## Proof sketch

Let `f = μ.rnDeriv ν`. At finite relative entropy `μ ≪ ν`, so the integral form of the total
variation distance with `ν` as reference measure
(`ProbabilityTheory.tvDist_eq_add_sub_two_mul_integral_min`) reads
`∫ min f 1 ∂ν = 1 - tvDist μ ν / 2`, and (14.8) is Statlib's inequality divided by two. Finally
`μ A + ν Aᶜ ≥ ∫⁻ min f 1 ∂ν`.

The last two bounds give another proof of (14.8), without the total variation distance: by the
Cauchy–Schwarz inequality, `(∫⁻ √f ∂ν)² ≤ (∫⁻ min f 1 ∂ν) (∫⁻ max f 1 ∂ν) ≤ 2 ∫⁻ min f 1 ∂ν`, and
`∫⁻ √f ∂ν = ∫ exp (-llr μ ν / 2) ∂μ ≥ exp (-KL(μ ‖ ν) / 2)` by Jensen's inequality.

## References

* J. Bretagnolle and C. Huber, *Estimation des densités : risque minimax*, Z. Wahrsch. Verw.
  Gebiete 47 (1979).
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer (2009), Lemma 2.6.
* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Theorem 14.2 and (14.8).

The Cauchy–Schwarz and Jensen bounds are adapted from the formalization in the LMLPapers project
(`LeanMachineLearning/ForMathlib/InformationTheory/KullbackLeibler/BretagnolleHuber.lean` in
`LeanMachineLearning/LMLPapers`). The stronger form (14.8), and the derivation of the inequality
from it, are new here.
-/

public section

open MeasureTheory InformationTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace LMLExplore

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {A : Set Ω}

/-- Lower bound on `μ A + ν Aᶜ` by the integral of the minimum of the density `μ.rnDeriv ν`
and `1`. -/
lemma lintegral_min_rnDeriv_one_le (hA : MeasurableSet A) :
    ∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν ≤ μ A + ν Aᶜ := by
  rw [← lintegral_add_compl _ hA]
  gcongr
  · exact (lintegral_mono fun x ↦ min_le_left _ _).trans (Measure.setLIntegral_rnDeriv_le A)
  · exact (lintegral_mono fun x ↦ min_le_right _ _).trans (setLIntegral_one _).le

/-- The stronger form of the Bretagnolle–Huber inequality [LS, (14.8)]: for probability measures
`μ` and `ν` at finite relative entropy, the integral of the minimum of the two densities,
`∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν`, is at least `exp (-KL(μ ‖ ν)) / 2`. This is Statlib's
`ProbabilityTheory.exp_neg_klDiv_le_two_sub_tvDist` divided by two, since `μ ≪ ν` and then
`∫ x, min (μ.rnDeriv ν x) 1 ∂ν = 1 - tvDist μ ν / 2`. -/
theorem ofReal_exp_neg_klDiv_div_two_le_lintegral_min_rnDeriv
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : klDiv μ ν ≠ ∞) :
    ENNReal.ofReal (exp (-(klDiv μ ν).toReal) / 2) ≤ ∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν := by
  -- The density of `ν` with respect to itself is `1`, so the minimum of the two densities with
  -- respect to `ν` is `min (μ.rnDeriv ν) 1`.
  have h_int : ∫ x, min (μ.rnDeriv ν x).toReal (ν.rnDeriv ν x).toReal ∂ν =
      (∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν).toReal := by
    rw [← integral_toReal ((Measure.measurable_rnDeriv μ ν).min measurable_const).aemeasurable
      (.of_forall fun x ↦ (min_le_right _ _).trans_lt ENNReal.one_lt_top)]
    refine integral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_self ν, Measure.rnDeriv_lt_top μ ν] with x hx hlt
    rw [hx, ENNReal.toReal_min hlt.ne ENNReal.one_ne_top]
  have h_tv := tvDist_eq_add_sub_two_mul_integral_min (klDiv_ne_top_iff.mp h).1
    (Measure.AbsolutelyContinuous.refl ν)
  rw [probReal_univ, probReal_univ, h_int] at h_tv
  refine ENNReal.ofReal_le_of_le_toReal ?_
  linarith [exp_neg_klDiv_le_two_sub_tvDist μ ν h]

/-- **Bretagnolle–Huber inequality** [LS, Theorem 14.2]: for probability measures `μ` and `ν` at
finite relative entropy and a measurable set `A`, `exp (-KL(μ ‖ ν)) / 2 ≤ μ A + ν Aᶜ`. -/
theorem exp_neg_klDiv_div_two_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) (h : klDiv μ ν ≠ ∞) :
    exp (-(klDiv μ ν).toReal) / 2 ≤ μ.real A + ν.real Aᶜ := by
  have h_le := (ofReal_exp_neg_klDiv_div_two_le_lintegral_min_rnDeriv h).trans
    (lintegral_min_rnDeriv_one_le (μ := μ) (ν := ν) hA)
  rwa [ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← measureReal_def,
    ← measureReal_def] at h_le

/-! ### The integral of the square root of the density -/

/-- Cauchy–Schwarz bound: the integral of the square root of the density `μ.rnDeriv ν` is bounded
by the geometric mean of `μ univ + ν univ` and of the integral of `min (μ.rnDeriv ν) 1`. -/
lemma lintegral_rnDeriv_rpow_half_le :
    ∫⁻ x, μ.rnDeriv ν x ^ (1 / 2 : ℝ) ∂ν
      ≤ ((μ univ + ν univ) * ∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν) ^ (1 / 2 : ℝ) := by
  have h_eq : ∀ x, μ.rnDeriv ν x ^ (1 / 2 : ℝ)
      = min (μ.rnDeriv ν x) 1 ^ (1 / 2 : ℝ) * max (μ.rnDeriv ν x) 1 ^ (1 / 2 : ℝ) := by
    intro x
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), min_mul_max, mul_one]
  simp_rw [h_eq]
  calc ∫⁻ x, min (μ.rnDeriv ν x) 1 ^ (1 / 2 : ℝ) * max (μ.rnDeriv ν x) 1 ^ (1 / 2 : ℝ) ∂ν
      ≤ (∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν) ^ (1 / 2 : ℝ)
        * (∫⁻ x, max (μ.rnDeriv ν x) 1 ∂ν) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_mul_norm_pow_le
          ((Measure.measurable_rnDeriv _ _).min measurable_const).aemeasurable
          ((Measure.measurable_rnDeriv _ _).max measurable_const).aemeasurable
          (by norm_num) (by norm_num) (by norm_num)
    _ ≤ (∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν) ^ (1 / 2 : ℝ) * (μ univ + ν univ) ^ (1 / 2 : ℝ) := by
        gcongr
        calc ∫⁻ x, max (μ.rnDeriv ν x) 1 ∂ν ≤ ∫⁻ x, μ.rnDeriv ν x + 1 ∂ν :=
              lintegral_mono fun x ↦ max_le (le_add_right le_rfl) (le_add_left le_rfl)
          _ ≤ μ univ + ν univ := by
              rw [lintegral_add_right _ measurable_const, lintegral_one]
              gcongr
              exact Measure.lintegral_rnDeriv_le
    _ = ((μ univ + ν univ) * ∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_comm]

/-- The integral of the square root of the density `μ.rnDeriv ν` with respect to `ν` is the
integral of `exp (-llr μ ν / 2)` with respect to `μ`. -/
lemma lintegral_rnDeriv_rpow_half_eq [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫⁻ x, μ.rnDeriv ν x ^ (1 / 2 : ℝ) ∂ν
      = ∫⁻ x, ENNReal.ofReal (exp (-llr μ ν x / 2)) ∂μ := by
  rw [← lintegral_rnDeriv_mul hμν (by fun_prop)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h0 : μ.rnDeriv ν x = 0
  · simp [h0, ENNReal.zero_rpow_of_pos]
  · have hpos : 0 < (μ.rnDeriv ν x).toReal := ENNReal.toReal_pos h0 hx.ne
    have h_exp : exp (-llr μ ν x / 2) = (μ.rnDeriv ν x).toReal ^ (-1 / 2 : ℝ) := by
      rw [llr, Real.rpow_def_of_pos hpos]
      congr 1
      ring
    rw [h_exp, ← ENNReal.ofReal_rpow_of_pos hpos, ENNReal.ofReal_toReal hx.ne]
    calc μ.rnDeriv ν x ^ (1 / 2 : ℝ) = μ.rnDeriv ν x ^ (1 + (-1 / 2) : ℝ) := by norm_num
      _ = μ.rnDeriv ν x ^ (1 : ℝ) * μ.rnDeriv ν x ^ (-1 / 2 : ℝ) := ENNReal.rpow_add _ _ h0 hx.ne
      _ = μ.rnDeriv ν x * μ.rnDeriv ν x ^ (-1 / 2 : ℝ) := by rw [ENNReal.rpow_one]

/-- Jensen bound: for probability measures at finite relative entropy,
`exp (-KL(μ ‖ ν) / 2) ≤ ∫⁻ x, (μ.rnDeriv ν x) ^ (1 / 2) ∂ν`. Together with
`lintegral_rnDeriv_rpow_half_le`, it bounds `∫⁻ x, min (μ.rnDeriv ν x) 1 ∂ν` below by
`exp (-KL(μ ‖ ν)) / 2` without the total variation distance. -/
lemma ofReal_exp_neg_toReal_klDiv_div_two_le_lintegral_rnDeriv_rpow_half
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : klDiv μ ν ≠ ∞) :
    ENNReal.ofReal (exp (-(klDiv μ ν).toReal / 2)) ≤ ∫⁻ x, μ.rnDeriv ν x ^ (1 / 2 : ℝ) ∂ν := by
  obtain ⟨hμν, h_int⟩ := klDiv_ne_top_iff.mp h
  have h_nonneg : 0 ≤ᵐ[μ] fun x ↦ exp (-llr μ ν x / 2) := ae_of_all _ fun x ↦ (exp_pos _).le
  have h_int' : Integrable (fun x ↦ exp (-llr μ ν x / 2)) μ := by
    refine ⟨(by fun_prop : Measurable fun x ↦ exp (-llr μ ν x / 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal h_nonneg, ← lintegral_rnDeriv_rpow_half_eq hμν]
    refine lintegral_rnDeriv_rpow_half_le.trans_lt ?_
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top (by simp) ?_)
    refine ((lintegral_mono fun x ↦ min_le_right _ _).trans_lt ?_).ne
    rw [lintegral_one]
    exact measure_lt_top _ _
  have h_jensen : exp (∫ x, -llr μ ν x / 2 ∂μ) ≤ ∫ x, exp (-llr μ ν x / 2) ∂μ :=
    convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ ↦ mem_univ _) (h_int.neg.div_const 2) h_int'
  have h_integral : ∫ x, -llr μ ν x / 2 ∂μ = -(klDiv μ ν).toReal / 2 := by
    rw [integral_div, integral_neg, toReal_klDiv_of_measure_eq hμν (by simp)]
  rw [← h_integral, lintegral_rnDeriv_rpow_half_eq hμν,
    ← ofReal_integral_eq_lintegral_ofReal h_int' h_nonneg]
  exact ENNReal.ofReal_le_ofReal h_jensen

end LMLExplore
