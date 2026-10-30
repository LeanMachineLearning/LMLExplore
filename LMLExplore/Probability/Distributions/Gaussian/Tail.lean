/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.Gaussian.Real

/-!
# Tail bounds for the standard Gaussian distribution

For a standard Gaussian random variable `Z` with density `φ = gaussianPDFReal 0 1` and `t > 0`,

`t / (1 + t²) φ(t) ≤ P(Z ≥ t) ≤ min (φ(t) / t) (exp (-t² / 2) / 2)`.

## Main statements

* `LMLExplore.div_mul_gaussianPDFReal_le_measureReal_Ici_gaussianReal_zero_one`: the Mills-ratio
  lower bound `t / (1 + t²) φ(t) ≤ P(Z ≥ t)`.
* `LMLExplore.measureReal_Ici_gaussianReal_zero_one_le_div`: the Mills-ratio upper bound
  `P(Z ≥ t) ≤ φ(t) / t`.
* `LMLExplore.measureReal_Ici_gaussianReal_zero_one_le_exp`: `P(Z ≥ t) ≤ exp (-t² / 2) / 2` for
  `t ≥ 0`.

Along the way: the tail probability as an integral of the density
(`measureReal_Ici_gaussianReal`), `P(X ≥ μ) = 1 / 2` for `X ~ N(μ, v)` with `v ≠ 0`
(`measureReal_Ici_gaussianReal_self`), and `∫ x in Ioi t, (x - μ) φ x = v φ t` for the density `φ`
of `N(μ, v)` (`integral_Ioi_sub_mul_gaussianPDFReal`).

## Implementation notes

The lower bound `div_mul_gaussianPDFReal_le_measureReal_Ici_gaussianReal_zero_one` and its private
helpers are adapted from the LMLPapers project (Rémy Degenne),
`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Distributions/Gaussian/Real.lean` in
<https://github.com/LeanMachineLearning/LMLPapers>. The two upper bounds,
`integral_Ioi_sub_mul_gaussianPDFReal`, `measureReal_Ici_gaussianReal` and
`measureReal_Ici_gaussianReal_self` are new here.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Chapter 36, where these bounds enter the analysis of Thompson sampling.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace LMLExplore

/-- For `v ≠ 0`, the upper tail probability of `N(μ, v)` at `t` is the integral of the density
over `Ioi t`. -/
lemma measureReal_Ici_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    (gaussianReal μ v).real (Ici t) = ∫ x in Ioi t, gaussianPDFReal μ v x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral μ hv,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg μ v)),
    restrict_Ioi_eq_restrict_Ici]

/-- A Gaussian distribution with nonzero variance puts mass `1 / 2` above its mean. -/
@[simp]
lemma measureReal_Ici_gaussianReal_self (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal μ v).real (Ici μ) = 1 / 2 := by
  have hv' : (0 : ℝ) < v := by positivity
  have h0 : (gaussianReal 0 v).real (Ici 0) = 1 / 2 := by
    rw [measureReal_Ici_gaussianReal 0 hv]
    simp_rw [gaussianPDFReal_def, sub_zero, integral_const_mul,
      show ∀ x : ℝ, -x ^ 2 / (2 * v) = -(1 / (2 * v)) * x ^ 2 from fun x ↦ by ring]
    rw [integral_gaussian_Ioi, show π / (1 / (2 * v)) = 2 * π * v by field_simp]
    have : 0 < √(2 * π * v) := by positivity
    field_simp
  have hmap : gaussianReal μ v = (gaussianReal 0 v).map (· + μ) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [hmap, map_measureReal_apply (measurable_add_const μ) measurableSet_Ici,
    show (· + μ) ⁻¹' Ici μ = Ici (0 : ℝ) by ext x; simp, h0]

/-- `∫ x in Ioi t, (x - μ) φ x = v φ t` for the Gaussian density `φ = gaussianPDFReal μ v`. -/
lemma integral_Ioi_sub_mul_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    ∫ x in Ioi t, (x - μ) * gaussianPDFReal μ v x = v * gaussianPDFReal μ v t := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  have hderiv : ∀ x, HasDerivAt (fun x ↦ -(v * gaussianPDFReal μ v x))
      ((x - μ) * gaussianPDFReal μ v x) x := fun x ↦
    ((hasDerivAt_gaussianPDFReal μ v x).const_mul (v : ℝ)).neg.congr_deriv (by field_simp)
  have htend : Tendsto (fun x ↦ -(v * gaussianPDFReal μ v x)) atTop (𝓝 0) := by
    simpa using ((tendsto_gaussianPDFReal_atTop μ v).const_mul (v : ℝ)).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv t).continuousAt.continuousWithinAt
    (fun x _ ↦ hderiv x) (integrable_sub_mul_gaussianPDFReal μ v).integrableOn htend]
  ring

/-- Derivative of `-φ x / x` for `x > 0`: it equals `φ x (1 + 1 / x²)`. -/
private lemma hasDerivAt_neg_gaussianPDFReal_div {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x ↦ -gaussianPDFReal 0 1 x / x)
      (gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)) x := by
  refine (((hasDerivAt_gaussianPDFReal 0 1 x).neg).div (hasDerivAt_id x)
    hx.ne').congr_deriv ?_
  simp only [sub_zero, NNReal.coe_one, div_one, id, Pi.neg_apply]
  field_simp
  ring

/-- `-φ x / x` tends to `0` at `+∞`. -/
private lemma tendsto_neg_gaussianPDFReal_div_atTop :
    Tendsto (fun x ↦ -gaussianPDFReal 0 1 x / x) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun x ↦ (√(2 * π))⁻¹ / x) ?_
    (tendsto_const_nhds.div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hx,
    abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
  gcongr
  simpa using gaussianPDFReal_le 0 1 x

/-- `φ x (1 + 1 / x²) ≤ (1 + 1 / t²) φ x` for `0 < t < x`. -/
private lemma gaussianPDFReal_mul_le_of_lt {t x : ℝ} (ht : 0 < t) (hx : t < x) :
    gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2) ≤ (1 + 1 / t ^ 2) * gaussianPDFReal 0 1 x := by
  rw [mul_comm]
  gcongr
  exact gaussianPDFReal_nonneg 0 1 x

/-- `φ x (1 + 1 / x²)` is integrable on `Ioi t` for `t > 0`. -/
private lemma integrableOn_gaussianPDFReal_mul_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)) (Ioi t) := by
  refine ((integrable_gaussianPDFReal 0 1).restrict.const_mul (1 + 1 / t ^ 2)).mono' ?_ ?_
  · exact ((measurable_gaussianPDFReal 0 1).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 1 x) (by positivity))]
    exact gaussianPDFReal_mul_le_of_lt ht hx

/-- `∫ x in Ioi t, φ x (1 + 1 / x²) = φ t / t` for `t > 0` and the standard Gaussian density
`φ = gaussianPDFReal 0 1`. -/
private lemma integral_Ioi_gaussianPDFReal_mul_zero_one {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi t, gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2) = gaussianPDFReal 0 1 t / t := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_neg_gaussianPDFReal_div ht).continuousAt.continuousWithinAt
    (fun x hx ↦ hasDerivAt_neg_gaussianPDFReal_div (ht.trans hx))
    (integrableOn_gaussianPDFReal_mul_Ioi ht) tendsto_neg_gaussianPDFReal_div_atTop]
  ring

/-- **Mills-ratio lower bound**: `t / (1 + t²) φ(t) ≤ P(Z ≥ t)` for a standard Gaussian `Z` and
`t > 0`, where `φ = gaussianPDFReal 0 1` is its density. -/
lemma div_mul_gaussianPDFReal_le_measureReal_Ici_gaussianReal_zero_one {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) * gaussianPDFReal 0 1 t ≤ (gaussianReal 0 1).real (Ici t) := by
  rw [measureReal_Ici_gaussianReal 0 one_ne_zero]
  have h : gaussianPDFReal 0 1 t / t ≤ (1 + 1 / t ^ 2) * ∫ x in Ioi t, gaussianPDFReal 0 1 x := by
    rw [← integral_Ioi_gaussianPDFReal_mul_zero_one ht, ← integral_const_mul]
    exact setIntegral_mono_on (integrableOn_gaussianPDFReal_mul_Ioi ht)
      ((integrable_gaussianPDFReal 0 1).restrict.const_mul _) measurableSet_Ioi
      fun x hx ↦ gaussianPDFReal_mul_le_of_lt ht hx
  calc t / (1 + t ^ 2) * gaussianPDFReal 0 1 t
      = t ^ 2 / (1 + t ^ 2) * (gaussianPDFReal 0 1 t / t) := by field_simp
    _ ≤ t ^ 2 / (1 + t ^ 2) * ((1 + 1 / t ^ 2) * ∫ x in Ioi t, gaussianPDFReal 0 1 x) := by
        gcongr
    _ = ∫ x in Ioi t, gaussianPDFReal 0 1 x := by field_simp; ring

/-- **Mills-ratio upper bound**: `P(Z ≥ t) ≤ φ(t) / t` for a standard Gaussian `Z` and `t > 0`,
where `φ = gaussianPDFReal 0 1` is its density. -/
lemma measureReal_Ici_gaussianReal_zero_one_le_div {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real (Ici t) ≤ gaussianPDFReal 0 1 t / t := by
  have hint : Integrable (fun x ↦ x * gaussianPDFReal 0 1 x) := by
    simpa using integrable_sub_mul_gaussianPDFReal 0 1
  have h : ∫ x in Ioi t, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 t := by
    simpa using integral_Ioi_sub_mul_gaussianPDFReal 0 1 t
  rw [measureReal_Ici_gaussianReal 0 one_ne_zero, ← h, div_eq_inv_mul, ← integral_const_mul]
  refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
    (hint.integrableOn.const_mul _) measurableSet_Ioi fun x hx ↦ ?_
  have hx' : t < x := hx
  rw [← mul_assoc, ← div_eq_inv_mul]
  exact le_mul_of_one_le_left (gaussianPDFReal_nonneg 0 1 x) ((one_le_div ht).2 hx'.le)

/-- `φ x ≤ exp (-t² / 2) φ_t x` for `0 ≤ t ≤ x`, where `φ = gaussianPDFReal 0 1` and
`φ_t = gaussianPDFReal t 1` is the density of `N(t, 1)`. -/
private lemma gaussianPDFReal_zero_one_le_exp_mul {t x : ℝ} (ht : 0 ≤ t) (hx : t ≤ x) :
    gaussianPDFReal 0 1 x ≤ exp (-t ^ 2 / 2) * gaussianPDFReal t 1 x := by
  calc gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := gaussianPDFReal_zero_one x
    _ ≤ (√(2 * π))⁻¹ * exp (-t ^ 2 / 2 + -(x - t) ^ 2 / 2) := by gcongr; nlinarith
    _ = exp (-t ^ 2 / 2) * gaussianPDFReal t 1 x := by
        rw [gaussianPDFReal_def, exp_add, NNReal.coe_one, mul_one, mul_one]
        ring

/-- `P(Z ≥ t) ≤ exp (-t² / 2) / 2` for a standard Gaussian `Z` and `t ≥ 0`. -/
lemma measureReal_Ici_gaussianReal_zero_one_le_exp {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Ici t) ≤ exp (-t ^ 2 / 2) / 2 := by
  have h_half : ∫ x in Ioi t, gaussianPDFReal t 1 x = 1 / 2 := by
    rw [← measureReal_Ici_gaussianReal t one_ne_zero,
      measureReal_Ici_gaussianReal_self t one_ne_zero]
  rw [measureReal_Ici_gaussianReal 0 one_ne_zero,
    show exp (-t ^ 2 / 2) / 2 = exp (-t ^ 2 / 2) * ∫ x in Ioi t, gaussianPDFReal t 1 x by
      rw [h_half]; ring,
    ← integral_const_mul]
  exact setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
    ((integrable_gaussianPDFReal t 1).integrableOn.const_mul _) measurableSet_Ioi
    fun x hx ↦ gaussianPDFReal_zero_one_le_exp_mul ht (le_of_lt hx)

end LMLExplore
