/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tail bounds for the standard Gaussian distribution

For a standard Gaussian random variable `Z` with density `φ = gaussianPDFReal 0 1` and `t > 0`,

`t / (1 + t²) φ(t) ≤ P(Z ≥ t) ≤ min (φ(t) / t) (exp (-t² / 2) / 2)`.

## Main statements

* `LMLExplore.mul_gaussianPDFReal_le_measureReal_Ici`: the Mills-ratio lower bound
  `t / (1 + t²) φ(t) ≤ P(Z ≥ t)`.
* `LMLExplore.measureReal_Ici_gaussianReal_le_div`: the Mills-ratio upper bound
  `P(Z ≥ t) ≤ φ(t) / t`.
* `LMLExplore.measureReal_Ici_gaussianReal_le_exp`: `P(Z ≥ t) ≤ exp (-t² / 2) / 2` for `t ≥ 0`.

Along the way: the derivative of the Gaussian density (`hasDerivAt_gaussianPDFReal`), its bound by
its value at the mean (`gaussianPDFReal_le`), the tail probability as an integral of the density
(`measureReal_Ici_gaussianReal`), and `P(X ≥ μ) = 1 / 2` for `X ~ N(μ, 1)`
(`measureReal_Ici_gaussianReal_self`).

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Chapter 36, where these bounds enter the analysis of Thompson sampling.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace LMLExplore

/-- The derivative of the Gaussian density `φ = gaussianPDFReal μ v` is
`φ' x = -((x - μ) / v) * φ x`. Also true (as `0 = 0`) for `v = 0`. -/
lemma hasDerivAt_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-((x - μ) / v) * gaussianPDFReal μ v x) x := by
  simp only [gaussianPDFReal]
  have h : HasDerivAt (fun y ↦ -(y - μ) ^ 2 / (2 * v)) (-(x - μ) / v) x := by
    refine ((((hasDerivAt_id' x).sub_const μ).fun_pow 2).fun_neg.div_const
      (2 * (v : ℝ))).congr_deriv ?_
    norm_num
    ring
  refine (h.exp.const_mul (√(2 * π * v))⁻¹).congr_deriv ?_
  ring

/-- The standard Gaussian density: `φ x = exp (-x² / 2) / √(2π)`. -/
lemma gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal]

/-- The Gaussian density is bounded by its value `(√(2π v))⁻¹` at the mean. -/
lemma gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal_def]
  refine mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- The Gaussian density tends to `0` at `+∞`. -/
lemma tendsto_gaussianPDFReal_atTop (μ : ℝ) (v : ℝ≥0) :
    Tendsto (gaussianPDFReal μ v) atTop (𝓝 0) := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianPDFReal_zero_var, Pi.zero_def]
    exact tendsto_const_nhds
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have h : Tendsto (fun x : ℝ ↦ (x - μ) ^ 2 / (2 * v)) atTop atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_right _ (-μ)
      tendsto_id)).atTop_div_const (by positivity)
  have := (tendsto_exp_neg_atTop_nhds_zero.comp h).const_mul (√(2 * π * v))⁻¹
  rw [mul_zero] at this
  refine this.congr fun x ↦ ?_
  simp [gaussianPDFReal_def, neg_div, sub_eq_add_neg]

/-- For `v ≠ 0`, the upper tail probability of `N(μ, v)` at `t` is the integral of the density
over `Ioi t`. -/
lemma measureReal_Ici_gaussianReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    (gaussianReal μ v).real (Ici t) = ∫ x in Ioi t, gaussianPDFReal μ v x := by
  rw [measureReal_def, gaussianReal_apply_eq_integral μ hv,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg μ v)),
    restrict_Ioi_eq_restrict_Ici]

/-- A Gaussian distribution with unit variance puts mass `1 / 2` above its mean. -/
lemma measureReal_Ici_gaussianReal_self (μ : ℝ) : (gaussianReal μ 1).real (Ici μ) = 1 / 2 := by
  have h0 : (gaussianReal 0 1).real (Ici 0) = 1 / 2 := by
    rw [measureReal_Ici_gaussianReal 0 one_ne_zero]
    simp_rw [gaussianPDFReal_zero_one, integral_const_mul,
      show ∀ x : ℝ, -x ^ 2 / 2 = -(1 / 2) * x ^ 2 from fun x ↦ by ring]
    rw [integral_gaussian_Ioi, show π / (1 / 2) = 2 * π by ring]
    field_simp
  have hmap : gaussianReal μ 1 = (gaussianReal 0 1).map (· + μ) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [hmap, map_measureReal_apply (measurable_add_const μ) measurableSet_Ici,
    show (· + μ) ⁻¹' Ici μ = Ici (0 : ℝ) by ext x; simp, h0]

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

/-- `φ x (1 + 1 / x²)` is integrable on `Ioi t` for `t > 0`. -/
private lemma integrableOn_gaussianPDFReal_mul_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2)) (Ioi t) := by
  refine ((integrable_gaussianPDFReal 0 1).restrict.const_mul (1 + 1 / t ^ 2)).mono' ?_ ?_
  · exact ((measurable_gaussianPDFReal 0 1).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : t < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 1 x) (by positivity)),
      mul_comm]
    gcongr
    exact gaussianPDFReal_nonneg 0 1 x

/-- `∫ x in Ioi t, φ x (1 + 1 / x²) = φ t / t` for `t > 0` and the standard Gaussian density
`φ = gaussianPDFReal 0 1`. -/
lemma integral_gaussianPDFReal_mul_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi t, gaussianPDFReal 0 1 x * (1 + 1 / x ^ 2) = gaussianPDFReal 0 1 t / t := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_neg_gaussianPDFReal_div ht).continuousAt.continuousWithinAt
    (fun x hx ↦ hasDerivAt_neg_gaussianPDFReal_div (ht.trans hx))
    (integrableOn_gaussianPDFReal_mul_Ioi ht) tendsto_neg_gaussianPDFReal_div_atTop]
  ring

/-- `x ↦ x φ x` is integrable for the standard Gaussian density `φ = gaussianPDFReal 0 1`. -/
lemma integrable_mul_gaussianPDFReal_zero_one :
    Integrable (fun x ↦ x * gaussianPDFReal 0 1 x) := by
  have : (fun x ↦ x * gaussianPDFReal 0 1 x) =
      fun x ↦ (√(2 * π))⁻¹ * (x * exp (-(1 / 2) * x ^ 2)) := by
    funext x
    rw [gaussianPDFReal_zero_one, show -x ^ 2 / 2 = -(1 / 2) * x ^ 2 by ring]
    ring
  rw [this]
  exact (integrable_mul_exp_neg_mul_sq (by norm_num)).const_mul _

/-- `∫ x in Ioi t, x φ x = φ t` for the standard Gaussian density `φ = gaussianPDFReal 0 1`. -/
lemma integral_Ioi_mul_gaussianPDFReal_zero_one (t : ℝ) :
    ∫ x in Ioi t, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 t := by
  have hderiv : ∀ x, HasDerivAt (fun x ↦ -gaussianPDFReal 0 1 x) (x * gaussianPDFReal 0 1 x) x :=
    fun x ↦ (hasDerivAt_gaussianPDFReal 0 1 x).neg.congr_deriv (by simp)
  have htend : Tendsto (fun x ↦ -gaussianPDFReal 0 1 x) atTop (𝓝 0) := by
    simpa using (tendsto_gaussianPDFReal_atTop 0 1).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hderiv t).continuousAt.continuousWithinAt
    (fun x _ ↦ hderiv x) integrable_mul_gaussianPDFReal_zero_one.integrableOn htend]
  ring

/-- **Mills-ratio lower bound**: `t / (1 + t²) φ(t) ≤ P(Z ≥ t)` for a standard Gaussian `Z` and
`t > 0`, where `φ = gaussianPDFReal 0 1` is its density. -/
lemma mul_gaussianPDFReal_le_measureReal_Ici {t : ℝ} (ht : 0 < t) :
    t / (1 + t ^ 2) * gaussianPDFReal 0 1 t ≤ (gaussianReal 0 1).real (Ici t) := by
  rw [measureReal_Ici_gaussianReal 0 one_ne_zero]
  have h : gaussianPDFReal 0 1 t / t ≤ (1 + 1 / t ^ 2) * ∫ x in Ioi t, gaussianPDFReal 0 1 x := by
    rw [← integral_gaussianPDFReal_mul_Ioi ht, ← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_gaussianPDFReal_mul_Ioi ht)
      ((integrable_gaussianPDFReal 0 1).restrict.const_mul _) measurableSet_Ioi fun x hx ↦ ?_
    have hx' : t < x := hx
    rw [mul_comm]
    gcongr
    exact gaussianPDFReal_nonneg 0 1 x
  calc t / (1 + t ^ 2) * gaussianPDFReal 0 1 t
      = t ^ 2 / (1 + t ^ 2) * (gaussianPDFReal 0 1 t / t) := by field_simp
    _ ≤ t ^ 2 / (1 + t ^ 2) * ((1 + 1 / t ^ 2) * ∫ x in Ioi t, gaussianPDFReal 0 1 x) := by
        gcongr
    _ = ∫ x in Ioi t, gaussianPDFReal 0 1 x := by field_simp; ring

/-- **Mills-ratio upper bound**: `P(Z ≥ t) ≤ φ(t) / t` for a standard Gaussian `Z` and `t > 0`,
where `φ = gaussianPDFReal 0 1` is its density. -/
lemma measureReal_Ici_gaussianReal_le_div {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 1).real (Ici t) ≤ gaussianPDFReal 0 1 t / t := by
  rw [measureReal_Ici_gaussianReal 0 one_ne_zero, ← integral_Ioi_mul_gaussianPDFReal_zero_one t,
    div_eq_inv_mul, ← integral_const_mul]
  refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
    (integrable_mul_gaussianPDFReal_zero_one.integrableOn.const_mul _) measurableSet_Ioi
    fun x hx ↦ ?_
  have hx' : t < x := hx
  rw [← mul_assoc, ← div_eq_inv_mul]
  exact le_mul_of_one_le_left (gaussianPDFReal_nonneg 0 1 x) ((one_le_div ht).2 hx'.le)

/-- `P(Z ≥ t) ≤ exp (-t² / 2) / 2` for a standard Gaussian `Z` and `t ≥ 0`. -/
lemma measureReal_Ici_gaussianReal_le_exp {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real (Ici t) ≤ exp (-t ^ 2 / 2) / 2 := by
  have h_half : ∫ x in Ioi t, gaussianPDFReal t 1 x = 1 / 2 := by
    rw [← measureReal_Ici_gaussianReal t one_ne_zero, measureReal_Ici_gaussianReal_self]
  rw [measureReal_Ici_gaussianReal 0 one_ne_zero,
    show exp (-t ^ 2 / 2) / 2 = exp (-t ^ 2 / 2) * ∫ x in Ioi t, gaussianPDFReal t 1 x by
      rw [h_half]; ring,
    ← integral_const_mul]
  refine setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
    ((integrable_gaussianPDFReal t 1).integrableOn.const_mul _) measurableSet_Ioi
    fun x hx ↦ ?_
  have hx' : t < x := hx
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_left_comm, ← exp_add]
  gcongr
  nlinarith

end LMLExplore
