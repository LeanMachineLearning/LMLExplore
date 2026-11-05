/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Probability.Distributions.Gaussian.Real
public import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Tail bounds for Gaussian distributions

For a standard Gaussian random variable `Z` with density `φ = gaussianPDFReal 0 1` and `t > 0`,

`t / (1 + t²) φ(t) ≤ P(Z ≥ t) ≤ min (φ(t) / t) (exp (-t² / 2) / 2)`,

and `φ(t) / (1 + t) ≤ P(Z ≥ t)` for `t ≥ 0`, a lower bound that stays meaningful at `t = 0`.

The inverse `1 / P(Z > u)` of the tail grows like `(1 + u) / φ(u)`. Evaluated at a Gaussian
point `U ∼ N(-a, 1)` with `a > 0`, its excess over `1` has expectation
`𝔼[1 / P(Z > U) - 1] ≤ exp (-a² / 4) / √2 + exp (-a² / 2) (1 / a + 1 / a²)`, which is small for
large `a`. In Gaussian Thompson sampling, `P(Z > U)` is the probability that the sample of an arm
exceeds a level below its mean by `a` standard deviations of its posterior, and this bound controls
the expected number of rounds at which an optimal arm is underestimated [LS, Exercise 36.6(a)].

## Main statements

* `LMLExplore.div_mul_gaussianPDFReal_le_measureReal_Ici_gaussianReal_zero_one`: the Mills-ratio
  lower bound `t / (1 + t²) φ(t) ≤ P(Z ≥ t)`.
* `LMLExplore.measureReal_Ici_gaussianReal_zero_one_le_div`: the Mills-ratio upper bound
  `P(Z ≥ t) ≤ φ(t) / t`.
* `LMLExplore.gaussianPDFReal_div_one_add_le_measureReal_Ici_gaussianReal_zero_one`: the lower
  bound `φ(t) / (1 + t) ≤ P(Z ≥ t)` for `t ≥ 0`.
* `LMLExplore.measureReal_Ici_gaussianReal_zero_one_le_exp`: `P(Z ≥ t) ≤ exp (-t² / 2) / 2` for
  `t ≥ 0`.
* `LMLExplore.measureReal_Ici_gaussianReal_le_exp`: the Chernoff bound
  `P(X ≥ t) ≤ exp (-(t - μ)² / (2 v))` for `X ~ N(μ, v)` and `t ≥ μ`, for every variance `v`.
* `LMLExplore.lintegral_inv_gaussianReal_Ioi_sub_one_le`: for `a > 0` and `U ∼ N(-a, 1)`,
  `𝔼[1 / P(Z > U) - 1] ≤ exp (-a² / 4) / √2 + exp (-a² / 2) (1 / a + 1 / a²)`.

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
`measureReal_Ici_gaussianReal_self` are new here, as is the lower bound
`gaussianPDFReal_div_one_add_le_measureReal_Ici_gaussianReal_zero_one`, which follows the same
integration argument with the antiderivative `-φ(x) / (1 + x)`. The Chernoff bound
`measureReal_Ici_gaussianReal_le_exp` is Mathlib's sub-Gaussian tail bound
`HasSubgaussianMGF.measure_ge_le` applied to the Gaussian distribution.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Chapter 36 and Exercise 36.6, where these bounds enter the analysis of Thompson sampling.
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

/-- Derivative of `-φ x / (1 + x)` for `x ≥ 0`: it equals `φ x (x² + x + 1) / (1 + x)²`. -/
private lemma hasDerivAt_neg_gaussianPDFReal_div_one_add {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun x ↦ -gaussianPDFReal 0 1 x / (1 + x))
      (gaussianPDFReal 0 1 x * ((x ^ 2 + x + 1) / (1 + x) ^ 2)) x := by
  have h1 : 1 + x ≠ 0 := by positivity
  refine (((hasDerivAt_gaussianPDFReal 0 1 x).neg).div ((hasDerivAt_id x).const_add 1)
    h1).congr_deriv ?_
  simp only [sub_zero, NNReal.coe_one, div_one, id, Pi.neg_apply]
  field_simp
  ring

/-- `-φ x / (1 + x)` tends to `0` at `+∞`. -/
private lemma tendsto_neg_gaussianPDFReal_div_one_add_atTop :
    Tendsto (fun x ↦ -gaussianPDFReal 0 1 x / (1 + x)) atTop (𝓝 0) := by
  simpa using (tendsto_gaussianPDFReal_atTop 0 1).neg.div_atTop
    (tendsto_atTop_add_const_left _ 1 tendsto_id)

/-- **Lower bound on the Gaussian tail**: `φ(t) / (1 + t) ≤ P(Z ≥ t)` for a standard Gaussian `Z`
and `t ≥ 0`, where `φ = gaussianPDFReal 0 1` is its density. Unlike the Mills-ratio lower bound
`div_mul_gaussianPDFReal_le_measureReal_Ici_gaussianReal_zero_one`, it is not trivial at
`t = 0`. -/
lemma gaussianPDFReal_div_one_add_le_measureReal_Ici_gaussianReal_zero_one {t : ℝ} (ht : 0 ≤ t) :
    gaussianPDFReal 0 1 t / (1 + t) ≤ (gaussianReal 0 1).real (Ici t) := by
  -- `φ(t) / (1 + t)` is the integral over `Ioi t` of `φ x (x² + x + 1) / (1 + x)² ≤ φ x`
  have hle : ∀ x ∈ Ioi t, gaussianPDFReal 0 1 x * ((x ^ 2 + x + 1) / (1 + x) ^ 2) ≤
      gaussianPDFReal 0 1 x := fun x hx ↦ by
    have hx : 0 ≤ x := ht.trans (le_of_lt hx)
    refine mul_le_of_le_one_right (gaussianPDFReal_nonneg 0 1 x) ?_
    rw [div_le_one (by positivity)]
    nlinarith
  have hint : IntegrableOn (fun x ↦ gaussianPDFReal 0 1 x * ((x ^ 2 + x + 1) / (1 + x) ^ 2))
      (Ioi t) := by
    refine (integrable_gaussianPDFReal 0 1).integrableOn.mono'
      ((measurable_gaussianPDFReal 0 1).mul (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := ht.trans (le_of_lt hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 1 x)
      (by positivity))]
    exact hle x hx
  have h_eq : ∫ x in Ioi t, gaussianPDFReal 0 1 x * ((x ^ 2 + x + 1) / (1 + x) ^ 2) =
      gaussianPDFReal 0 1 t / (1 + t) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto
      (hasDerivAt_neg_gaussianPDFReal_div_one_add ht).continuousAt.continuousWithinAt
      (fun x hx ↦ hasDerivAt_neg_gaussianPDFReal_div_one_add (ht.trans (le_of_lt hx))) hint
      tendsto_neg_gaussianPDFReal_div_one_add_atTop]
    ring
  rw [measureReal_Ici_gaussianReal 0 one_ne_zero, ← h_eq]
  exact setIntegral_mono_on hint (integrable_gaussianPDFReal 0 1).integrableOn measurableSet_Ioi
    hle

/-- `φ x ≤ exp (-t² / 2) φ_t x` for `0 ≤ t ≤ x`, where `φ = gaussianPDFReal 0 1` and
`φ_t = gaussianPDFReal t 1` is the density of `N(t, 1)`. -/
private lemma gaussianPDFReal_zero_one_le_exp_mul {t x : ℝ} (ht : 0 ≤ t) (hx : t ≤ x) :
    gaussianPDFReal 0 1 x ≤ exp (-t ^ 2 / 2) * gaussianPDFReal t 1 x := by
  calc gaussianPDFReal 0 1 x = (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) := gaussianPDFReal_zero_one x
    _ ≤ (√(2 * π))⁻¹ * exp (-t ^ 2 / 2 + -(x - t) ^ 2 / 2) := by gcongr; nlinarith
    _ = exp (-t ^ 2 / 2) * gaussianPDFReal t 1 x := by
        rw [gaussianPDFReal_def, exp_add, NNReal.coe_one, mul_one, mul_one]
        ring

/-- The Chernoff bound for the upper tail of a Gaussian distribution: for `X ~ N(μ, v)` and
`t ≥ μ`, `P(X ≥ t) ≤ exp (-(t - μ)² / (2 v))`. It holds for every variance `v`: for `v = 0` the
right-hand side is `exp 0 = 1` with Lean's division by zero. -/
lemma measureReal_Ici_gaussianReal_le_exp {μ t : ℝ} (v : ℝ≥0) (ht : μ ≤ t) :
    (gaussianReal μ v).real (Ici t) ≤ exp (-(t - μ) ^ 2 / (2 * v)) := by
  have h := (hasSubgaussianMGF_sub_of_hasLaw_gaussianReal
    (HasLaw.id (μ := gaussianReal μ v))).measure_ge_le (sub_nonneg.2 ht)
  convert h using 2
  ext x
  simp

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

/-- For `u ≤ 0`, `1 / P(Z > u) - 1 ≤ exp (-u² / 2)` for a standard Gaussian `Z`: the tail
`q = P(Z > -u)` is at most `exp (-u² / 2) / 2 ≤ 1 / 2`, and `1 / (1 - q) - 1 ≤ 2 q`. -/
private lemma inv_measureReal_Ioi_sub_one_le_exp {u : ℝ} (hu : u ≤ 0) :
    ((gaussianReal 0 1).real (Ioi u))⁻¹ - 1 ≤ exp (-u ^ 2 / 2) := by
  have hq : (gaussianReal 0 1).real (Ioi u) + (gaussianReal 0 1).real (Ioi (-u)) = 1 := by
    rw [TauCeti.Probability.measureReal_Ioi_gaussianReal_eq_cdf 0 one_ne_zero,
      TauCeti.Probability.measureReal_Ioi_gaussianReal_eq_cdf 0 one_ne_zero]
    simp [TauCeti.Probability.cdf_gaussianReal_zero_one_neg]
  set q := (gaussianReal 0 1).real (Ioi (-u))
  have hq_le : q ≤ exp (-u ^ 2 / 2) / 2 := by
    calc q ≤ (gaussianReal 0 1).real (Ici (-u)) := measureReal_mono Ioi_subset_Ici_self
      _ ≤ exp (-(-u) ^ 2 / 2) / 2 := measureReal_Ici_gaussianReal_zero_one_le_exp (by linarith)
      _ = exp (-u ^ 2 / 2) / 2 := by rw [neg_sq]
  have hexp : exp (-u ^ 2 / 2) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  have hp : 0 < 1 - q := by linarith
  rw [show (gaussianReal 0 1).real (Ioi u) = 1 - q by linarith, inv_eq_one_div,
    div_sub_one hp.ne', div_le_iff₀ hp]
  have h_half : 1 / 2 ≤ 1 - q := by linarith
  nlinarith [exp_pos (-u ^ 2 / 2)]

/-- For `u ≥ 0`, `1 / P(Z > u) - 1 ≤ (1 + u) / φ(u)` for a standard Gaussian `Z` of density `φ`,
by `gaussianPDFReal_div_one_add_le_measureReal_Ici_gaussianReal_zero_one`. -/
private lemma inv_measureReal_Ioi_sub_one_le_div {u : ℝ} (hu : 0 ≤ u) :
    ((gaussianReal 0 1).real (Ioi u))⁻¹ - 1 ≤ (1 + u) / gaussianPDFReal 0 1 u := by
  have hφ := gaussianPDFReal_pos 0 1 u one_ne_zero
  have h := gaussianPDFReal_div_one_add_le_measureReal_Ici_gaussianReal_zero_one hu
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  rw [← measureReal_congr Ioi_ae_eq_Ici] at h
  calc ((gaussianReal 0 1).real (Ioi u))⁻¹ - 1 ≤ ((gaussianReal 0 1).real (Ioi u))⁻¹ := by
        linarith
    _ ≤ (gaussianPDFReal 0 1 u / (1 + u))⁻¹ := by gcongr
    _ = (1 + u) / gaussianPDFReal 0 1 u := inv_div _ _

/-- The ratio of the densities of `N(-a, 1)` and `N(0, 1)`, times `1 + u`. -/
private lemma gaussianPDFReal_mul_div_gaussianPDFReal (a u : ℝ) :
    gaussianPDFReal (-a) 1 u * ((1 + u) / gaussianPDFReal 0 1 u) =
      (1 + u) * exp (-a * u - a ^ 2 / 2) := by
  have h : gaussianPDFReal (-a) 1 u = gaussianPDFReal 0 1 u * exp (-a * u - a ^ 2 / 2) := by
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one]
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  rw [h]
  field_simp [(gaussianPDFReal_pos 0 1 u one_ne_zero).ne']

/-- An antiderivative of `(1 + u) exp (-a u - a² / 2)`. -/
private lemma hasDerivAt_one_add_mul_exp {a u : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun u ↦ -(exp (-a * u - a ^ 2 / 2) * (1 + u + 1 / a) / a))
      ((1 + u) * exp (-a * u - a ^ 2 / 2)) u := by
  have h1 : HasDerivAt (fun u ↦ -a * u - a ^ 2 / 2) (-a) u := by
    simpa using ((hasDerivAt_id u).const_mul (-a)).sub_const (a ^ 2 / 2)
  have h2 : HasDerivAt (fun u ↦ 1 + u + 1 / a) 1 u := by
    simpa using ((hasDerivAt_id u).const_add 1).add_const (1 / a)
  refine ((h1.exp.mul h2).div_const a).neg.congr_deriv ?_
  field_simp
  ring

private lemma tendsto_one_add_mul_exp_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u ↦ -(exp (-a * u - a ^ 2 / 2) * (1 + u + 1 / a) / a)) atTop (𝓝 0) := by
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  simp only [Real.rpow_zero, one_mul, Real.rpow_one] at h0 h1
  have := ((h0.mul_const ((1 + 1 / a) * exp (-a ^ 2 / 2))).add
    (h1.mul_const (exp (-a ^ 2 / 2)))).div_const a |>.neg
  simp only [zero_mul, add_zero, zero_div, neg_zero] at this
  refine this.congr fun u ↦ ?_
  rw [sub_eq_add_neg, exp_add, neg_div]
  ring

private lemma integrableOn_Ioi_one_add_mul_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u ↦ (1 + u) * exp (-a * u - a ^ 2 / 2)) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun _ _ ↦ hasDerivAt_one_add_mul_exp ha.ne')
    (fun u hu ↦ mul_nonneg (by linarith [hu.out]) (exp_nonneg _)) (tendsto_one_add_mul_exp_atTop ha)

private lemma integral_Ioi_one_add_mul_exp {a : ℝ} (ha : 0 < a) :
    ∫ u in Ioi 0, (1 + u) * exp (-a * u - a ^ 2 / 2) = exp (-a ^ 2 / 2) * (1 / a + 1 / a ^ 2) := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun u _ ↦ hasDerivAt_one_add_mul_exp ha.ne')
    (fun u hu ↦ mul_nonneg (by linarith [hu.out]) (exp_nonneg _))
    (tendsto_one_add_mul_exp_atTop ha)]
  field_simp
  ring_nf

/-- **The expected inverse of the Gaussian tail at a Gaussian point.** For `a > 0`, a standard
Gaussian `Z` and `U ∼ N(-a, 1)`,
`𝔼[1 / P(Z > U) - 1] ≤ exp (-a² / 4) / √2 + exp (-a² / 2) (1 / a + 1 / a²)`.
The two terms come from `U ≤ 0` and `U > 0`. For `a ≤ 0` the expectation is infinite, since
`1 / P(Z > u)` grows like `u exp (u² / 2)`. This is the Gaussian computation of
[LS, Exercise 36.6(a)]. -/
theorem lintegral_inv_gaussianReal_Ioi_sub_one_le {a : ℝ} (ha : 0 < a) :
    ∫⁻ u, (gaussianReal 0 1 (Ioi u))⁻¹ - 1 ∂(gaussianReal (-a) 1) ≤
      ENNReal.ofReal (exp (-a ^ 2 / 4) / √2 + exp (-a ^ 2 / 2) * (1 / a + 1 / a ^ 2)) := by
  have hpt (u : ℝ) : (gaussianReal 0 1 (Ioi u))⁻¹ - 1 =
      ENNReal.ofReal (((gaussianReal 0 1).real (Ioi u))⁻¹ - 1) := by
    have hpos : 0 < (gaussianReal 0 1).real (Ioi u) := by
      rw [TauCeti.Probability.measureReal_Ioi_gaussianReal_eq_cdf 0 one_ne_zero]
      exact TauCeti.Probability.cdf_gaussianReal_pos 0 one_ne_zero _
    rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one, ENNReal.ofReal_inv_of_pos hpos,
      ofReal_measureReal]
  simp_rw [hpt]
  rw [← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), compl_Iic,
    ENNReal.ofReal_add (by positivity) (by positivity)]
  gcongr ?_ + ?_
  · -- left of `0`, the bound is Gaussian in `u`
    have hint : Integrable (fun u ↦ exp (-u ^ 2 / 2)) (gaussianReal (-a) 1) := by
      refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun u ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      nlinarith
    calc ∫⁻ u in Iic 0, ENNReal.ofReal (((gaussianReal 0 1).real (Ioi u))⁻¹ - 1)
          ∂gaussianReal (-a) 1
        ≤ ∫⁻ u in Iic 0, ENNReal.ofReal (exp (-u ^ 2 / 2)) ∂gaussianReal (-a) 1 :=
          setLIntegral_mono (by fun_prop) fun u hu ↦
            ENNReal.ofReal_le_ofReal (inv_measureReal_Ioi_sub_one_le_exp hu)
      _ ≤ ∫⁻ u, ENNReal.ofReal (exp (-u ^ 2 / 2)) ∂gaussianReal (-a) 1 :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (exp (-a ^ 2 / 4) / √2) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ (exp_pos _).le),
            integral_exp_neg_sq_div_two_gaussianReal, neg_sq]
  · -- right of `0`, the density of `N(-a, 1)` compensates the factor `1 / φ(u)`
    calc ∫⁻ u in Ioi 0, ENNReal.ofReal (((gaussianReal 0 1).real (Ioi u))⁻¹ - 1)
          ∂gaussianReal (-a) 1
        ≤ ∫⁻ u in Ioi 0, ENNReal.ofReal ((1 + u) / gaussianPDFReal 0 1 u) ∂gaussianReal (-a) 1 :=
          setLIntegral_mono (by fun_prop) fun u hu ↦
            ENNReal.ofReal_le_ofReal (inv_measureReal_Ioi_sub_one_le_div (le_of_lt hu))
      _ = ∫⁻ u in Ioi 0, ENNReal.ofReal ((1 + u) * exp (-a * u - a ^ 2 / 2)) := by
          rw [gaussianReal_of_var_ne_zero _ one_ne_zero, restrict_withDensity measurableSet_Ioi,
            lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
          refine lintegral_congr fun u ↦ ?_
          rw [Pi.mul_apply, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
            gaussianPDFReal_mul_div_gaussianPDFReal]
      _ = ENNReal.ofReal (exp (-a ^ 2 / 2) * (1 / a + 1 / a ^ 2)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_one_add_mul_exp ha),
            integral_Ioi_one_add_mul_exp ha]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact mul_nonneg (by linarith [hu.out]) (exp_nonneg _)

end LMLExplore
