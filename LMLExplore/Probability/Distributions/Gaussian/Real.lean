/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Real Gaussian distributions: density, moments, tilts and sub-Gaussianity

Complements to Mathlib's `ProbabilityTheory.gaussianReal`:

* `LMLExplore.log_gaussianPDFReal`: the logarithm of the Gaussian density is a quadratic
  polynomial.
* `LMLExplore.hasDerivAt_gaussianPDFReal`: the derivative of the Gaussian density `φ` is
  `φ' x = -((x - μ) / v) φ x`.
* `LMLExplore.gaussianPDFReal_le`, `LMLExplore.tendsto_gaussianPDFReal_atTop`: the Gaussian
  density is bounded by its value `(√(2π v))⁻¹` at the mean and tends to `0` at `+∞`.
* `LMLExplore.integrable_sub_mul_gaussianPDFReal`: `x ↦ (x - μ) φ x` is integrable.
* `LMLExplore.integral_sub_sq_gaussianReal`: for `X ∼ 𝒩(μ, v)` and every `c`,
  `𝔼[(X - c) ^ 2] = v + (μ - c) ^ 2`, with the integrability statement
  `LMLExplore.integrable_sub_sq_gaussianReal`.
* `LMLExplore.tilted_mul_gaussianReal`: tilting `𝒩(μ, v)` by `x ↦ η x` gives `𝒩(μ + v η, v)`.
* `LMLExplore.integrable_exp_mul_sub_sq_gaussianReal_iff`,
  `LMLExplore.integrableExpSet_sub_sq_gaussianReal`, `LMLExplore.mgf_sub_sq_gaussianReal`,
  `LMLExplore.cgf_sub_sq_gaussianReal`: for `X ∼ 𝒩(μ, v)`, `exp (t (X - μ) ^ 2)` is integrable
  iff `2 v t < 1`, and then `𝔼[exp (t (X - μ) ^ 2)] = (√(1 - 2 v t))⁻¹`; for `v ≠ 0`, the set of
  these `t` is `(-∞, (2 v)⁻¹)`.
* `LMLExplore.tilted_mul_sub_sq_gaussianReal`: for `2 v t < 1`, tilting `𝒩(μ, v)` by
  `x ↦ t (x - μ) ^ 2` gives `𝒩(μ, v / (1 - 2 v t))`.
* `LMLExplore.integral_exp_neg_sq_div_two_gaussianReal`: for `X ∼ 𝒩(a, 1)`,
  `𝔼[exp (-X ^ 2 / 2)] = exp (-a ^ 2 / 4) / √2`.
* `LMLExplore.gaussianReal_absolutelyContinuous_gaussianReal`: two real Gaussian laws with nonzero
  variances are mutually absolutely continuous.
* `LMLExplore.rnDeriv_gaussianReal_gaussianReal`: the Radon-Nikodym derivative of `𝒩(μ₁, v₁)` with
  respect to `𝒩(μ₂, v₂)`, for `v₂ ≠ 0`, is the ratio of their densities.
* `LMLExplore.hasSubgaussianMGF_sub_of_hasLaw_gaussianReal`: a random variable with law `𝒩(μ, v)`
  is `v`-sub-Gaussian around its mean, in the sense of `ProbabilityTheory.HasSubgaussianMGF`.
* `ProbabilityTheory.iIndepFun.hasLaw_sum_gaussianReal`: a finite sum of independent random
  variables of laws `𝒩(μ i, v i)` has law `𝒩(∑ μ i, ∑ v i)`.

The derivative, boundedness, limit and integrability facts about the density are the ingredients
of the Gaussian tail bounds in `LMLExplore.Probability.Distributions.Gaussian.Tail`.
There, `integral_exp_neg_sq_div_two_gaussianReal` enters the bound on the expected inverse of the
Gaussian tail at a Gaussian point.
`log_gaussianPDFReal`, `integral_sub_sq_gaussianReal`,
`gaussianReal_absolutelyContinuous_gaussianReal` and `rnDeriv_gaussianReal_gaussianReal` are the
ingredients of the closed form of the relative entropy between Gaussian laws.
The exponential moments and tilts of `(X - μ) ^ 2` make the Gaussian laws of a fixed mean an
exponential family with sufficient statistic `x ↦ (x - μ) ^ 2`, parametrized by the variance
(`LMLExplore.Probability.Distributions.ExponentialFamily.Gaussian`).
`hasSubgaussianMGF_sub_of_hasLaw_gaussianReal` shows that Gaussian rewards satisfy the
sub-Gaussian noise assumption of Mathlib's concentration inequalities.
`iIndepFun.hasLaw_sum_gaussianReal` extends Mathlib's `gaussianReal_add_gaussianReal_of_indepFun`
from two to finitely many summands; it gives the law of the sum of the first `s` rewards of an arm
with Gaussian rewards.

## Implementation notes

`hasDerivAt_gaussianPDFReal`, `gaussianPDFReal_le` and `tendsto_gaussianPDFReal_atTop` are adapted
from the LMLPapers project (Rémy Degenne),
`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Distributions/Gaussian/Real.lean` in
<https://github.com/LeanMachineLearning/LMLPapers>.
-/

public section

open MeasureTheory ProbabilityTheory Real Filter Topology

open scoped NNReal

namespace LMLExplore

variable {μ : ℝ} {v : ℝ≥0}

/-- The logarithm of the density of `𝒩(μ, v)` is `-log (2πv) / 2 - (x - μ) ^ 2 / (2v)`. -/
lemma log_gaussianPDFReal (hv : v ≠ 0) (x : ℝ) :
    log (gaussianPDFReal μ v x) = -log (2 * π * v) / 2 - (x - μ) ^ 2 / (2 * v) := by
  have hv' : (0 : ℝ) < v := by positivity
  rw [gaussianPDFReal_def, log_mul (by positivity) (exp_pos _).ne', log_inv,
    log_sqrt (by positivity), log_exp]
  ring

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

/-- `x ↦ (x - μ) φ x` is integrable for the Gaussian density `φ = gaussianPDFReal μ v`. -/
lemma integrable_sub_mul_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (fun x ↦ (x - μ) * gaussianPDFReal μ v x) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  have hv' : (0 : ℝ) < v := by positivity
  have : (fun x ↦ (x - μ) * gaussianPDFReal μ v x) =
      fun x ↦ (√(2 * π * v))⁻¹ * ((x - μ) * exp (-(1 / (2 * v)) * (x - μ) ^ 2)) := by
    funext x
    rw [gaussianPDFReal, show -(x - μ) ^ 2 / (2 * v) = -(1 / (2 * v)) * (x - μ) ^ 2 by ring]
    ring
  rw [this]
  exact ((integrable_mul_exp_neg_mul_sq (by positivity)).comp_sub_right μ).const_mul _

/-- The square of the distance to any point is integrable under `𝒩(μ, v)`. -/
lemma integrable_sub_sq_gaussianReal (c : ℝ) :
    Integrable (fun x ↦ (x - c) ^ 2) (gaussianReal μ v) :=
  ((memLp_id_gaussianReal 2).sub (memLp_const c)).integrable_sq

/-- The second moment of `𝒩(μ, v)` around any point `c` is `v + (μ - c) ^ 2`. -/
@[simp]
lemma integral_sub_sq_gaussianReal (c : ℝ) :
    ∫ x, (x - c) ^ 2 ∂gaussianReal μ v = v + (μ - c) ^ 2 := by
  -- Translate by `c`, then use `Var[X] = 𝔼[X ^ 2] - 𝔼[X] ^ 2` for `X ∼ 𝒩(μ - c, v)`.
  have hvar := variance_eq_sub (memLp_id_gaussianReal (μ := μ - c) (v := v) 2)
  simp only [variance_id_gaussianReal, id_eq, Pi.pow_apply, integral_id_gaussianReal] at hvar
  rw [← gaussianReal_map_sub_const c] at hvar
  rw [integral_map (by fun_prop) (by fun_prop)] at hvar
  linarith

/-- The pointwise identity behind the tilting of a Gaussian law: multiplying the density of
`𝒩(μ, v)` by `exp (η x)` and normalizing by the moment generating function gives the density of
`𝒩(μ + v η, v)`. -/
private lemma gaussianPDFReal_mul_exp_div (μ η : ℝ) (hv : v ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v x * (exp (η * x) / exp (μ * η + v * η ^ 2 / 2)) =
      gaussianPDFReal (μ + v * η) v x := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  rw [gaussianPDFReal_def, gaussianPDFReal_def, mul_assoc, ← exp_sub, ← exp_add]
  congr 2
  field_simp
  ring

/-- Tilting a Gaussian law by `x ↦ η x` shifts its mean by `v η`: `𝒩(μ, v)` tilted by
`x ↦ η x` is `𝒩(μ + v η, v)`. For `v = 0`, both sides are the Dirac mass at `μ`. -/
@[simp]
lemma tilted_mul_gaussianReal (μ : ℝ) (v : ℝ≥0) (η : ℝ) :
    (gaussianReal μ v).tilted (fun x ↦ η * x) = gaussianReal (μ + v * η) v := by
  rcases eq_or_ne v 0 with rfl | hv
  · -- The Dirac mass at `μ` is unchanged by tilting.
    simp only [gaussianReal_zero_var, NNReal.coe_zero, zero_mul, add_zero]
    rw [tilted_congr (ae_eq_dirac fun x ↦ η * x)]
    -- `Function.const ℝ (η * μ)` is `fun _ ↦ η * μ` by definition.
    exact tilted_const _ _
  rw [Measure.tilted, gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext x
  have h_mgf : ∫ y, exp (η * y) ∂(volume.withDensity (gaussianPDF μ v)) =
      exp (μ * η + v * η ^ 2 / 2) := by
    rw [← gaussianReal_of_var_ne_zero _ hv]
    exact congrFun mgf_id_gaussianReal η
  simp only [Pi.mul_apply, gaussianPDF_def] at h_mgf ⊢
  rw [h_mgf, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_mul_exp_div μ η hv x]

/-! ### Exponential moments of the squared deviation -/

/-- The pointwise identity behind the exponential moments of `(X - μ) ^ 2` for `X ∼ 𝒩(μ, v)`: the
density of `𝒩(μ, v)` times `exp (t (x - μ) ^ 2)` is the Gaussian function
`exp (-((2 v)⁻¹ - t) (x - μ) ^ 2)` up to the factor `(√(2πv))⁻¹`. -/
private lemma gaussianPDFReal_mul_exp_mul_sub_sq (μ : ℝ) (v : ℝ≥0) (t x : ℝ) :
    gaussianPDFReal μ v x * exp (t * (x - μ) ^ 2) =
      (√(2 * π * v))⁻¹ * exp (-((2 * (v : ℝ))⁻¹ - t) * (x - μ) ^ 2) := by
  rw [gaussianPDFReal_def, mul_assoc, ← exp_add]
  congr 2
  ring

/-- For `v ≠ 0`, `t < (2 v)⁻¹` iff `2 v t < 1`: the two forms of the condition on `t` under which
`exp (t (X - μ) ^ 2)` is integrable for `X ∼ 𝒩(μ, v)`. -/
private lemma lt_inv_two_mul_iff (hv : v ≠ 0) {t : ℝ} : t < (2 * (v : ℝ))⁻¹ ↔ 2 * v * t < 1 := by
  rw [← one_div, lt_div_iff₀ (by positivity), mul_comm]

/-- The exponential moment `𝔼[exp (t (X - μ) ^ 2)]` of `X ∼ 𝒩(μ, v)` is finite iff
`2 v t < 1`. -/
@[simp]
lemma integrable_exp_mul_sub_sq_gaussianReal_iff (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x ↦ exp (t * (x - μ) ^ 2)) (gaussianReal μ v) ↔ 2 * v * t < 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simpa [gaussianReal_zero_var] using integrable_dirac (a := μ) (by simp)
  have hc : (√(2 * π * v))⁻¹ ≠ 0 := by positivity
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp_rw [toReal_gaussianPDF, mul_comm (exp _), gaussianPDFReal_mul_exp_mul_sub_sq,
    integrable_const_mul_iff (IsUnit.mk0 _ hc)]
  -- Translate by `μ` and use the integrability criterion of the Gaussian function.
  have h_iff : Integrable (fun x ↦ exp (-((2 * (v : ℝ))⁻¹ - t) * (x - μ) ^ 2)) ↔
      Integrable (fun x : ℝ ↦ exp (-((2 * (v : ℝ))⁻¹ - t) * x ^ 2)) :=
    ⟨fun h ↦ by simpa using h.comp_add_right μ, fun h ↦ h.comp_sub_right μ⟩
  rw [h_iff, integrable_exp_neg_mul_sq_iff, sub_pos, lt_inv_two_mul_iff hv]

/-- For `v ≠ 0`, the set of `t` at which `exp (t (X - μ) ^ 2)` is integrable for `X ∼ 𝒩(μ, v)` is
`(-∞, (2 v)⁻¹)`. -/
@[simp]
lemma integrableExpSet_sub_sq_gaussianReal (μ : ℝ) (hv : v ≠ 0) :
    integrableExpSet (fun x ↦ (x - μ) ^ 2) (gaussianReal μ v) = Set.Iio (2 * (v : ℝ))⁻¹ := by
  ext t
  rw [Set.mem_Iio, lt_inv_two_mul_iff hv]
  exact integrable_exp_mul_sub_sq_gaussianReal_iff μ v t

/-- The moment generating function of `(X - μ) ^ 2` for `X ∼ 𝒩(μ, v)` is
`t ↦ (√(1 - 2 v t))⁻¹` on `2 v t < 1`. -/
@[simp]
lemma mgf_sub_sq_gaussianReal (μ : ℝ) (v : ℝ≥0) {t : ℝ} (ht : 2 * v * t < 1) :
    mgf (fun x ↦ (x - μ) ^ 2) (gaussianReal μ v) t = (√(1 - 2 * v * t))⁻¹ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var, mgf_dirac']
  have hv' : (0 : ℝ) < v := by positivity
  have hs : 0 < 1 - 2 * v * t := by linarith
  have hb : (2 * (v : ℝ))⁻¹ - t = (1 - 2 * v * t) / (2 * v) := by field_simp
  rw [mgf, integral_gaussianReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul, gaussianPDFReal_mul_exp_mul_sub_sq, integral_const_mul]
  rw [integral_sub_right_eq_self (fun x ↦ exp (-((2 * (v : ℝ))⁻¹ - t) * x ^ 2)) μ,
    integral_gaussian, hb, div_div_eq_mul_div, sqrt_div' _ hs.le, mul_comm π]
  field_simp

/-- The cumulant generating function of `(X - μ) ^ 2` for `X ∼ 𝒩(μ, v)` is
`t ↦ -log (1 - 2 v t) / 2` on `2 v t < 1`. -/
@[simp]
lemma cgf_sub_sq_gaussianReal (μ : ℝ) (v : ℝ≥0) {t : ℝ} (ht : 2 * v * t < 1) :
    cgf (fun x ↦ (x - μ) ^ 2) (gaussianReal μ v) t = -log (1 - 2 * v * t) / 2 := by
  rw [cgf, mgf_sub_sq_gaussianReal μ v ht, log_inv, log_sqrt (by linarith)]
  ring

/-- Tilting a Gaussian law by `x ↦ t (x - μ) ^ 2` rescales its variance and keeps its mean: for
`2 v t < 1`, `𝒩(μ, v)` tilted by `x ↦ t (x - μ) ^ 2` is `𝒩(μ, v / (1 - 2 v t))`. For `v = 0`,
both sides are the Dirac mass at `μ`. -/
@[simp]
lemma tilted_mul_sub_sq_gaussianReal (μ : ℝ) (v : ℝ≥0) {t : ℝ} (ht : 2 * v * t < 1) :
    (gaussianReal μ v).tilted (fun x ↦ t * (x - μ) ^ 2) =
      gaussianReal μ (v / (1 - 2 * v * t)).toNNReal := by
  rcases eq_or_ne v 0 with rfl | hv
  · -- The Dirac mass at `μ` is unchanged by tilting.
    simp only [gaussianReal_zero_var, NNReal.coe_zero, zero_div, Real.toNNReal_zero]
    rw [tilted_congr (ae_eq_dirac fun x ↦ t * (x - μ) ^ 2)]
    -- `Function.const ℝ (t * (μ - μ) ^ 2)` is `fun _ ↦ t * (μ - μ) ^ 2` by definition.
    exact tilted_const _ _
  have hv₀ : (0 : ℝ) < v := by positivity
  have hs : 0 < 1 - 2 * v * t := by linarith
  have hv' : (v / (1 - 2 * v * t)).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    positivity
  rw [Measure.tilted, gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv',
    ← withDensity_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
  congr 1
  funext x
  have h_mgf : ∫ y, exp (t * (y - μ) ^ 2) ∂(volume.withDensity (gaussianPDF μ v)) =
      (√(1 - 2 * v * t))⁻¹ := by
    rw [← gaussianReal_of_var_ne_zero _ hv]
    exact mgf_sub_sq_gaussianReal μ v ht
  simp only [Pi.mul_apply, gaussianPDF_def] at h_mgf ⊢
  rw [h_mgf, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  -- `φ_v(x) exp (t (x - μ) ^ 2) √(1 - 2 v t) = φ_{v / (1 - 2 v t)}(x)`
  rw [div_inv_eq_mul, ← mul_assoc, gaussianPDFReal_mul_exp_mul_sub_sq, gaussianPDFReal_def,
    Real.coe_toNNReal _ (by positivity), mul_right_comm]
  congr 1
  · rw [mul_div_assoc', sqrt_div' _ hs.le]
    field_simp
  · congr 1
    field_simp

/-- `𝔼[exp (-X² / 2)] = exp (-a² / 4) / √2` for `X ∼ N(a, 1)`. -/
lemma integral_exp_neg_sq_div_two_gaussianReal (a : ℝ) :
    ∫ u, exp (-u ^ 2 / 2) ∂(gaussianReal a 1) = exp (-a ^ 2 / 4) / √2 := by
  -- complete the square: `-(u - a)² / 2 - u² / 2 = -a² / 4 - (u - a / 2)²`
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  have h (u : ℝ) : gaussianPDFReal a 1 u • exp (-u ^ 2 / 2) =
      (√(2 * π))⁻¹ * exp (-a ^ 2 / 4) * exp (-1 * (u - a / 2) ^ 2) := by
    rw [smul_eq_mul, gaussianPDFReal_def, NNReal.coe_one, mul_one, mul_one, mul_assoc,
      ← exp_add, mul_assoc, ← exp_add]
    congr 2
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_sub_right_eq_self (fun u ↦ exp (-1 * u ^ 2)) (a / 2),
    integral_gaussian, div_one, sqrt_mul zero_le_two]
  field_simp

section TwoGaussians

variable {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0}

/-- A real Gaussian distribution with nonzero variance is absolutely continuous with respect to
every real Gaussian distribution with nonzero variance. -/
lemma gaussianReal_absolutelyContinuous_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    gaussianReal μ₁ v₁ ≪ gaussianReal μ₂ v₂ :=
  (gaussianReal_absolutelyContinuous μ₁ hv₁).trans (gaussianReal_absolutelyContinuous' μ₂ hv₂)

/-- The Radon-Nikodym derivative of `𝒩(μ₁, v₁)` with respect to `𝒩(μ₂, v₂)`, for `v₂ ≠ 0`, is
Lebesgue-almost everywhere the ratio of their densities. -/
lemma rnDeriv_gaussianReal_gaussianReal (μ₁ : ℝ) (v₁ : ℝ≥0) (μ₂ : ℝ) (hv₂ : v₂ ≠ 0) :
    (gaussianReal μ₁ v₁).rnDeriv (gaussianReal μ₂ v₂) =ᵐ[volume]
      fun x ↦ (gaussianPDF μ₂ v₂ x)⁻¹ * gaussianPDF μ₁ v₁ x := by
  rw [gaussianReal_of_var_ne_zero μ₂ hv₂]
  filter_upwards [Measure.rnDeriv_withDensity_right (gaussianReal μ₁ v₁) volume
    (measurable_gaussianPDF μ₂ v₂).aemeasurable
    (ae_of_all _ fun x ↦ (gaussianPDF_pos μ₂ hv₂ x).ne') (ae_of_all _ fun _ ↦ gaussianPDF_ne_top),
    rnDeriv_gaussianReal μ₁ v₁] with x hx hx'
  rw [hx, hx']

end TwoGaussians

/-- A random variable with law `𝒩(μ, v)` is `v`-sub-Gaussian around its mean `μ`. -/
lemma hasSubgaussianMGF_sub_of_hasLaw_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal μ v) P) :
    HasSubgaussianMGF (fun ω ↦ X ω - μ) v P := by
  have hY : HasLaw (fun ω ↦ X ω - μ) (gaussianReal 0 v) P := by
    simpa using gaussianReal_sub_const hX μ
  have : IsProbabilityMeasure P := hY.isProbabilityMeasure_iff.mpr inferInstance
  refine ⟨fun t ↦ ?_, fun t ↦ ?_⟩
  · rw [← mgf_pos_iff, mgf_gaussianReal hY]
    exact exp_pos _
  · rw [mgf_gaussianReal hY, zero_mul, zero_add]

end LMLExplore

namespace ProbabilityTheory.iIndepFun

/-- A finite sum of independent real random variables of laws `𝒩(m i, v i)` has the Gaussian law
`𝒩(∑ m i, ∑ v i)`. This extends `gaussianReal_add_gaussianReal_of_indepFun` to finitely many
summands. -/
theorem hasLaw_sum_gaussianReal {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ι → Ω → ℝ} (hX : iIndepFun X P) {m : ι → ℝ} {v : ι → ℝ≥0}
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P) (s : Finset ι) :
    HasLaw (fun ω ↦ ∑ i ∈ s, X i ω) (gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i)) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [gaussianReal_zero_var] using hasLaw_dirac_of_ae_eq (P := P) (ae_eq_refl _)
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    have h_indep : IndepFun (X i) (fun ω ↦ ∑ j ∈ s, X j ω) P := by
      rw [← Finset.sum_fn]
      exact (hX.indepFun_finsetSum_of_notMem₀ (fun j ↦ (hlaw j).aemeasurable) hi).symm
    exact ⟨(hlaw i).aemeasurable.add ih.aemeasurable,
      gaussianReal_add_gaussianReal_of_indepFun h_indep (hlaw i) ih⟩

end ProbabilityTheory.iIndepFun
