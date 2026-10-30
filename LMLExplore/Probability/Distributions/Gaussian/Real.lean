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
# Real Gaussian distributions: density, second moments and sub-Gaussianity

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
* `LMLExplore.gaussianReal_absolutelyContinuous_gaussianReal`: two real Gaussian laws with nonzero
  variances are mutually absolutely continuous.
* `LMLExplore.rnDeriv_gaussianReal_gaussianReal`: the Radon-Nikodym derivative of `𝒩(μ₁, v₁)` with
  respect to `𝒩(μ₂, v₂)`, for `v₂ ≠ 0`, is the ratio of their densities.
* `LMLExplore.hasSubgaussianMGF_sub_of_hasLaw_gaussianReal`: a random variable with law `𝒩(μ, v)`
  is `v`-sub-Gaussian around its mean, in the sense of `ProbabilityTheory.HasSubgaussianMGF`.

The derivative, boundedness, limit and integrability facts about the density are the ingredients
of the Gaussian tail bounds in `LMLExplore.Probability.Distributions.Gaussian.Tail`.
`log_gaussianPDFReal`, `integral_sub_sq_gaussianReal`,
`gaussianReal_absolutelyContinuous_gaussianReal` and `rnDeriv_gaussianReal_gaussianReal` are the
ingredients of the closed form of the relative entropy between Gaussian laws.
`hasSubgaussianMGF_sub_of_hasLaw_gaussianReal` shows that Gaussian rewards satisfy the
sub-Gaussian noise assumption of Mathlib's concentration inequalities.

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
