/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Real Gaussian distributions: log-density, second moments and sub-Gaussianity

Complements to Mathlib's `ProbabilityTheory.gaussianReal`:

* `LMLExplore.log_gaussianPDFReal`: the logarithm of the Gaussian density is a quadratic
  polynomial.
* `LMLExplore.integral_sub_sq_gaussianReal`: for `X ∼ 𝒩(μ, v)` and every `c`,
  `𝔼[(X - c) ^ 2] = v + (μ - c) ^ 2`, with the integrability statement
  `LMLExplore.integrable_sub_sq_gaussianReal`.
* `LMLExplore.gaussianReal_absolutelyContinuous_gaussianReal`: two real Gaussian laws with nonzero
  variances are mutually absolutely continuous.
* `LMLExplore.rnDeriv_gaussianReal_gaussianReal`: the Radon-Nikodym derivative of `𝒩(μ₁, v₁)` with
  respect to `𝒩(μ₂, v₂)`, for `v₂ ≠ 0`, is the ratio of their densities.
* `LMLExplore.hasSubgaussianMGF_sub_of_hasLaw_gaussianReal`: a random variable with law `𝒩(μ, v)`
  is `v`-sub-Gaussian around its mean, in the sense of `ProbabilityTheory.HasSubgaussianMGF`.

The first four are the ingredients of the closed form of the relative entropy between Gaussian
laws; the last shows that Gaussian rewards satisfy the sub-Gaussian noise assumption of Mathlib's
concentration inequalities.
-/

public section

open MeasureTheory ProbabilityTheory Real

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
