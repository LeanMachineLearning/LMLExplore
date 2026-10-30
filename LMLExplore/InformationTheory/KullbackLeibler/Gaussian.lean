/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import LMLExplore.Probability.Distributions.Gaussian.Real

/-!
# Relative entropy between real Gaussian distributions

For `v₁ v₂ ≠ 0`, the log-likelihood ratio of `𝒩(μ₁, v₁)` with respect to `𝒩(μ₂, v₂)` is the
quadratic polynomial `log (v₂ / v₁) / 2 + (x - μ₂) ^ 2 / (2 v₂) - (x - μ₁) ^ 2 / (2 v₁)`, and
integrating it against `𝒩(μ₁, v₁)` gives the closed form
`D(𝒩(μ₁, v₁), 𝒩(μ₂, v₂)) = (log (v₂ / v₁) + (v₁ + (μ₁ - μ₂) ^ 2) / v₂ - 1) / 2`.
For equal variances this is `(μ₁ - μ₂) ^ 2 / (2 v)` [LS, Theorem 14.1], the value used in the
lower bounds for Gaussian bandits.

## Main statements

* `LMLExplore.llr_gaussianReal_gaussianReal`: the log-likelihood ratio, almost everywhere.
* `LMLExplore.klDiv_gaussianReal_gaussianReal`: the relative entropy for arbitrary variances.
* `LMLExplore.klDiv_gaussianReal_gaussianReal_same_var`: the relative entropy for equal variances.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real

open scoped ENNReal NNReal

namespace LMLExplore

variable {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0}

/-- A real Gaussian distribution with nonzero variance is absolutely continuous with respect to
every real Gaussian distribution with nonzero variance. -/
lemma gaussianReal_absolutelyContinuous_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    gaussianReal μ₁ v₁ ≪ gaussianReal μ₂ v₂ :=
  (gaussianReal_absolutelyContinuous μ₁ hv₁).trans (gaussianReal_absolutelyContinuous' μ₂ hv₂)

/-- The log-likelihood ratio of `𝒩(μ₁, v₁)` with respect to `𝒩(μ₂, v₂)` is, Lebesgue-almost
everywhere, the quadratic polynomial
`log (v₂ / v₁) / 2 + (x - μ₂) ^ 2 / (2 v₂) - (x - μ₁) ^ 2 / (2 v₁)`. -/
lemma llr_gaussianReal_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    llr (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂) =ᵐ[volume] fun x ↦
      log (v₂ / v₁) / 2 + (x - μ₂) ^ 2 / (2 * v₂) - (x - μ₁) ^ 2 / (2 * v₁) := by
  have hrn : (gaussianReal μ₁ v₁).rnDeriv (gaussianReal μ₂ v₂) =ᵐ[volume]
      fun x ↦ (gaussianPDF μ₂ v₂ x)⁻¹ * gaussianPDF μ₁ v₁ x := by
    rw [gaussianReal_of_var_ne_zero μ₂ hv₂]
    filter_upwards [Measure.rnDeriv_withDensity_right (gaussianReal μ₁ v₁) volume
      (measurable_gaussianPDF μ₂ v₂).aemeasurable
      (ae_of_all _ fun x ↦ (gaussianPDF_pos μ₂ hv₂ x).ne') (ae_of_all _ fun _ ↦ gaussianPDF_ne_top),
      rnDeriv_gaussianReal μ₁ v₁] with x hx hx'
    rw [hx, hx']
  filter_upwards [hrn] with x hx
  have hv₁' : (0 : ℝ) < v₁ := by positivity
  have hv₂' : (0 : ℝ) < v₂ := by positivity
  simp only [llr_def]
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_gaussianPDF, toReal_gaussianPDF,
    log_mul (inv_pos.2 (gaussianPDFReal_pos μ₂ v₂ x hv₂)).ne' (gaussianPDFReal_pos μ₁ v₁ x hv₁).ne',
    log_inv, log_gaussianPDFReal hv₁, log_gaussianPDFReal hv₂, log_div hv₂'.ne' hv₁'.ne',
    log_mul (by positivity) hv₁'.ne', log_mul (by positivity) hv₂'.ne']
  ring

/-- The log-likelihood ratio of `𝒩(μ₁, v₁)` with respect to `𝒩(μ₂, v₂)` is the quadratic
polynomial of `llr_gaussianReal_gaussianReal`, `𝒩(μ₁, v₁)`-almost everywhere. -/
private lemma llr_gaussianReal_gaussianReal_ae (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    llr (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂) =ᵐ[gaussianReal μ₁ v₁] fun x ↦
      log (v₂ / v₁) / 2 + (x - μ₂) ^ 2 / (2 * v₂) - (x - μ₁) ^ 2 / (2 * v₁) :=
  (gaussianReal_absolutelyContinuous μ₁ hv₁).ae_le (llr_gaussianReal_gaussianReal hv₁ hv₂)

/-- The log-likelihood ratio of two real Gaussian distributions with nonzero variances is
integrable. -/
lemma integrable_llr_gaussianReal_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    Integrable (llr (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂)) (gaussianReal μ₁ v₁) := by
  have h₁ := (integrable_sub_sq_gaussianReal (μ := μ₁) (v := v₁) μ₁).div_const (2 * v₁)
  have h₂ := (integrable_sub_sq_gaussianReal (μ := μ₁) (v := v₁) μ₂).div_const (2 * v₂)
  exact Integrable.congr (by fun_prop) (llr_gaussianReal_gaussianReal_ae hv₁ hv₂).symm

/-- The integral of the log-likelihood ratio of `𝒩(μ₁, v₁)` with respect to `𝒩(μ₂, v₂)`. -/
lemma integral_llr_gaussianReal_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    ∫ x, llr (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂) x ∂gaussianReal μ₁ v₁ =
      (log (v₂ / v₁) + (v₁ + (μ₁ - μ₂) ^ 2) / v₂ - 1) / 2 := by
  have h₁ := (integrable_sub_sq_gaussianReal (μ := μ₁) (v := v₁) μ₁).div_const (2 * v₁)
  have h₂ := (integrable_sub_sq_gaussianReal (μ := μ₁) (v := v₁) μ₂).div_const (2 * v₂)
  rw [integral_congr_ae (llr_gaussianReal_gaussianReal_ae hv₁ hv₂), integral_sub, integral_add]
  · simp only [integral_div, integral_sub_sq_gaussianReal, integral_const, probReal_univ, one_smul,
      sub_self]
    have hv₁' : (v₁ : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  all_goals fun_prop

/-- The relative entropy between two real Gaussian distributions with nonzero variances:
`D(𝒩(μ₁, v₁), 𝒩(μ₂, v₂)) = (log (v₂ / v₁) + (v₁ + (μ₁ - μ₂) ^ 2) / v₂ - 1) / 2`. -/
theorem klDiv_gaussianReal_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    klDiv (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂) =
      ENNReal.ofReal ((log (v₂ / v₁) + (v₁ + (μ₁ - μ₂) ^ 2) / v₂ - 1) / 2) := by
  rw [klDiv_of_ac_of_integrable (gaussianReal_absolutelyContinuous_gaussianReal hv₁ hv₂)
    (integrable_llr_gaussianReal_gaussianReal hv₁ hv₂), probReal_univ, probReal_univ,
    add_sub_cancel_right, integral_llr_gaussianReal_gaussianReal hv₁ hv₂]

/-- The relative entropy between two real Gaussian distributions with the same nonzero variance
[LS, Theorem 14.1]: `D(𝒩(μ₁, v), 𝒩(μ₂, v)) = (μ₁ - μ₂) ^ 2 / (2 v)`. -/
theorem klDiv_gaussianReal_gaussianReal_same_var {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal μ₁ v) (gaussianReal μ₂ v) = ENNReal.ofReal ((μ₁ - μ₂) ^ 2 / (2 * v)) := by
  rw [klDiv_gaussianReal_gaussianReal hv hv]
  have hv' : (v : ℝ) ≠ 0 := by positivity
  congr 1
  rw [div_self hv', log_one]
  field_simp
  ring

end LMLExplore
