/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
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

When the variance of the second law is free, as in the model of Gaussian arms with unknown
variances, the relevant quantity is the smallest relative entropy from `𝒩(μ₁, v₁)` to a Gaussian
law of mean `μ₂`. Since `log x ≤ x - 1`, the closed form is at least
`log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2`, with equality for the variance `v₂ = v₁ + (μ₁ - μ₂) ^ 2`; the
degenerate law `𝒩(μ₂, 0)`, a Dirac mass, is at infinite relative entropy. Hence
`inf_{v₂} D(𝒩(μ₁, v₁), 𝒩(μ₂, v₂)) = log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2` [JDK23, proof of Lemma 11].

## Main statements

* `LMLExplore.llr_gaussianReal_gaussianReal`: the log-likelihood ratio, almost everywhere.
* `LMLExplore.klDiv_gaussianReal_gaussianReal`: the relative entropy for arbitrary variances.
* `LMLExplore.klDiv_gaussianReal_gaussianReal_same_var`: the relative entropy for equal variances.
* `LMLExplore.klDiv_gaussianReal_gaussianReal_zero`: the relative entropy to a Dirac mass `𝒩(μ₂, 0)`
  is infinite.
* `LMLExplore.continuousOn_klDiv_gaussianReal`: the relative entropy is continuous in the means and
  the variances of the two laws, on the laws of nonzero variance.
* `LMLExplore.ofReal_log_one_add_div_le_klDiv_gaussianReal`,
  `LMLExplore.klDiv_gaussianReal_gaussianReal_add_sq`: the relative entropy from `𝒩(μ₁, v₁)` to a
  Gaussian law of mean `μ₂` is at least `log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2`, with equality for the
  variance `v₁ + (μ₁ - μ₂) ^ 2`.
* `LMLExplore.iInf_klDiv_gaussianReal_gaussianReal`: the infimum over the variance of the second
  law, `inf_{v₂} D(𝒩(μ₁, v₁), 𝒩(μ₂, v₂)) = log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2`.

## References

* [JDK23] M. Jourdan, R. Degenne and E. Kaufmann, *Dealing with unknown variances in best-arm
  identification*, ALT 2023, Appendix C.1, proof of Lemma 11.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real

open scoped ENNReal NNReal

namespace LMLExplore

variable {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0}

/-- The log-likelihood ratio of `𝒩(μ₁, v₁)` with respect to `𝒩(μ₂, v₂)` is, Lebesgue-almost
everywhere, the quadratic polynomial
`log (v₂ / v₁) / 2 + (x - μ₂) ^ 2 / (2 v₂) - (x - μ₁) ^ 2 / (2 v₁)`. -/
lemma llr_gaussianReal_gaussianReal (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    llr (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂) =ᵐ[volume] fun x ↦
      log (v₂ / v₁) / 2 + (x - μ₂) ^ 2 / (2 * v₂) - (x - μ₁) ^ 2 / (2 * v₁) := by
  filter_upwards [rnDeriv_gaussianReal_gaussianReal μ₁ v₁ μ₂ hv₂] with x hx
  have hv₁' : (0 : ℝ) < v₁ := by positivity
  have hv₂' : (0 : ℝ) < v₂ := by positivity
  have h₁ := gaussianPDFReal_pos μ₁ v₁ x hv₁
  have h₂ := gaussianPDFReal_pos μ₂ v₂ x hv₂
  simp [llr_def, hx, ENNReal.toReal_mul, toReal_gaussianPDF, log_mul, log_div,
    log_gaussianPDFReal hv₁, log_gaussianPDFReal hv₂, h₁.ne', h₂.ne', hv₁'.ne', hv₂'.ne',
    pi_ne_zero]
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

/-- The relative entropy between real Gaussian distributions is continuous in the means and the
variances of the two laws, on the pairs of laws of nonzero variance. -/
theorem continuousOn_klDiv_gaussianReal :
    ContinuousOn (fun q : (ℝ × ℝ≥0) × (ℝ × ℝ≥0) ↦
        klDiv (gaussianReal q.1.1 q.1.2) (gaussianReal q.2.1 q.2.2))
      ({p | p.2 ≠ 0} ×ˢ {p | p.2 ≠ 0}) := by
  have h₁ : ∀ q ∈ ({p : ℝ × ℝ≥0 | p.2 ≠ 0} ×ˢ {p : ℝ × ℝ≥0 | p.2 ≠ 0}), (q.1.2 : ℝ) ≠ 0 :=
    fun q hq ↦ NNReal.coe_ne_zero.2 hq.1
  have h₂ : ∀ q ∈ ({p : ℝ × ℝ≥0 | p.2 ≠ 0} ×ˢ {p : ℝ × ℝ≥0 | p.2 ≠ 0}), (q.2.2 : ℝ) ≠ 0 :=
    fun q hq ↦ NNReal.coe_ne_zero.2 hq.2
  have hc₁ : Continuous fun q : (ℝ × ℝ≥0) × (ℝ × ℝ≥0) ↦ (q.1.2 : ℝ) := by fun_prop
  have hc₂ : Continuous fun q : (ℝ × ℝ≥0) × (ℝ × ℝ≥0) ↦ (q.2.2 : ℝ) := by fun_prop
  have hc : Continuous fun q : (ℝ × ℝ≥0) × (ℝ × ℝ≥0) ↦ (q.1.2 : ℝ) + (q.1.1 - q.2.1) ^ 2 := by
    fun_prop
  refine (ENNReal.continuous_ofReal.comp_continuousOn
    (((((hc₂.continuousOn.div hc₁.continuousOn h₁).log fun q hq ↦
      div_ne_zero (h₂ q hq) (h₁ q hq)).add (hc.continuousOn.div hc₂.continuousOn h₂)).sub
        (continuousOn_const (c := (1 : ℝ)))).div_const 2)).congr fun q hq ↦ ?_
  exact klDiv_gaussianReal_gaussianReal hq.1 hq.2

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

/-- The relative entropy from a nondegenerate Gaussian law to the Dirac mass `𝒩(μ₂, 0)` is
infinite: the Gaussian law is not absolutely continuous with respect to it. -/
theorem klDiv_gaussianReal_gaussianReal_zero (hv₁ : v₁ ≠ 0) :
    klDiv (gaussianReal μ₁ v₁) (gaussianReal μ₂ 0) = ∞ := by
  refine klDiv_of_not_ac fun h ↦ ?_
  have := nullSingletonClass_gaussianReal (μ := μ₁) hv₁
  have h_compl : gaussianReal μ₁ v₁ {μ₂}ᶜ = 0 := h (by simp)
  rw [measure_compl (measurableSet_singleton μ₂) (measure_ne_top _ _), measure_univ,
    measure_singleton, tsub_zero] at h_compl
  exact one_ne_zero h_compl

/-- The relative entropy from `𝒩(μ₁, v₁)` to a Gaussian law of mean `μ₂`, whatever its variance,
is at least `log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2`. -/
theorem ofReal_log_one_add_div_le_klDiv_gaussianReal (hv₁ : v₁ ≠ 0) (v₂ : ℝ≥0) :
    ENNReal.ofReal (log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2) ≤
      klDiv (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂) := by
  rcases eq_or_ne v₂ 0 with rfl | hv₂
  · rw [klDiv_gaussianReal_gaussianReal_zero hv₁]
    exact le_top
  rw [klDiv_gaussianReal_gaussianReal hv₁ hv₂]
  refine ENNReal.ofReal_le_ofReal ?_
  have hv₁' : (0 : ℝ) < v₁ := by positivity
  have hv₂' : (0 : ℝ) < v₂ := by positivity
  have hc : 0 < (v₁ : ℝ) + (μ₁ - μ₂) ^ 2 := by positivity
  have h_log := log_le_sub_one_of_pos (div_pos hc hv₂')
  have h_eq : 1 + (μ₁ - μ₂) ^ 2 / v₁ = ((v₁ + (μ₁ - μ₂) ^ 2) / v₂) * (v₂ / v₁) := by
    field_simp
  rw [h_eq, log_mul (div_pos hc hv₂').ne' (div_pos hv₂' hv₁').ne']
  linarith

/-- The relative entropy from `𝒩(μ₁, v₁)` to the Gaussian law of mean `μ₂` and variance
`v₁ + (μ₁ - μ₂) ^ 2` is `log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2`: this variance attains the lower bound
`LMLExplore.ofReal_log_one_add_div_le_klDiv_gaussianReal`. -/
theorem klDiv_gaussianReal_gaussianReal_add_sq (hv₁ : v₁ ≠ 0) :
    klDiv (gaussianReal μ₁ v₁) (gaussianReal μ₂ (v₁ + ((μ₁ - μ₂) ^ 2).toNNReal)) =
      ENNReal.ofReal (log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2) := by
  have hv₁' : (0 : ℝ) < v₁ := by positivity
  have hc : 0 < (v₁ : ℝ) + (μ₁ - μ₂) ^ 2 := by positivity
  have hv₂ : v₁ + ((μ₁ - μ₂) ^ 2).toNNReal ≠ 0 := by
    rw [← NNReal.coe_ne_zero, NNReal.coe_add, Real.coe_toNNReal _ (sq_nonneg _)]
    exact hc.ne'
  rw [klDiv_gaussianReal_gaussianReal hv₁ hv₂, NNReal.coe_add, Real.coe_toNNReal _ (sq_nonneg _),
    div_self hc.ne', add_div, div_self hv₁'.ne']
  ring_nf

/-- The smallest relative entropy from `𝒩(μ₁, v₁)` to a Gaussian law of mean `μ₂`:
`inf_{v₂} D(𝒩(μ₁, v₁), 𝒩(μ₂, v₂)) = log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2` [JDK23, proof of Lemma 11],
attained at the variance `v₁ + (μ₁ - μ₂) ^ 2`. -/
theorem iInf_klDiv_gaussianReal_gaussianReal (hv₁ : v₁ ≠ 0) (μ₂ : ℝ) :
    ⨅ v₂ : ℝ≥0, klDiv (gaussianReal μ₁ v₁) (gaussianReal μ₂ v₂) =
      ENNReal.ofReal (log (1 + (μ₁ - μ₂) ^ 2 / v₁) / 2) :=
  le_antisymm ((iInf_le _ _).trans (klDiv_gaussianReal_gaussianReal_add_sq hv₁).le)
    (le_iInf fun v₂ ↦ ofReal_log_one_add_div_le_klDiv_gaussianReal hv₁ v₂)

end LMLExplore
