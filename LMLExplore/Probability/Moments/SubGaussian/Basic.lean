/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Moments.SubGaussian
public import LMLExplore.Probability.Kernel.Condexp

/-!
# Conditionally sub-Gaussian variables

If `X` is conditionally `c`-sub-Gaussian given a sub-σ-algebra `m`, the moment generating function
bound `E[exp (s X) | m] ≤ exp (c s² / 2)` also holds at an `m`-measurable random parameter `s`.
We state it in integrated form, against an arbitrary `m`-measurable weight `g ≥ 0`, which is the
form used to prove that exponential processes built from sub-Gaussian increments are
supermartingales.

A `c`-sub-Gaussian variable independent of `m` is conditionally `c`-sub-Gaussian given `m`. This
lets the martingale bounds for conditionally sub-Gaussian increments apply to sums of independent
sub-Gaussian variables.

## Main statements

* `ProbabilityTheory.HasCondSubgaussianMGF.lintegral_mul_exp_le`: for every `m`-measurable `s`
  and `m`-measurable `g ≥ 0`, `∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (c * s ^ 2 / 2)`.
* `ProbabilityTheory.HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep`: a `c`-sub-Gaussian
  variable independent of `m` is conditionally `c`-sub-Gaussian given `m`.

## References

* The proof is adapted from the formalization in the LMLPapers project
  (`LMLPapers/LeanMachineLearning/ForMathlib/Probability/Moments/SubGaussian.lean`).
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- **Conditional moment bound at a random parameter.** If `X` is measurable and conditionally
`c`-sub-Gaussian given `m`, then for every `m`-measurable `s` and `m`-measurable `g ≥ 0`,
`∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (c * s ^ 2 / 2)`. -/
theorem HasCondSubgaussianMGF.lintegral_mul_exp_le [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {hm : m ≤ mΩ} (h : HasCondSubgaussianMGF m hm X c μ) (hX : Measurable X) {s : Ω → ℝ}
    (hs : Measurable[m] s) {g : Ω → ℝ≥0∞} (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (s ω * X ω)) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (c * s ω ^ 2 / 2)) ∂μ := by
  have hΦ : Measurable
      (fun p : (ℝ≥0∞ × ℝ) × Ω ↦ p.1.1 * ENNReal.ofReal (Real.exp (p.1.2 * X p.2))) := by
    fun_prop
  rw [LMLExplore.lintegral_comp_condExpKernel hm (hg.prodMk hs) hΦ]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_of_ae_trim hm (Kernel.HasSubgaussianMGF.mgf_le h),
    ae_of_ae_trim hm (Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul h)] with ω hmgf hint
  rw [lintegral_const_mul _ (by fun_prop)]
  gcongr
  rw [← ofReal_integral_eq_lintegral_ofReal (hint (s ω))
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (hmgf (s ω))

/-- **Independence gives conditional sub-Gaussianity.** If `X` is measurable, `c`-sub-Gaussian and
independent of the sub-σ-algebra `m`, then `X` is conditionally `c`-sub-Gaussian given `m`. -/
theorem HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep [StandardBorelSpace Ω]
    [IsFiniteMeasure μ] {hm : m ≤ mΩ} (h : HasSubgaussianMGF X c μ) (hX : Measurable X)
    (h_indep : Indep (MeasurableSpace.comap X inferInstance) m μ) :
    HasCondSubgaussianMGF m hm X c μ := by
  refine Kernel.HasSubgaussianMGF.of_rat (fun t ↦ ?_) (fun q ↦ ?_)
  · rw [condExpKernel_comp_trim]
    exact h.integrable_exp_mul t
  -- the conditional moment generating function is the conditional expectation of `exp (q X)`,
  -- which is constant by independence
  have h_meas : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (fun ω ↦ Real.exp (q * X ω)) :=
    (measurable_const.mul (comap_measurable X)).exp.stronglyMeasurable
  have h_const : μ[fun ω ↦ Real.exp (q * X ω) | m]
      =ᵐ[μ.trim hm] fun _ ↦ μ[fun ω ↦ Real.exp (q * X ω)] :=
    StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp
      stronglyMeasurable_const (condExp_indep_eq hX.comap_le hm h_meas h_indep)
  filter_upwards [condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul q),
    h_const] with ω h_kernel h_const
  rw [mgf, ← h_kernel, h_const]
  exact h.mgf_le q

end ProbabilityTheory
