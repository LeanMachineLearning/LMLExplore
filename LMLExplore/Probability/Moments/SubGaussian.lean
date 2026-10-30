/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import LMLExplore.Probability.Kernel.Condexp

/-!
# Conditionally sub-Gaussian variables at a random parameter

If `X` is conditionally `c`-sub-Gaussian given a sub-σ-algebra `m`, the moment generating function
bound `E[exp (s X) | m] ≤ exp (c s² / 2)` also holds at an `m`-measurable random parameter `s`.
We state it in integrated form, against an arbitrary `m`-measurable weight `g ≥ 0`, which is the
form used to prove that exponential processes built from sub-Gaussian increments are
supermartingales.

## Main statements

* `ProbabilityTheory.HasCondSubgaussianMGF.lintegral_mul_exp_le`: for every `m`-measurable `s`
  and `m`-measurable `g ≥ 0`, `∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (c * s ^ 2 / 2)`.
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

end ProbabilityTheory
