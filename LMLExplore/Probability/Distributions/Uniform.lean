/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Integrating a derivative against the uniform law

Against Tau Ceti's uniform law `uniformMeasure a b` on `(a, b]`, the lower Lebesgue integral of a
nonnegative continuous derivative `f'` of `f` is the mean slope `(b - a)⁻¹ * (f b - f a)`, by the
fundamental theorem of calculus. The second form takes the uniform law between two distinct
points `a` and `b` in either order, `uniformMeasure (min a b) (max a b)`; the mean slope is
symmetric in `a` and `b`.

## Main statements

* `ProbabilityTheory.lintegral_ofReal_uniformMeasure_of_hasDerivAt`: for `a < b`,
  `∫⁻ x, ENNReal.ofReal (f' x) ∂uniformMeasure a b = ENNReal.ofReal ((b - a)⁻¹ * (f b - f a))`.
* `ProbabilityTheory.lintegral_ofReal_uniformMeasure_min_max_of_hasDerivAt`: the same for the
  uniform law between `a ≠ b`.
-/

public section

open MeasureTheory Set TauCeti.Probability

namespace ProbabilityTheory

variable {a b : ℝ} {f f' : ℝ → ℝ}

/-- **The integral of a derivative against the uniform law is the mean slope.** For `a < b` and a
function `f` with a continuous derivative `f'` on `[a, b]`, nonnegative on `(a, b]`, the integral
of `f'` against the uniform law on `(a, b]` is `(b - a)⁻¹ * (f b - f a)`. -/
theorem lintegral_ofReal_uniformMeasure_of_hasDerivAt (hab : a < b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (Icc a b))
    (hf'0 : ∀ x ∈ Ioc a b, 0 ≤ f' x) :
    ∫⁻ x, ENNReal.ofReal (f' x) ∂uniformMeasure a b =
      ENNReal.ofReal ((b - a)⁻¹ * (f b - f a)) := by
  rw [← uIcc_of_le hab.le] at hf hf'
  rw [uniformMeasure_eq_smul, lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal,
    ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hf hf'.intervalIntegrable, smul_eq_mul,
    ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hab),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_pos.mpr hab).le)]
  · rw [uIcc_of_le hab.le] at hf'
    exact hf'.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · exact ae_restrict_of_forall_mem measurableSet_Ioc hf'0

/-- **The integral of a derivative against the uniform law between two points.** For `a ≠ b` and
a function `f` with a continuous derivative `f'` on `uIcc a b`, nonnegative on `uIoc a b`, the
integral of `f'` against the uniform law between `a` and `b` is `(b - a)⁻¹ * (f b - f a)`. -/
theorem lintegral_ofReal_uniformMeasure_min_max_of_hasDerivAt (hab : a ≠ b)
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) (hf' : ContinuousOn f' (uIcc a b))
    (hf'0 : ∀ x ∈ uIoc a b, 0 ≤ f' x) :
    ∫⁻ x, ENNReal.ofReal (f' x) ∂uniformMeasure (min a b) (max a b) =
      ENNReal.ofReal ((b - a)⁻¹ * (f b - f a)) := by
  rcases hab.lt_or_gt with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    rw [uIcc_of_le h.le] at hf hf'
    rw [uIoc_of_le h.le] at hf'0
    exact lintegral_ofReal_uniformMeasure_of_hasDerivAt h hf hf' hf'0
  · rw [min_eq_right h.le, max_eq_left h.le, ← neg_sub a b, inv_neg, ← neg_sub (f a) (f b),
      neg_mul_neg]
    rw [uIcc_of_ge h.le] at hf hf'
    rw [uIoc_of_ge h.le] at hf'0
    exact lintegral_ofReal_uniformMeasure_of_hasDerivAt h hf hf' hf'0

end ProbabilityTheory
