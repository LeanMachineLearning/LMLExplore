/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Signs of conditional expectations from set integrals

Let `m` be a sub-σ-algebra and `f` an integrable real function. If `∫ x in s, f x ∂μ ≤ 0` for
every `m`-measurable set `s`, then the conditional expectation `μ[f | m]` is nonpositive almost
everywhere, and so `∫ x, h x * f x ∂μ ≤ 0` for every nonnegative `m`-measurable weight `h` such that
`h * f` is integrable: the set integrals over `m`-measurable sets are the integrals against
indicators, and the inequality extends to all such weights. If the set integrals vanish, so does
the conditional expectation, and `∫ x, h x * f x ∂μ = 0` for every `m`-measurable `h` with
`h * f` integrable, of either sign.

## Main statements

* `LMLExplore.condExp_nonpos_of_forall_setIntegral_nonpos`,
  `LMLExplore.condExp_ae_eq_zero_of_forall_setIntegral_eq_zero`: the conditional expectation is
  nonpositive, or zero, when the set integrals over `m`-measurable sets are.
* `LMLExplore.integral_mul_nonpos_of_forall_setIntegral_nonpos`,
  `LMLExplore.integral_mul_eq_zero_of_forall_setIntegral_eq_zero`: the integrals against
  almost everywhere `m`-measurable weights.
-/

public section

open MeasureTheory

namespace LMLExplore

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f h : Ω → ℝ}

/-- If the integral of `f` over every `m`-measurable set is nonpositive, then so is the conditional
expectation of `f` given `m`, almost everywhere. -/
theorem condExp_nonpos_of_forall_setIntegral_nonpos (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) (hfs : ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂μ ≤ 0) :
    μ[f | m] ≤ᵐ[μ] 0 := by
  have h := ae_nonneg_of_forall_setIntegral_nonneg (μ := μ.trim hm) (f := -μ[f | m])
    (integrable_condExp.neg.trim hm stronglyMeasurable_condExp.neg) fun s hs _ ↦ by
      rw [← setIntegral_trim hm stronglyMeasurable_condExp.neg hs, Pi.neg_def, integral_neg,
        setIntegral_condExp hm hf hs, neg_nonneg]
      exact hfs s hs
  filter_upwards [ae_of_ae_trim hm h] with x hx
  simpa using hx

/-- If the integral of `f` over every `m`-measurable set vanishes, then so does the conditional
expectation of `f` given `m`, almost everywhere. -/
theorem condExp_ae_eq_zero_of_forall_setIntegral_eq_zero (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) (hfs : ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂μ = 0) :
    μ[f | m] =ᵐ[μ] 0 :=
  (ae_eq_condExp_of_forall_setIntegral_eq hm hf (fun _ _ _ ↦ integrableOn_zero)
    (fun s hs _ ↦ by simp [hfs s hs]) aestronglyMeasurable_zero).symm

/-- If the integral of `f` over every `m`-measurable set is nonpositive, then
`∫ x, h x * f x ∂μ ≤ 0` for every almost everywhere nonnegative and almost everywhere
`m`-measurable `h` such that `h * f` is integrable. -/
theorem integral_mul_nonpos_of_forall_setIntegral_nonpos (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) (hfs : ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂μ ≤ 0)
    (hh : AEStronglyMeasurable[m] h μ) (hh_nonneg : 0 ≤ᵐ[μ] h)
    (hhf : Integrable (fun x ↦ h x * f x) μ) : ∫ x, h x * f x ∂μ ≤ 0 := by
  rw [← integral_condExp hm]
  refine integral_nonpos_of_ae ?_
  filter_upwards [condExp_mul_of_aestronglyMeasurable_left hh hhf hf,
    condExp_nonpos_of_forall_setIntegral_nonpos hm hf hfs, hh_nonneg] with x hx hfx hhx
  simp only [Pi.mul_def] at hx
  rw [hx]
  exact mul_nonpos_of_nonneg_of_nonpos hhx hfx

/-- If the integral of `f` over every `m`-measurable set vanishes, then `∫ x, h x * f x ∂μ = 0`
for every almost everywhere `m`-measurable `h` such that `h * f` is integrable. -/
theorem integral_mul_eq_zero_of_forall_setIntegral_eq_zero (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hfs : ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂μ = 0) (hh : AEStronglyMeasurable[m] h μ)
    (hhf : Integrable (fun x ↦ h x * f x) μ) : ∫ x, h x * f x ∂μ = 0 := by
  rw [← integral_condExp hm]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [condExp_mul_of_aestronglyMeasurable_left hh hhf hf,
    condExp_ae_eq_zero_of_forall_setIntegral_eq_zero hm hf hfs] with x hx hfx
  simp only [Pi.mul_def] at hx
  rw [hx]
  simp [hfx]

end LMLExplore
