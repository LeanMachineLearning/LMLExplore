/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Comparing densities on a sub-σ-algebra

For a sub-σ-algebra `m` and two densities `f g : Ω → ℝ≥0∞`, the inequality
`∫⁻ ω in s, f ω ∂μ ≤ ∫⁻ ω in s, g ω ∂μ` for every `m`-measurable `s` says that `f` is at most `g`
"conditionally on `m`", with no integrability assumption and no conditional expectation. It is the
inequality `(μ.withDensity f).trim hm ≤ (μ.withDensity g).trim hm` between the restrictions of the
two measures with densities to `m`, and it extends from indicators to every `m`-measurable weight
`Y : Ω → ℝ≥0∞`: `∫⁻ Y * f ≤ ∫⁻ Y * g`. This is how a known factor is pulled out of a conditional
expectation in `ℝ≥0∞`, the step behind every bound on a product of a predictable factor and a
conditionally bounded increment.

## Main statements

* `MeasureTheory.withDensity_trim_le_withDensity_trim_iff`,
  `MeasureTheory.withDensity_trim_eq_withDensity_trim_iff`: the set-integral comparisons over the
  `m`-measurable sets are the comparisons of the trimmed measures with densities.
* `MeasureTheory.lintegral_mul_le_lintegral_mul_of_forall_setLIntegral_le`,
  `MeasureTheory.lintegral_mul_eq_lintegral_mul_of_forall_setLIntegral_eq`: they extend to
  `m`-measurable weights.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g Y : Ω → ℝ≥0∞}

/-- The restrictions to a sub-σ-algebra `m` of `μ.withDensity f` and `μ.withDensity g` compare
exactly when the set integrals of `f` and `g` over the `m`-measurable sets do. -/
theorem withDensity_trim_le_withDensity_trim_iff (hm : m ≤ mΩ) :
    (μ.withDensity f).trim hm ≤ (μ.withDensity g).trim hm ↔
      ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, f ω ∂μ ≤ ∫⁻ ω in s, g ω ∂μ := by
  refine (@Measure.le_iff Ω m _ _).trans (forall₂_congr fun s hs ↦ ?_)
  rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs),
    withDensity_apply _ (hm s hs)]

/-- The restrictions to a sub-σ-algebra `m` of `μ.withDensity f` and `μ.withDensity g` are equal
exactly when the set integrals of `f` and `g` over the `m`-measurable sets are. -/
theorem withDensity_trim_eq_withDensity_trim_iff (hm : m ≤ mΩ) :
    (μ.withDensity f).trim hm = (μ.withDensity g).trim hm ↔
      ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, f ω ∂μ = ∫⁻ ω in s, g ω ∂μ := by
  refine (@Measure.ext_iff Ω m _ _).trans (forall₂_congr fun s hs ↦ ?_)
  rw [trim_measurableSet_eq hm hs, trim_measurableSet_eq hm hs, withDensity_apply _ (hm s hs),
    withDensity_apply _ (hm s hs)]

/-- The integral of `Y * f` against an `m`-measurable weight `Y` is the integral of `Y` against the
restriction of `μ.withDensity f` to `m`. -/
theorem lintegral_mul_eq_lintegral_trim_withDensity (hm : m ≤ mΩ) (hf : AEMeasurable f μ)
    (hY : Measurable[m] Y) :
    ∫⁻ ω, Y ω * f ω ∂μ = ∫⁻ ω, Y ω ∂(μ.withDensity f).trim hm := by
  rw [lintegral_trim hm hY, lintegral_withDensity_eq_lintegral_mul₀ hf
    (hY.mono hm le_rfl).aemeasurable]
  simp_rw [Pi.mul_apply, mul_comm]

/-- If the set integrals of `f` are at most those of `g` over the `m`-measurable sets, then
`∫⁻ Y * f ≤ ∫⁻ Y * g` for every `m`-measurable `Y : Ω → ℝ≥0∞`: the factor `Y`, known given `m`,
can be pulled out. -/
theorem lintegral_mul_le_lintegral_mul_of_forall_setLIntegral_le (hm : m ≤ mΩ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, f ω ∂μ ≤ ∫⁻ ω in s, g ω ∂μ)
    (hY : Measurable[m] Y) :
    ∫⁻ ω, Y ω * f ω ∂μ ≤ ∫⁻ ω, Y ω * g ω ∂μ := by
  rw [lintegral_mul_eq_lintegral_trim_withDensity hm hf hY,
    lintegral_mul_eq_lintegral_trim_withDensity hm hg hY]
  exact lintegral_mono' ((withDensity_trim_le_withDensity_trim_iff hm).2 h) le_rfl

/-- If the set integrals of `f` and `g` agree over the `m`-measurable sets, then
`∫⁻ Y * f = ∫⁻ Y * g` for every `m`-measurable `Y : Ω → ℝ≥0∞`. -/
theorem lintegral_mul_eq_lintegral_mul_of_forall_setLIntegral_eq (hm : m ≤ mΩ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, f ω ∂μ = ∫⁻ ω in s, g ω ∂μ)
    (hY : Measurable[m] Y) :
    ∫⁻ ω, Y ω * f ω ∂μ = ∫⁻ ω, Y ω * g ω ∂μ := by
  rw [lintegral_mul_eq_lintegral_trim_withDensity hm hf hY,
    lintegral_mul_eq_lintegral_trim_withDensity hm hg hY,
    (withDensity_trim_eq_withDensity_trim_iff hm).2 h]

end MeasureTheory
