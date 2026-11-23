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
* `MeasureTheory.setLIntegral_mul_le_setLIntegral_mul_of_forall_setLIntegral_le`,
  `MeasureTheory.setLIntegral_mul_eq_setLIntegral_mul_of_forall_setLIntegral_eq`: the same over an
  `m`-measurable set.
* `MeasureTheory.lintegral_withDensity_inv_eq_lintegral_div`: integrating against the measure of
  density `X⁻¹` is integrating `Y / X`.
* `MeasureTheory.lintegral_withDensity_comm`: integrating `f` against the measure of density `g`
  is integrating `g` against the measure of density `f`.
-/

public section

open Set
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

/-- If the set integrals of `f` are at most those of `g` over the `m`-measurable sets, then
`∫⁻ ω in s, Y ω * f ω ∂μ ≤ ∫⁻ ω in s, Y ω * g ω ∂μ` for every `m`-measurable `Y : Ω → ℝ≥0∞` and
`m`-measurable set `s`. -/
theorem setLIntegral_mul_le_setLIntegral_mul_of_forall_setLIntegral_le (hm : m ≤ mΩ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, f ω ∂μ ≤ ∫⁻ ω in s, g ω ∂μ)
    (hY : Measurable[m] Y) {s : Set Ω} (hs : MeasurableSet[m] s) :
    ∫⁻ ω in s, Y ω * f ω ∂μ ≤ ∫⁻ ω in s, Y ω * g ω ∂μ := by
  rw [← lintegral_indicator (hm s hs), ← lintegral_indicator (hm s hs)]
  simp_rw [indicator_mul_left]
  exact lintegral_mul_le_lintegral_mul_of_forall_setLIntegral_le hm hf hg h (hY.indicator hs)

/-- If the set integrals of `f` and `g` agree over the `m`-measurable sets, then
`∫⁻ ω in s, Y ω * f ω ∂μ = ∫⁻ ω in s, Y ω * g ω ∂μ` for every `m`-measurable `Y : Ω → ℝ≥0∞` and
`m`-measurable set `s`. -/
theorem setLIntegral_mul_eq_setLIntegral_mul_of_forall_setLIntegral_eq (hm : m ≤ mΩ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (h : ∀ s, MeasurableSet[m] s → ∫⁻ ω in s, f ω ∂μ = ∫⁻ ω in s, g ω ∂μ)
    (hY : Measurable[m] Y) {s : Set Ω} (hs : MeasurableSet[m] s) :
    ∫⁻ ω in s, Y ω * f ω ∂μ = ∫⁻ ω in s, Y ω * g ω ∂μ := by
  rw [← lintegral_indicator (hm s hs), ← lintegral_indicator (hm s hs)]
  simp_rw [indicator_mul_left]
  exact lintegral_mul_eq_lintegral_mul_of_forall_setLIntegral_eq hm hf hg h (hY.indicator hs)

/-- The integral of `Y` against the measure of density `X⁻¹` with respect to `μ` is the integral of
`Y / X` against `μ`. -/
theorem lintegral_withDensity_inv_eq_lintegral_div {X : Ω → ℝ≥0∞} (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) :
    ∫⁻ ω, Y ω ∂(μ.withDensity fun ω ↦ (X ω)⁻¹) = ∫⁻ ω, Y ω / X ω ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ (f := fun ω ↦ (X ω)⁻¹) hX.inv hY]
  simp_rw [Pi.mul_apply, mul_comm _ (Y _), ← div_eq_mul_inv]

/-- Integrating `f` against the measure of density `g` with respect to `μ` is integrating `g`
against the measure of density `f`: both are `∫⁻ ω, f ω * g ω ∂μ`. -/
theorem lintegral_withDensity_comm (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ ω, f ω ∂(μ.withDensity g) = ∫⁻ ω, g ω ∂(μ.withDensity f) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ hg hf, lintegral_withDensity_eq_lintegral_mul₀ hf hg,
    mul_comm]

end MeasureTheory
