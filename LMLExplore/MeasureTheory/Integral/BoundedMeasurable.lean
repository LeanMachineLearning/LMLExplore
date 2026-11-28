/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Normed.Lp.Measurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Integrals of bounded measurable functions

A bounded measurable function `f : LMLExplore.boundedMeasurable β` is integrable against every
finite measure `μ`, and its integral is bounded in absolute value by `‖f‖ * μ univ`.

## Main statements

* `LMLExplore.boundedMeasurable.integrable`: a bounded measurable function is integrable for every
  finite measure.
* `LMLExplore.boundedMeasurable.abs_integral_le`: `|∫ y, f y ∂μ| ≤ ‖f‖ * μ.real univ`.
* `LMLExplore.integrable_of_abs_le`, `LMLExplore.abs_integral_le_of_abs_le`: the same statements
  for a function `f : β → ℝ` with `|f| ≤ B`, the second one against a probability measure.
* `LMLExplore.abs_integral_mixture_sub_le`: mixing a measure `F` with `Q`, with weights `1 - ε`
  and `ε`, brings its integral of `f` closer to that of `Q`.
* `LMLExplore.integrable_integral_kernel_of_abs_le`: for a Markov kernel `κ`, the integral
  `a ↦ ∫ f d(κ a)` of a measurable `f` with `|f| ≤ B` is integrable for every finite measure.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal lp

namespace LMLExplore

variable {β : Type*} [MeasurableSpace β]

/-- A measurable function bounded by `B` in absolute value is integrable for every finite
measure. -/
lemma integrable_of_abs_le {f : β → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B)
    (μ : Measure β) [IsFiniteMeasure μ] : Integrable f μ :=
  .of_bound hf.aestronglyMeasurable B (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hfB x))

/-- The integral against a probability measure of a function bounded by `B` in absolute value is
bounded by `B` in absolute value. -/
lemma abs_integral_le_of_abs_le {f : β → ℝ} {B : ℝ} {μ : Measure β} [IsProbabilityMeasure μ]
    (hfB : ∀ x, |f x| ≤ B) : |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f)
      (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hfB x))

/-- Mixing a measure `F` with `Q`, with weights `1 - ε` and `ε` for `ε ≤ 1`, brings its integral
of `f` closer to that of `Q`: if `|∫ f ∂F - ∫ f ∂Q| ≤ δ`, then
`|∫ f ∂((1 - ε) F + ε Q) - ∫ f ∂Q| ≤ δ`. -/
lemma abs_integral_mixture_sub_le {F Q : Measure β} {ε : ℝ≥0∞} (hε : ε ≤ 1) {f : β → ℝ}
    (hfF : Integrable f F) (hfQ : Integrable f Q) {δ : ℝ} (h : |∫ x, f x ∂F - ∫ x, f x ∂Q| ≤ δ) :
    |∫ x, f x ∂((1 - ε) • F + ε • Q) - ∫ x, f x ∂Q| ≤ δ := by
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε
  rw [integral_add_measure (hfF.smul_measure (by simp)) (hfQ.smul_measure hεt),
    integral_smul_measure, integral_smul_measure]
  have hsum : (1 - ε).toReal + ε.toReal = 1 := by
    rw [← ENNReal.toReal_add (by simp) hεt, tsub_add_cancel_of_le hε, ENNReal.toReal_one]
  have h1 : 0 ≤ (1 - ε).toReal := ENNReal.toReal_nonneg
  have h1' : (1 - ε).toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := ε)]
  have heq : (1 - ε).toReal • (∫ x, f x ∂F) + ε.toReal • (∫ x, f x ∂Q) - ∫ x, f x ∂Q =
      (1 - ε).toReal * (∫ x, f x ∂F - ∫ x, f x ∂Q) := by
    rw [smul_eq_mul, smul_eq_mul]
    linear_combination (∫ x, f x ∂Q) * hsum
  rw [heq, abs_mul, abs_of_nonneg h1]
  calc (1 - ε).toReal * |∫ x, f x ∂F - ∫ x, f x ∂Q|
  _ ≤ 1 * δ := mul_le_mul h1' h (abs_nonneg _) zero_le_one
  _ = δ := one_mul δ

/-- For a Markov kernel `κ` and a measurable function `f` bounded by `B` in absolute value, the
integral `a ↦ ∫ f d(κ a)` is integrable for every finite measure. -/
lemma integrable_integral_kernel_of_abs_le {α : Type*} [MeasurableSpace α] {f : β → ℝ} {B : ℝ}
    (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) (κ : Kernel α β) [IsMarkovKernel κ]
    (μ : Measure α) [IsFiniteMeasure μ] : Integrable (fun a ↦ ∫ x, f x ∂(κ a)) μ :=
  integrable_of_abs_le (hf.stronglyMeasurable.integral_kernel (κ := κ)).measurable
    (fun _ ↦ abs_integral_le_of_abs_le hfB) μ

namespace boundedMeasurable

/-- A bounded measurable function is integrable for every finite measure. -/
lemma integrable (f : boundedMeasurable β) (μ : Measure β) [IsFiniteMeasure μ] :
    Integrable (⇑(f : ℓ^∞(β, ℝ))) μ :=
  integrable_of_abs_le (measurable f) (abs_apply_le_norm f) μ

/-- The integral of a bounded measurable function `f` against a finite measure `μ` is at most
`‖f‖ * μ univ` in absolute value. -/
lemma abs_integral_le (f : boundedMeasurable β) {μ : Measure β} [IsFiniteMeasure μ] :
    |∫ y, (f : ℓ^∞(β, ℝ)) y ∂μ| ≤ ‖f‖ * μ.real univ := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (abs_apply_le_norm f y)

end boundedMeasurable

end LMLExplore
