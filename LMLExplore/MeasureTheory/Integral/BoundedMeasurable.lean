/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Normed.Lp.Measurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrals of bounded measurable functions

A bounded measurable function `f : LMLExplore.boundedMeasurable β` is integrable against every
finite measure `μ`, and its integral is bounded in absolute value by `‖f‖ * μ univ`.

## Main statements

* `LMLExplore.boundedMeasurable.integrable`: a bounded measurable function is integrable for every
  finite measure.
* `LMLExplore.boundedMeasurable.abs_integral_le`: `|∫ y, f y ∂μ| ≤ ‖f‖ * μ.real univ`.
-/

public section

open MeasureTheory Set
open scoped ENNReal lp

namespace LMLExplore.boundedMeasurable

variable {β : Type*} [MeasurableSpace β]

/-- A bounded measurable function is integrable for every finite measure. -/
lemma integrable (f : boundedMeasurable β) (μ : Measure β) [IsFiniteMeasure μ] :
    Integrable (⇑(f : ℓ^∞(β, ℝ))) μ :=
  .of_bound (measurable f).aestronglyMeasurable ‖f‖ <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (abs_apply_le_norm f y)

/-- The integral of a bounded measurable function `f` against a finite measure `μ` is at most
`‖f‖ * μ univ` in absolute value. -/
lemma abs_integral_le (f : boundedMeasurable β) {μ : Measure β} [IsFiniteMeasure μ] :
    |∫ y, (f : ℓ^∞(β, ℝ)) y ∂μ| ≤ ‖f‖ * μ.real univ := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (abs_apply_le_norm f y)

end LMLExplore.boundedMeasurable
