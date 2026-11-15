/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Events of a pair of independent random variables

For random variables `X` and `Y` that are independent under a finite measure `μ`, the joint law of
`(X, Y)` is the product of the laws (`ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map`). By
Tonelli's theorem, the probability of an event `{(X, Y) ∈ s}` is then obtained by freezing the
value of `Y` and integrating the probability of the resulting event of `X` against the law of
`Y`. This computes the probability of the events of a randomized test, which compare a test
statistic with an independent source of randomness.

## Main statements

* `ProbabilityTheory.IndepFun.measure_prodMk_mem_eq_lintegral`: for independent `X` and `Y`,
  `μ {ω | (X ω, Y ω) ∈ s} = ∫⁻ ω, μ {ω' | (X ω', Y ω) ∈ s} ∂μ`.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {X : Ω → α} {Y : Ω → β}

/-- **Freezing an independent variable**: for random variables `X` and `Y` that are independent
under a finite measure `μ`, the probability of an event `{(X, Y) ∈ s}` is the integral over the
values of `Y` of the probability of the event of `X` obtained by fixing `Y`. -/
theorem IndepFun.measure_prodMk_mem_eq_lintegral [IsFiniteMeasure μ] (hXY : IndepFun X Y μ)
    (hX : Measurable X) (hY : Measurable Y) {s : Set (α × β)} (hs : MeasurableSet s) :
    μ {ω | (X ω, Y ω) ∈ s} = ∫⁻ ω, μ {ω' | (X ω', Y ω) ∈ s} ∂μ := by
  have h_map : μ {ω | (X ω, Y ω) ∈ s} = (μ.map X).prod (μ.map Y) s := by
    rw [← hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
      Measure.map_apply (hX.prodMk hY) hs]
    rfl
  rw [h_map, Measure.prod_apply_symm hs,
    lintegral_map (measurable_measure_prodMk_right hs) hY]
  refine lintegral_congr fun ω ↦ ?_
  rw [Measure.map_apply hX (measurable_prodMk_right hs)]
  rfl

end ProbabilityTheory
