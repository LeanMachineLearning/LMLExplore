/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measures of intervals

The mass that a finite measure gives to the open rays `Ioi x` tends to `0` as `x → ∞`, the
counterpart for upper tails of Mathlib's `MeasureTheory.tendsto_measure_Iic_atTop`.

## Main statements

* `MeasureTheory.tendsto_measure_Ioi_atTop`: `μ (Ioi x) → 0` as `x → ∞`, for a finite measure.
-/

public section

open Set Filter
open scoped Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} [LinearOrder α] [TopologicalSpace α]
  [ClosedIicTopology α] [OpensMeasurableSpace α]

/-- A finite measure gives to the open rays `Ioi x` a mass that tends to `0` as `x → ∞`. -/
theorem tendsto_measure_Ioi_atTop [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) [IsFiniteMeasure μ] : Tendsto (fun x ↦ μ (Ioi x)) atTop (𝓝 0) := by
  refine .of_neBot_imp fun hne ↦ ?_
  obtain ⟨x₀⟩ := (atTop_neBot_iff.1 hne).1
  have h := tendsto_measure_iInter_atTop (μ := μ) (fun x ↦ measurableSet_Ioi.nullMeasurableSet)
    antitone_Ioi ⟨x₀, measure_ne_top _ _⟩
  rwa [iInter_eq_empty_iff.2 fun x ↦ ⟨x, lt_irrefl x⟩, measure_empty] at h

end MeasureTheory
