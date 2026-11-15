/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Measures of the closed balls of integer radius

In a pseudometric space, the closed balls `closedBall x M`, `M : ℕ`, increase to the whole space,
so every measure gives them a mass tending to the mass of the space: a finite measure gives one of
them a mass more than `μ univ - δ`, for every `δ ≠ 0`, in the form
`μ univ < μ (closedBall x M) + δ` (true also for the zero measure).

## Main statements

* `MeasureTheory.tendsto_measure_closedBall_nat`: `μ (closedBall x M) → μ univ` as `M → ∞`.
* `MeasureTheory.exists_measure_univ_lt_measure_closedBall_add`: a finite measure gives a mass
  more than `μ univ - δ` to some closed ball `closedBall x M`, `M : ℕ`.
-/

public section

open Set Filter Metric

open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]

/-- The mass of the closed balls `closedBall x M`, `M : ℕ`, tends to the mass of the space. -/
lemma tendsto_measure_closedBall_nat (μ : Measure α) (x : α) :
    Tendsto (fun M : ℕ ↦ μ (closedBall x M)) atTop (𝓝 (μ univ)) := by
  rw [← iUnion_closedBall_nat x]
  exact tendsto_measure_iUnion_atTop fun m n hmn ↦ closedBall_subset_closedBall (by simpa)

/-- A finite measure gives a mass more than `μ univ - δ` to some closed ball `closedBall x M`,
`M : ℕ`, for every `δ ≠ 0`: `μ univ < μ (closedBall x M) + δ`. -/
lemma exists_measure_univ_lt_measure_closedBall_add (μ : Measure α) [IsFiniteMeasure μ] (x : α)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) : ∃ M : ℕ, μ univ < μ (closedBall x M) + δ :=
  (((tendsto_measure_closedBall_nat μ x).add tendsto_const_nhds).eventually
    (lt_mem_nhds (ENNReal.lt_add_right (measure_ne_top μ univ) hδ))).exists

end MeasureTheory
