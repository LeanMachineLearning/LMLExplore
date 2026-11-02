/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Iterates of a contraction converge to a given fixed point

## Main statements

* `ContractingWith.tendsto_iterate_of_isFixedPt`: the iterates of a contraction converge to a given
  fixed point of it, without assuming completeness.
-/

public section

open Function Filter Topology NNReal

/-- The iterates of a contraction at any point converge to a fixed point of it. Unlike
`ContractingWith.tendsto_iterate_fixedPoint`, this does not assume completeness, since the fixed
point is given. -/
theorem ContractingWith.tendsto_iterate_of_isFixedPt {α : Type*} [MetricSpace α] {K : ℝ≥0}
    {f : α → α} (hf : ContractingWith K f) {y : α} (hy : IsFixedPt f y) (x : α) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) := by
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one K.coe_nonneg hf.1).mul_const (dist x y)))
  simpa [iterate_fixed hy] using (hf.toLipschitzWith.iterate n).dist_le_mul x y
