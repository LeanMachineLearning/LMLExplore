/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.UniformSpace.Real

/-!
# Topological lemmas about the nonnegative reals

## Main statements

* `NNReal.tendsto_coe_nhdsLT`: the coercion `ℝ≥0 → ℝ` maps left neighbourhoods of `x` to left
  neighbourhoods of `x`. It turns limits `γ ↑ 1` over real numbers into limits over discount
  factors `γ : ℝ≥0`.
-/

public section

open Filter Topology

namespace NNReal

/-- The coercion `ℝ≥0 → ℝ` maps left neighbourhoods of `x` to left neighbourhoods of `x`. -/
theorem tendsto_coe_nhdsLT (x : ℝ≥0) : Tendsto ((↑) : ℝ≥0 → ℝ) (𝓝[<] x) (𝓝[<] (x : ℝ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (continuous_coe.tendsto x |>.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun _ hy ↦ coe_lt_coe.2 hy)

end NNReal
