/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Continuity of functions on the extended reals

A function on the extended real line `EReal` is continuous as soon as its restriction to the reals
is continuous and has limits at `+∞` and `-∞` equal to its values at `⊤` and `⊥`.

## Main statements

* `EReal.continuous_of_continuous_coe_of_tendsto`: the continuity criterion above.

## References

* The criterion is adapted from the Lean proof in
  `EValuesResearch/Results/SubGaussianCompleteClass.lean` and
  `EValuesResearch/Results/SubGaussianCompleteClassAux.lean` (commit `dd4072f`) of the paper
  project `RemyDegenne/evalues_research`.
-/

public section

open Filter Topology

namespace EReal

/-- A function on the extended real line is continuous when its restriction to the reals is
continuous, with limits at `+∞` and `-∞` equal to its values at `⊤` and `⊥`. -/
theorem continuous_of_continuous_coe_of_tendsto {Y : Type*} [TopologicalSpace Y] {G : EReal → Y}
    (hG : Continuous fun t : ℝ ↦ G t) (htop : Tendsto (fun t : ℝ ↦ G t) atTop (𝓝 (G ⊤)))
    (hbot : Tendsto (fun t : ℝ ↦ G t) atBot (𝓝 (G ⊥))) : Continuous G := by
  refine continuous_iff_continuousAt.2 fun l ↦ ?_
  induction l using EReal.rec with
  | bot =>
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, EReal.nhdsWithin_bot]
    exact tendsto_map'_iff.2 hbot
  | coe t => exact EReal.isOpenEmbedding_coe.continuousAt_iff.1 hG.continuousAt
  | top =>
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, EReal.nhdsWithin_top]
    exact tendsto_map'_iff.2 htop

end EReal
