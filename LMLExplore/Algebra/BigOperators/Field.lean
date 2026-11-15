/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.Defs

/-!
# Normalizing a finite combination over a semifield

A finite combination `∑ i ∈ T, w i • x i` with weights in a semifield of nonzero sum is that sum
times the combination with the normalized weights `w i / ∑ j ∈ T, w j`, which sum to `1`.

## Main statements

* `Finset.sum_smul_eq_smul_sum_div_smul`: a combination with weights of nonzero sum is that sum
  times the normalized combination.
-/

public section

/-- A combination with weights of nonzero sum is that sum times the convex combination of the same
points with the normalized weights. -/
lemma Finset.sum_smul_eq_smul_sum_div_smul {𝕜 E ι : Type*} [Semifield 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] {T : Finset ι} {x : ι → E} {w : ι → 𝕜} (hw : ∑ i ∈ T, w i ≠ 0) :
    ∑ i ∈ T, w i • x i = (∑ i ∈ T, w i) • ∑ i ∈ T, (w i / ∑ j ∈ T, w j) • x i := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [smul_smul, mul_div_cancel₀ _ hw]
