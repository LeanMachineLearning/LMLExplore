/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# First-order optimality for convex functions

A function `f` convex on a convex set `s`, with derivative `f'` within `s` at `x ∈ s`, attains its
minimum over `s` at `x` if and only if `f' (y - x) ≥ 0` for every `y ∈ s` [LS, (26.2)]: the
derivative is a subgradient by convexity, and it is nonnegative along the directions of the
segments `[x, y] ⊆ s` at a minimum. This is how minimizers over a constraint set are recognized in
the analysis of Legendre functions, of Bregman projections and of follow the regularized leader.

## Main statements

* `ConvexOn.isMinOn_iff_forall_apply_sub_nonneg`: for `f` convex on `s` with derivative `f'`
  within `s` at `x ∈ s`, `x` minimizes `f` over `s` iff `0 ≤ f' (y - x)` for all `y ∈ s`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.5.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
  {f' : E →L[ℝ] ℝ} {x : E}

/-- **First-order optimality for convex functions** [LS, (26.2)]. If `f` is convex on `s` and has
derivative `f'` within `s` at `x ∈ s`, then `x` minimizes `f` over `s` if and only if
`0 ≤ f' (y - x)` for every `y ∈ s`. -/
theorem ConvexOn.isMinOn_iff_forall_apply_sub_nonneg (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hf' : HasFDerivWithinAt f f' s x) :
    IsMinOn f s x ↔ ∀ y ∈ s, 0 ≤ f' (y - x) := by
  refine ⟨fun h y hy ↦ h.isLocalMinOn.hasFDerivWithinAt_nonneg hf'
    (sub_mem_posTangentConeAt_of_segment_subset (hf.1.segment_subset hx hy)),
    fun h ↦ isMinOn_iff.2 fun y hy ↦ ?_⟩
  have := (hasSubgradientWithinAt_iff_le.1 (hf'.hasSubgradientWithinAt hf hx)) y hy
  linarith [h y hy]
