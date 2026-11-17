/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Coercive operators are invertible

A continuous linear operator `A` on a real Hilbert space is *coercive* when
`c ‖v‖² ≤ ⟪A v, v⟫` for some `c > 0` and every `v`; the operator need not be symmetric. By the
Lax–Milgram theorem (Mathlib's `IsCoercive.continuousLinearEquivOfBilin`, applied to the bilinear
form `(v, w) ↦ ⟪A v, w⟫`), such an operator is invertible. This is how the linear systems of
least squares and of temporal-difference learning, whose operators are coercive but not
necessarily symmetric, are seen to have unique solutions.

## Main statements

* `ContinuousLinearMap.isInvertible_of_mul_norm_sq_le_inner`: a coercive operator is
  invertible.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- **Lax–Milgram for operators**: a continuous linear operator `A` on a real Hilbert space with
`c ‖v‖² ≤ ⟪A v, v⟫` for some `c > 0` is invertible. -/
theorem isInvertible_of_mul_norm_sq_le_inner {A : V →L[ℝ] V} {c : ℝ} (hc : 0 < c)
    (h : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪A v, v⟫_ℝ) : A.IsInvertible := by
  have hB : IsCoercive ((innerSL ℝ).comp A) :=
    ⟨c, hc, fun v ↦ by simpa [sq, mul_assoc] using h v⟩
  refine ⟨hB.continuousLinearEquivOfBilin, ContinuousLinearMap.ext fun v ↦ ?_⟩
  refine ext_inner_right ℝ fun w ↦ ?_
  simp

end ContinuousLinearMap
