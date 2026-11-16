/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Nearest points of complete convex sets

Mathlib's `exists_norm_eq_iInf_of_complete_convex` states that a nonempty complete convex set `K`
of a real inner product space has a point `v` nearest to any point `u`, in the form
`‖u - v‖ = ⨅ w : K, ‖u - w‖`. This file restates it as the existence of a minimizer over `K` of
the distance `x ↦ ‖x - u‖` (`IsMinOn`), the form in which projections onto `K` appear as steps of
projected gradient methods and as proximal steps of indicators.

## Main statements

* `exists_isMinOn_norm_sub_of_complete_convex`: a nonempty complete convex set has a point
  nearest to every point.
-/

public section

namespace LMLExplore

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {K : Set F}

/-- **Existence of nearest points.** In a real inner product space, a nonempty complete convex set
`K` (for instance a nonempty closed convex set of a Hilbert space) contains a point `v` nearest to
any point `u`: `v` minimizes `x ↦ ‖x - u‖` over `K`. -/
theorem exists_isMinOn_norm_sub_of_complete_convex (hK : K.Nonempty) (hKc : IsComplete K)
    (hKconv : Convex ℝ K) (u : F) : ∃ v ∈ K, IsMinOn (fun x ↦ ‖x - u‖) K v := by
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex hK hKc hKconv u
  refine ⟨v, hvK, isMinOn_iff.2 fun w hw ↦ ?_⟩
  rw [norm_sub_rev, hv, norm_sub_rev]
  exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩ (⟨w, hw⟩ : K)

end LMLExplore
