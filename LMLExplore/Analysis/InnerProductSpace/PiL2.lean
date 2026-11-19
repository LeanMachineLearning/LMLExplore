/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Euclidean norm as a dot product

On `ι → ℝ` the default norm is the sup norm, so a bound on the Euclidean norm of a vector `u` is
naturally stated through `u ⬝ᵥ u`. This file relates the norm of `toLp 2 u : EuclideanSpace ℝ ι`
to the dot product `u ⬝ᵥ u`.

## Main statements

* `EuclideanSpace.norm_toLp_sq`: `‖toLp 2 u‖ ^ 2 = u ⬝ᵥ u`.
* `EuclideanSpace.norm_toLp_le_abs_of_dotProduct_le_sq`: `u ⬝ᵥ u ≤ L ^ 2` implies
  `‖toLp 2 u‖ ≤ |L|`.
-/

public section

open WithLp

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm of `toLp 2 u` is `u ⬝ᵥ u`. -/
theorem norm_toLp_sq (u : ι → ℝ) : ‖(toLp 2 u : EuclideanSpace ℝ ι)‖ ^ 2 = u ⬝ᵥ u := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp

/-- A bound `u ⬝ᵥ u ≤ L ^ 2` is the bound `‖toLp 2 u‖ ≤ |L|` on the Euclidean norm. -/
theorem norm_toLp_le_abs_of_dotProduct_le_sq {u : ι → ℝ} {L : ℝ} (hu : u ⬝ᵥ u ≤ L ^ 2) :
    ‖(toLp 2 u : EuclideanSpace ℝ ι)‖ ≤ |L| := by
  rw [← abs_norm]
  exact sq_le_sq.1 (by rwa [norm_toLp_sq])

end EuclideanSpace
