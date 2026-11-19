/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Row-stochastic matrices

Complements to `Mathlib.LinearAlgebra.Matrix.Stochastic`.

## Main statements

* `Matrix.sum_norm_row_of_mem_rowStochastic`: the rows of a real row-stochastic matrix have
  `ℓ¹`-norm `1`.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rows of a real row-stochastic matrix have `ℓ¹`-norm `1`, so results stated under the
hypothesis `∀ i, ∑ j, ‖P i j‖ ≤ 1` apply to it. -/
theorem sum_norm_row_of_mem_rowStochastic {P : Matrix n n ℝ} (hP : P ∈ rowStochastic ℝ n)
    (i : n) : ∑ j, ‖P i j‖ = 1 := by
  simp_rw [Real.norm_of_nonneg (nonneg_of_mem_rowStochastic hP)]
  exact sum_row_of_mem_rowStochastic hP i

end Matrix
