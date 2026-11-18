/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.OrderClosed

/-!
# Topological properties of stochastic matrices

The row-stochastic matrices, with nonnegative entries and row sums `1`, form a closed set of
matrices. A limit of stochastic matrices, such as the limit of the Cesàro means of the powers of a
stochastic matrix, is therefore stochastic.

## Main statements

* `Matrix.isClosed_rowStochastic`: the row-stochastic matrices form a closed set.
-/

public section

namespace Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
  [IsOrderedRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [OrderClosedTopology R]

/-- The row-stochastic matrices form a closed set. -/
theorem isClosed_rowStochastic : IsClosed (rowStochastic R n : Set (Matrix n n R)) := by
  have h₁ : IsClosed {M : Matrix n n R | ∀ i j, 0 ≤ M i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
      isClosed_le continuous_const (continuous_id.matrix_elem i j)
  have : (rowStochastic R n : Set (Matrix n n R)) =
      {M | ∀ i j, 0 ≤ M i j} ∩ {M | M *ᵥ 1 = 1} :=
    Set.ext fun _ ↦ mem_rowStochastic
  rw [this]
  exact h₁.inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)

end Matrix
