/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Degrees of determinants of polynomial matrices

The determinant of a square matrix of polynomials whose `i`-th row has entries of degree at most
`d i` has degree at most `∑ i, d i`. This bounds the degrees of determinants and of adjugates of
polynomial matrices whose rows have different degrees, such as a matrix with one constant row.

## Main statements

* `Matrix.natDegree_det_le_sum`: `natDegree (det A) ≤ ∑ i, d i` when every entry of the `i`-th
  row of `A` has degree at most `d i`.
-/

public section

open Polynomial

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The determinant of a polynomial matrix whose `i`-th row has entries of degree at most `d i`
has degree at most `∑ i, d i`. -/
theorem natDegree_det_le_sum {A : Matrix n n R[X]} {d : n → ℕ}
    (h : ∀ i j, (A i j).natDegree ≤ d i) : A.det.natDegree ≤ ∑ i, d i := by
  rw [det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ ↦ ?_
  refine (natDegree_mul_le_of_le (natDegree_intCast _).le (natDegree_prod_le _ _)).trans ?_
  rw [zero_add, ← Equiv.sum_comp σ d]
  exact Finset.sum_le_sum fun i _ ↦ h (σ i) i

end Matrix
