/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Trace

/-!
# Square matrices as operators on Euclidean space

Mathlib's star algebra equivalence `Matrix.toEuclideanCLM` identifies a square matrix `A`
indexed by a finite type `n` with the continuous linear operator `v ↦ A *ᵥ v` on
`EuclideanSpace 𝕜 n`. This file records how it transports the objects of matrix analysis to those
of operator theory, so that results proved for operators on a finite-dimensional inner product
space specialize to matrices.

## Main statements

* `Matrix.toEuclideanCLM_vecMulVec`: the matrix `vecMulVec u (star v)` acts as the rank-one
  operator `rankOne 𝕜 u v`.
* `Matrix.toEuclideanCLM_inv`: the matrix inverse acts as the inverse operator (`Ring.inverse`,
  both being `0` for singular matrices).
* `Matrix.det_toEuclideanCLM`, `Matrix.trace_toEuclideanCLM`: determinant and trace are preserved.
* `Matrix.isPositive_toEuclideanCLM_iff`: `A` acts as a positive operator if and only if it is
  positive semidefinite.
* `Matrix.inner_ringInverse_toEuclideanCLM`: `⟪x, (A acting)⁻¹ y⟫ = x ⬝ᵥ A⁻¹ *ᵥ y`, the weighted
  inner products of least squares; `EuclideanSpace.norm_toLp_sq`: `‖u‖² = u ⬝ᵥ u`.
-/

public section

open WithLp
open scoped ComplexOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The matrix `vecMulVec u (star v)` acts on Euclidean space as the rank-one operator
`w ↦ ⟪v, w⟫ • u`. -/
@[simp]
theorem toEuclideanCLM_vecMulVec (u v : n → 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) (vecMulVec u (star v)) =
      InnerProductSpace.rankOne 𝕜 (toLp 2 u) (toLp 2 v) := by
  ext1 w
  apply (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).injective
  simp [vecMulVec_mulVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The inverse of a matrix acts as the inverse of its action; both are `0` for a singular
matrix. -/
@[simp]
theorem toEuclideanCLM_inv (A : Matrix n n 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) A⁻¹ = Ring.inverse (toEuclideanCLM (n := n) (𝕜 := 𝕜) A) := by
  rw [nonsing_inv_eq_ringInverse, map_ringInverse]

/-- The determinant of the action of a matrix on Euclidean space is its determinant. -/
@[simp]
theorem det_toEuclideanCLM (A : Matrix n n 𝕜) :
    LinearMap.det (toEuclideanCLM (n := n) (𝕜 := 𝕜) A :
      EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) = A.det := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]

/-- The trace of the action of a matrix on Euclidean space is its trace. -/
@[simp]
theorem trace_toEuclideanCLM (A : Matrix n n 𝕜) :
    LinearMap.trace 𝕜 _ (toEuclideanCLM (n := n) (𝕜 := 𝕜) A :
      EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) = A.trace := by
  rw [coe_toEuclideanCLM_eq_toEuclideanLin, toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.trace_eq_matrix_trace _ (EuclideanSpace.basisFun n 𝕜).toBasis,
    LinearMap.toMatrix_toLin]

/-- A matrix acts on Euclidean space as a positive operator if and only if it is positive
semidefinite. -/
@[simp]
theorem isPositive_toEuclideanCLM_iff {A : Matrix n n 𝕜} :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).IsPositive ↔ A.PosSemidef := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, coe_toEuclideanCLM_eq_toEuclideanLin,
    isPositive_toEuclideanLin_iff]

open scoped RealInnerProductSpace in
/-- The weighted inner product `x ⬝ᵥ A⁻¹ *ᵥ y` is the inner product of `x` with the inverse of the
action of `A` applied to `y`. -/
theorem inner_ringInverse_toEuclideanCLM (A : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    ⟪x, Ring.inverse (toEuclideanCLM (𝕜 := ℝ) A) y⟫ = x ⬝ᵥ A⁻¹ *ᵥ y := by
  rw [← toEuclideanCLM_inv, inner_toEuclideanCLM]

end Matrix

/-- The squared Euclidean norm of `toLp 2 u` is `u ⬝ᵥ u`. -/
theorem EuclideanSpace.norm_toLp_sq {n : Type*} [Fintype n] (u : n → ℝ) :
    ‖(toLp 2 u : EuclideanSpace ℝ n)‖ ^ 2 = u ⬝ᵥ u := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp
