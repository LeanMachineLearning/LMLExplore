/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Rank-one updates of operators

For vectors `u v` of an inner product space, `rankOne 𝕜 u v` is the operator `w ↦ ⟪v, w⟫ • u`.
We compute the determinant and, for symmetric operators, the inverse of a rank-one update
`V + rankOne 𝕜 u v` of an invertible operator `V`, in terms of `V⁻¹ = Ring.inverse V`.

## Main statements

* `LMLExplore.det_one_add_rankOne`: the **matrix determinant lemma**
  `det (1 + rankOne 𝕜 u v) = 1 + ⟪v, u⟫`, in finite dimension.
* `LMLExplore.det_add_rankOne`: for invertible `V`,
  `det (V + rankOne 𝕜 u v) = det V * (1 + ⟪v, V⁻¹ u⟫)`.
* `LMLExplore.isUnit_add_rankOne`: for a symmetric invertible `V` with `1 + ⟪v, V⁻¹ u⟫ ≠ 0`,
  `V + rankOne 𝕜 u v` is invertible.
* `LMLExplore.ringInverse_add_rankOne`: the **Sherman–Morrison formula** for a symmetric
  invertible `V`: `(V + rankOne 𝕜 u v)⁻¹ = V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • rankOne 𝕜 (V⁻¹ u) (V⁻¹ v)`,
  whenever `1 + ⟪v, V⁻¹ u⟫ ≠ 0`.
-/

public section

open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace

namespace LMLExplore

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Matrix determinant lemma**: in finite dimension, `det (1 + rankOne 𝕜 u v) = 1 + ⟪v, u⟫`. -/
theorem det_one_add_rankOne [FiniteDimensional 𝕜 E] (u v : E) :
    LinearMap.det ((1 + rankOne 𝕜 u v : E →L[𝕜] E) : E →ₗ[𝕜] E) = 1 + ⟪v, u⟫_𝕜 := by
  classical
  set b := stdOrthonormalBasis 𝕜 E
  have h : LinearMap.toMatrix b.toBasis b.toBasis ((1 + rankOne 𝕜 u v : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = 1 + Matrix.replicateCol Unit (fun i ↦ b.repr u i)
        * Matrix.replicateRow Unit (fun j ↦ ⟪v, b j⟫_𝕜) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Matrix.mul_apply, b.repr_apply_apply,
      mul_comm]
  rw [← LinearMap.det_toMatrix b.toBasis, h, Matrix.det_one_add_replicateCol_mul_replicateRow,
    ← b.sum_inner_mul_inner v u]
  simp [dotProduct, b.repr_apply_apply]

/-- For an invertible operator `V` in finite dimension,
`det (V + rankOne 𝕜 u v) = det V * (1 + ⟪v, V⁻¹ u⟫)`. -/
theorem det_add_rankOne [FiniteDimensional 𝕜 E] {V : E →L[𝕜] E} (hV : IsUnit V) (u v : E) :
    LinearMap.det ((V + rankOne 𝕜 u v : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      LinearMap.det (V : E →ₗ[𝕜] E) * (1 + ⟪v, Ring.inverse V u⟫_𝕜) := by
  have h : V + rankOne 𝕜 u v = V * (1 + rankOne 𝕜 (Ring.inverse V u) v) := by
    ext w
    simp only [add_apply, mul_apply_eq_comp, one_apply_eq_self, rankOne_apply, map_add, map_smul,
      V.apply_ringInverse_apply hV]
  rw [h, ContinuousLinearMap.toLinearMap_mul, map_mul, det_one_add_rankOne]

/-- The operator `V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • rankOne 𝕜 (V⁻¹ u) (V⁻¹ v)` is a two-sided inverse
of `V + rankOne 𝕜 u v`, for a symmetric invertible `V` with `1 + ⟪v, V⁻¹ u⟫ ≠ 0`. -/
private theorem add_rankOne_mul_eq_one_and {V : E →L[𝕜] E} (hV : IsUnit V)
    (hVs : (V : E →ₗ[𝕜] E).IsSymmetric) (u v : E) (h : 1 + ⟪v, Ring.inverse V u⟫_𝕜 ≠ 0) :
    (V + rankOne 𝕜 u v) * (Ring.inverse V -
        (1 + ⟪v, Ring.inverse V u⟫_𝕜)⁻¹ • rankOne 𝕜 (Ring.inverse V u) (Ring.inverse V v)) = 1 ∧
      (Ring.inverse V - (1 + ⟪v, Ring.inverse V u⟫_𝕜)⁻¹ •
        rankOne 𝕜 (Ring.inverse V u) (Ring.inverse V v)) * (V + rankOne 𝕜 u v) = 1 := by
  set W := Ring.inverse V
  set c := (1 + ⟪v, W u⟫_𝕜)⁻¹
  have hVW (y : E) : V (W y) = y := V.apply_ringInverse_apply hV y
  have hWV (y : E) : W (V y) = y := V.ringInverse_apply_apply hV y
  have hWs (y z : E) : ⟪W y, z⟫_𝕜 = ⟪y, W z⟫_𝕜 := hVs.ringInverse y z
  have hcu : c * (1 + ⟪v, W u⟫_𝕜) = 1 := inv_mul_cancel₀ h
  constructor
  · ext w
    have hcoef : ⟪v, W w⟫_𝕜 - c * ⟪W v, w⟫_𝕜 * (1 + ⟪v, W u⟫_𝕜) = 0 := by
      rw [hWs, mul_comm c, mul_assoc, hcu, mul_one, sub_self]
    have : (V + rankOne 𝕜 u v) ((W - c • rankOne 𝕜 (W u) (W v)) w)
        = w + (⟪v, W w⟫_𝕜 - c * ⟪W v, w⟫_𝕜 * (1 + ⟪v, W u⟫_𝕜)) • u := by
      simp only [add_apply, sub_apply, smul_apply, rankOne_apply, map_sub, map_smul, hVW]
      module
    rw [hcoef, zero_smul, add_zero] at this
    exact this
  · ext w
    have hVv : ⟪W v, V w⟫_𝕜 = ⟪v, w⟫_𝕜 := by
      rw [← hVs.apply_clm, hVW]
    have hcoef : 1 - c * (1 + ⟪W v, u⟫_𝕜) = 0 := by rw [hWs, hcu, sub_self]
    have : (W - c • rankOne 𝕜 (W u) (W v)) ((V + rankOne 𝕜 u v) w)
        = w + (1 - c * (1 + ⟪W v, u⟫_𝕜)) • ⟪v, w⟫_𝕜 • W u := by
      simp only [add_apply, sub_apply, smul_apply, rankOne_apply, map_add, map_smul, hWV, hVv]
      module
    rw [hcoef, zero_smul, add_zero] at this
    exact this

/-- For a symmetric invertible operator `V` and vectors `u v` with `1 + ⟪v, V⁻¹ u⟫ ≠ 0`, the
rank-one update `V + rankOne 𝕜 u v` is invertible. -/
theorem isUnit_add_rankOne {V : E →L[𝕜] E} (hV : IsUnit V) (hVs : (V : E →ₗ[𝕜] E).IsSymmetric)
    (u v : E) (h : 1 + ⟪v, Ring.inverse V u⟫_𝕜 ≠ 0) :
    IsUnit (V + rankOne 𝕜 u v) :=
  ⟨⟨_, _, (add_rankOne_mul_eq_one_and hV hVs u v h).1, (add_rankOne_mul_eq_one_and hV hVs u v h).2⟩,
    rfl⟩

/-- **Sherman–Morrison formula**: for a symmetric invertible operator `V` and vectors `u v` with
`1 + ⟪v, V⁻¹ u⟫ ≠ 0`, the inverse of `V + rankOne 𝕜 u v` is
`V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • rankOne 𝕜 (V⁻¹ u) (V⁻¹ v)`. That rank-one update is invertible by
`isUnit_add_rankOne`. -/
theorem ringInverse_add_rankOne {V : E →L[𝕜] E} (hV : IsUnit V)
    (hVs : (V : E →ₗ[𝕜] E).IsSymmetric) (u v : E) (h : 1 + ⟪v, Ring.inverse V u⟫_𝕜 ≠ 0) :
    Ring.inverse (V + rankOne 𝕜 u v) = Ring.inverse V -
      (1 + ⟪v, Ring.inverse V u⟫_𝕜)⁻¹ • rankOne 𝕜 (Ring.inverse V u) (Ring.inverse V v) :=
  Ring.inverse_unit
    ⟨_, _, (add_rankOne_mul_eq_one_and hV hVs u v h).1, (add_rankOne_mul_eq_one_and hV hVs u v h).2⟩

end LMLExplore
