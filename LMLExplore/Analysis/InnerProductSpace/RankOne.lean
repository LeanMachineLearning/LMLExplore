/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
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
* `LMLExplore.ring_inverse_add_rankOne_self`: the **Sherman–Morrison formula** for a symmetric
  invertible `V`: `(V + rankOne 𝕜 x x)⁻¹ = V⁻¹ - (1 + ⟪x, V⁻¹ x⟫)⁻¹ • rankOne 𝕜 (V⁻¹ x) (V⁻¹ x)`,
  whenever `1 + ⟪x, V⁻¹ x⟫ ≠ 0`.
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
    have hVV : V (Ring.inverse V u) = u := by
      change (V * Ring.inverse V) u = u
      rw [Ring.mul_inverse_cancel V hV]
      rfl
    change V w + ⟪v, w⟫_𝕜 • u = V (w + ⟪v, w⟫_𝕜 • Ring.inverse V u)
    rw [map_add, map_smul, hVV]
  rw [h, ContinuousLinearMap.toLinearMap_mul, map_mul, det_one_add_rankOne]

/-- **Sherman–Morrison formula**: for a symmetric invertible operator `V` and `x` with
`1 + ⟪x, V⁻¹ x⟫ ≠ 0`, `V + rankOne 𝕜 x x` is invertible with inverse
`V⁻¹ - (1 + ⟪x, V⁻¹ x⟫)⁻¹ • rankOne 𝕜 (V⁻¹ x) (V⁻¹ x)`. -/
theorem ring_inverse_add_rankOne_self {V : E →L[𝕜] E} (hV : IsUnit V)
    (hVs : (V : E →ₗ[𝕜] E).IsSymmetric) (x : E) (hx : 1 + ⟪x, Ring.inverse V x⟫_𝕜 ≠ 0) :
    Ring.inverse (V + rankOne 𝕜 x x) = Ring.inverse V -
      (1 + ⟪x, Ring.inverse V x⟫_𝕜)⁻¹ • rankOne 𝕜 (Ring.inverse V x) (Ring.inverse V x) := by
  set W := Ring.inverse V with hW
  set c := (1 + ⟪x, W x⟫_𝕜)⁻¹ with hc
  have hVW (y : E) : V (W y) = y := by
    change (V * W) y = y
    rw [hW, Ring.mul_inverse_cancel V hV]
    rfl
  have hWV (y : E) : W (V y) = y := by
    change (W * V) y = y
    rw [hW, Ring.inverse_mul_cancel V hV]
    rfl
  -- `W` is symmetric, as the inverse of a symmetric operator
  have hWs (y z : E) : ⟪W y, z⟫_𝕜 = ⟪y, W z⟫_𝕜 := by
    conv_lhs => rw [← hVW z]
    conv_rhs => rw [← hVW y]
    exact (hVs (W y) (W z)).symm
  have hcx : c * (1 + ⟪x, W x⟫_𝕜) = 1 := inv_mul_cancel₀ hx
  set B := W - c • rankOne 𝕜 (W x) (W x) with hB
  have h1 : (V + rankOne 𝕜 x x) * B = 1 := by
    ext w
    have hcoef : ⟪x, W w⟫_𝕜 - c * ⟪W x, w⟫_𝕜 * (1 + ⟪x, W x⟫_𝕜) = 0 := by
      rw [hWs, mul_comm c, mul_assoc, hcx, mul_one, sub_self]
    have : (V + rankOne 𝕜 x x) (B w)
        = w + (⟪x, W w⟫_𝕜 - c * ⟪W x, w⟫_𝕜 * (1 + ⟪x, W x⟫_𝕜)) • x := by
      simp only [hB, add_apply, sub_apply, smul_apply, rankOne_apply, map_sub, map_smul, hVW]
      module
    rw [hcoef, zero_smul, add_zero] at this
    exact this
  have h2 : B * (V + rankOne 𝕜 x x) = 1 := by
    ext w
    have hVx : ⟪W x, V w⟫_𝕜 = ⟪x, w⟫_𝕜 := by
      have := hVs (W x) w
      rw [ContinuousLinearMap.coe_coe, hVW] at this
      exact this.symm
    have hcoef : 1 - c * (1 + ⟪W x, x⟫_𝕜) = 0 := by rw [hWs, hcx, sub_self]
    have : B ((V + rankOne 𝕜 x x) w) = w + (1 - c * (1 + ⟪W x, x⟫_𝕜)) • ⟪x, w⟫_𝕜 • W x := by
      simp only [hB, add_apply, sub_apply, smul_apply, rankOne_apply, map_add, map_smul, hWV, hVx]
      module
    rw [hcoef, zero_smul, add_zero] at this
    exact this
  exact Ring.inverse_unit ⟨V + rankOne 𝕜 x x, B, h1, h2⟩

end LMLExplore
