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
We compute the determinant and the inverse of a rank-one update `V + rankOne 𝕜 u v` of an
invertible operator `V`, in terms of `V⁻¹ = Ring.inverse V`.

## Main statements

* `LMLExplore.det_one_add_rankOne`: the **matrix determinant lemma**
  `det (1 + rankOne 𝕜 u v) = 1 + ⟪v, u⟫`, in finite dimension.
* `LMLExplore.det_add_rankOne`: for invertible `V`,
  `det (V + rankOne 𝕜 u v) = det V * (1 + ⟪v, V⁻¹ u⟫)`, and
  `LMLExplore.det_eq_mul_prod_of_add_rankOne`: for a sequence of invertible rank-one updates
  `V (t + 1) = V t + rankOne 𝕜 (u t) (v t)`, `det V_t = det V_0 * ∏_{s < t} (1 + ⟪v s, V_s⁻¹ u s⟫)`.
* `LMLExplore.isUnit_add_rankOne`: for an invertible `V` with `1 + ⟪v, V⁻¹ u⟫ ≠ 0`,
  `V + rankOne 𝕜 u v` is invertible.
* `LMLExplore.ringInverse_add_rankOne`: the **Sherman–Morrison formula** for an invertible `V`:
  `(V + rankOne 𝕜 u v)⁻¹ = V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • (rankOne 𝕜 (V⁻¹ u) v * V⁻¹)`,
  whenever `1 + ⟪v, V⁻¹ u⟫ ≠ 0`; `LMLExplore.ringInverse_add_rankOne_of_isSymmetric` is its form
  `V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • rankOne 𝕜 (V⁻¹ u) (V⁻¹ v)` for symmetric `V`.
-/

public section

open ContinuousLinearMap InnerProductSpace Finset
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

/-- For a sequence of invertible operators in finite dimension with rank-one updates
`V (t + 1) = V t + rankOne 𝕜 (u t) (v t)`,
`det V_t = det V_0 * ∏_{s < t} (1 + ⟪v s, V_s⁻¹ u s⟫)`. -/
theorem det_eq_mul_prod_of_add_rankOne [FiniteDimensional 𝕜 E] {V : ℕ → E →L[𝕜] E}
    {u v : ℕ → E} (hV : ∀ t, V (t + 1) = V t + rankOne 𝕜 (u t) (v t)) (hVu : ∀ t, IsUnit (V t))
    (t : ℕ) :
    LinearMap.det (V t : E →ₗ[𝕜] E) =
      LinearMap.det (V 0 : E →ₗ[𝕜] E) * ∏ s ∈ range t, (1 + ⟪v s, Ring.inverse (V s) (u s)⟫_𝕜) := by
  induction t with
  | zero => simp
  | succ t ih => rw [hV, det_add_rankOne (hVu t), ih, prod_range_succ, mul_assoc]

/-- The operator `V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • (rankOne 𝕜 (V⁻¹ u) v * V⁻¹)` is a two-sided inverse
of `V + rankOne 𝕜 u v`, for an invertible `V` with `1 + ⟪v, V⁻¹ u⟫ ≠ 0`. -/
private theorem add_rankOne_mul_eq_one_and {V : E →L[𝕜] E} (hV : IsUnit V) (u v : E)
    (h : 1 + ⟪v, Ring.inverse V u⟫_𝕜 ≠ 0) :
    (V + rankOne 𝕜 u v) * (Ring.inverse V -
        (1 + ⟪v, Ring.inverse V u⟫_𝕜)⁻¹ • (rankOne 𝕜 (Ring.inverse V u) v * Ring.inverse V)) = 1 ∧
      (Ring.inverse V - (1 + ⟪v, Ring.inverse V u⟫_𝕜)⁻¹ •
        (rankOne 𝕜 (Ring.inverse V u) v * Ring.inverse V)) * (V + rankOne 𝕜 u v) = 1 := by
  set W := Ring.inverse V
  set c := (1 + ⟪v, W u⟫_𝕜)⁻¹
  have hVW (y : E) : V (W y) = y := V.apply_ringInverse_apply hV y
  have hWV (y : E) : W (V y) = y := V.ringInverse_apply_apply hV y
  have hcu : c * (1 + ⟪v, W u⟫_𝕜) = 1 := inv_mul_cancel₀ h
  constructor
  · ext w
    have hcoef : ⟪v, W w⟫_𝕜 - c * ⟪v, W w⟫_𝕜 * (1 + ⟪v, W u⟫_𝕜) = 0 := by
      rw [mul_comm c, mul_assoc, hcu, mul_one, sub_self]
    have : (V + rankOne 𝕜 u v) ((W - c • (rankOne 𝕜 (W u) v * W)) w)
        = w + (⟪v, W w⟫_𝕜 - c * ⟪v, W w⟫_𝕜 * (1 + ⟪v, W u⟫_𝕜)) • u := by
      simp only [add_apply, sub_apply, smul_apply, mul_apply_eq_comp, rankOne_apply, map_sub,
        map_smul, hVW]
      module
    rw [hcoef, zero_smul, add_zero] at this
    exact this
  · ext w
    have hcoef : 1 - c * (1 + ⟪v, W u⟫_𝕜) = 0 := by rw [hcu, sub_self]
    have : (W - c • (rankOne 𝕜 (W u) v * W)) ((V + rankOne 𝕜 u v) w)
        = w + (1 - c * (1 + ⟪v, W u⟫_𝕜)) • ⟪v, w⟫_𝕜 • W u := by
      simp only [add_apply, sub_apply, smul_apply, mul_apply_eq_comp, rankOne_apply, map_add,
        map_smul, hWV]
      module
    rw [hcoef, zero_smul, add_zero] at this
    exact this

/-- For an invertible operator `V` and vectors `u v` with `1 + ⟪v, V⁻¹ u⟫ ≠ 0`, the rank-one
update `V + rankOne 𝕜 u v` is invertible. -/
theorem isUnit_add_rankOne {V : E →L[𝕜] E} (hV : IsUnit V) (u v : E)
    (h : 1 + ⟪v, Ring.inverse V u⟫_𝕜 ≠ 0) :
    IsUnit (V + rankOne 𝕜 u v) :=
  ⟨⟨_, _, (add_rankOne_mul_eq_one_and hV u v h).1, (add_rankOne_mul_eq_one_and hV u v h).2⟩, rfl⟩

/-- **Sherman–Morrison formula**: for an invertible operator `V` and vectors `u v` with
`1 + ⟪v, V⁻¹ u⟫ ≠ 0`, the inverse of `V + rankOne 𝕜 u v` is
`V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • (rankOne 𝕜 (V⁻¹ u) v * V⁻¹)`. That rank-one update is invertible by
`isUnit_add_rankOne`; for symmetric `V`, see `ringInverse_add_rankOne_of_isSymmetric`. -/
theorem ringInverse_add_rankOne {V : E →L[𝕜] E} (hV : IsUnit V) (u v : E)
    (h : 1 + ⟪v, Ring.inverse V u⟫_𝕜 ≠ 0) :
    Ring.inverse (V + rankOne 𝕜 u v) = Ring.inverse V -
      (1 + ⟪v, Ring.inverse V u⟫_𝕜)⁻¹ • (rankOne 𝕜 (Ring.inverse V u) v * Ring.inverse V) :=
  Ring.inverse_unit
    ⟨_, _, (add_rankOne_mul_eq_one_and hV u v h).1, (add_rankOne_mul_eq_one_and hV u v h).2⟩

/-- **Sherman–Morrison formula** for a symmetric invertible operator `V`: for vectors `u v` with
`1 + ⟪v, V⁻¹ u⟫ ≠ 0`, the inverse of `V + rankOne 𝕜 u v` is
`V⁻¹ - (1 + ⟪v, V⁻¹ u⟫)⁻¹ • rankOne 𝕜 (V⁻¹ u) (V⁻¹ v)`. -/
theorem ringInverse_add_rankOne_of_isSymmetric {V : E →L[𝕜] E} (hV : IsUnit V)
    (hVs : (V : E →ₗ[𝕜] E).IsSymmetric) (u v : E) (h : 1 + ⟪v, Ring.inverse V u⟫_𝕜 ≠ 0) :
    Ring.inverse (V + rankOne 𝕜 u v) = Ring.inverse V -
      (1 + ⟪v, Ring.inverse V u⟫_𝕜)⁻¹ • rankOne 𝕜 (Ring.inverse V u) (Ring.inverse V v) := by
  have hR : rankOne 𝕜 (Ring.inverse V u) v * Ring.inverse V =
      rankOne 𝕜 (Ring.inverse V u) (Ring.inverse V v) := by
    ext w
    rw [mul_apply_eq_comp, rankOne_apply, rankOne_apply, hVs.ringInverse.apply_clm]
  rw [ringInverse_add_rankOne hV u v h, hR]

end LMLExplore
