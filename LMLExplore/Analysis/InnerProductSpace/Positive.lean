/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Symmetric
public import LMLExplore.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot

/-!
# Positive operators: inverse, quadratic form, determinant and trace

The inverse of a positive operator is positive, and the eigenvalues of a positive invertible
operator are positive. On a real inner product space, the quadratic form `x ↦ ⟪x, T x⟫` of a
positive operator `T` satisfies the Cauchy–Schwarz inequality, so `x ↦ √⟪x, T x⟫` is a seminorm
(the weighted norms `‖x‖_V` and `‖x‖_{V⁻¹}` of least squares). The determinant of a positive
operator `T` on a real inner product space of dimension `d` is at most `(trace T / d) ^ d`: both
are expressed through the eigenvalues of `T`, which are nonnegative, and the inequality is the
AM-GM inequality. More generally, for positive operators `A` and `B`,
`det A * det B ≤ (trace (A B) / d) ^ d`: the operator `√A B √A` is positive, with determinant
`det A * det B` and trace `trace (A B)`.

## Main statements

* `ContinuousLinearMap.IsPositive.ringInverse`: the inverse `Ring.inverse V` of a positive
  continuous linear operator `V` is positive. In particular `0 ≤ ⟪v, V⁻¹ v⟫` for every `v`, by
  `IsPositive.inner_nonneg_right`.
* `ContinuousLinearMap.isPositive_smul_one`, `ContinuousLinearMap.isUnit_smul_one`,
  `ContinuousLinearMap.det_smul_one`, `ContinuousLinearMap.trace_smul_one`: the scalar operator
  `c • 1` is positive for `c ≥ 0` and invertible for `c ≠ 0`, with `det (c • 1) = c ^ d` and
  `trace (c • 1) = c d`.
* `ContinuousLinearMap.IsPositive.one_add_inner_ringInverse_pos`: for a positive operator `V` on
  a real inner product space, `0 < 1 + ⟪x, V⁻¹ x⟫`.
* `ContinuousLinearMap.IsPositive.sq_inner_apply_le`,
  `ContinuousLinearMap.IsPositive.sqrt_inner_add_le`: for a positive operator `T` on a real inner
  product space, the Cauchy–Schwarz inequality `⟪x, T y⟫² ≤ ⟪x, T x⟫ * ⟪y, T y⟫` and the triangle
  inequality for the seminorm `x ↦ √⟪x, T x⟫`.
* `ContinuousLinearMap.IsPositive.abs_inner_le_sqrt_mul_sqrt_ringInverse`: for a positive
  invertible operator `T`, the Cauchy–Schwarz inequality `|⟪x, y⟫| ≤ ‖x‖_T ‖y‖_{T⁻¹}` for the
  dual weighted norms.
* `ContinuousLinearMap.IsPositive.mul_inner_ringInverse_le_of_smul_le`: the inverse is antitone
  in the Loewner order: `c • T ≤ S` gives `c ⟪x, S⁻¹ x⟫ ≤ ⟪x, T⁻¹ x⟫` for a positive invertible `T`
  and `c > 0`.
* `ContinuousLinearMap.IsPositive.isUnit_of_le`: an operator above a positive invertible operator
  is invertible, in finite dimension.
* `LinearMap.IsPositive.eigenvalues_pos`: the eigenvalues of a positive invertible operator on a
  finite-dimensional inner product space are positive.
* `LinearMap.IsPositive.det_le_trace_div_finrank_pow`,
  `ContinuousLinearMap.IsPositive.det_le_trace_div_finrank_pow`: for a positive operator `T`,
  `det T ≤ (trace T / d) ^ d`.
* `LinearMap.IsPositive.det_mul_det_le_trace_comp_div_finrank_pow`,
  `ContinuousLinearMap.IsPositive.det_mul_det_le_trace_comp_div_finrank_pow`: for positive
  operators `A` and `B`, `det A * det B ≤ (trace (A B) / d) ^ d`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  proof of Lemma 19.4.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inverse `Ring.inverse V` of a positive continuous linear operator `V` is positive.
If `V` is not invertible, then `Ring.inverse V = 0`, which is positive. -/
theorem IsPositive.ringInverse {V : E →L[𝕜] E} (hV : V.IsPositive) :
    (Ring.inverse V).IsPositive := by
  by_cases hu : IsUnit V
  · refine ⟨hV.isSymmetric.ringInverse, fun y ↦ ?_⟩
    have := hV.re_inner_nonneg_right (Ring.inverse V y)
    rwa [ContinuousLinearMap.apply_ringInverse_apply hu] at this
  · rw [Ring.inverse_non_unit V hu]
    exact isPositive_zero

open scoped ComplexOrder in
/-- The scalar operator `c • 1` is positive for `c ≥ 0`. -/
theorem isPositive_smul_one {c : 𝕜} (hc : 0 ≤ c) : (c • 1 : E →L[𝕜] E).IsPositive :=
  isPositive_one.smul_of_nonneg hc

/-- The scalar operator `c • 1` is invertible for `c ≠ 0`. -/
theorem isUnit_smul_one {c : 𝕜} (hc : c ≠ 0) : IsUnit (c • 1 : E →L[𝕜] E) :=
  isUnit_one.smul (Units.mk0 c hc)

/-- The determinant of the scalar operator `c • 1` is `c ^ d`. -/
theorem det_smul_one (c : 𝕜) :
    LinearMap.det ((c • 1 : E →L[𝕜] E) : E →ₗ[𝕜] E) = c ^ Module.finrank 𝕜 E := by
  simp [LinearMap.det_smul]

/-- The trace of the scalar operator `c • 1` is `c d`. -/
theorem trace_smul_one [FiniteDimensional 𝕜 E] (c : 𝕜) :
    LinearMap.trace 𝕜 E ((c • 1 : E →L[𝕜] E) : E →ₗ[𝕜] E) = c * Module.finrank 𝕜 E := by
  simp

/-- For a positive operator `V` on a real inner product space, `0 < 1 + ⟪x, V⁻¹ x⟫`. -/
theorem IsPositive.one_add_inner_ringInverse_pos {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {V : F →L[ℝ] F} (hV : V.IsPositive) (x : F) :
    0 < 1 + ⟪x, Ring.inverse V x⟫_ℝ :=
  add_pos_of_pos_of_nonneg one_pos (hV.ringInverse.inner_nonneg_right x)

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {T : F →L[ℝ] F}

/-- **Cauchy–Schwarz inequality** for a positive operator `T` on a real inner product space:
`⟪x, T y⟫² ≤ ⟪x, T x⟫ * ⟪y, T y⟫`. -/
theorem IsPositive.sq_inner_apply_le (hT : T.IsPositive) (x y : F) :
    ⟪x, T y⟫_ℝ ^ 2 ≤ ⟪x, T x⟫_ℝ * ⟪y, T y⟫_ℝ :=
  LinearMap.BilinForm.apply_sq_le_of_symm ((innerₗ F).compl₂ (T : F →ₗ[ℝ] F))
    hT.inner_nonneg_right
    ⟨fun u v ↦ by simpa [real_inner_comm] using hT.inner_left_eq_inner_right v u⟩ x y

/-- **Triangle inequality** for the seminorm `x ↦ √⟪x, T x⟫` of a positive operator `T` on a
real inner product space. -/
theorem IsPositive.sqrt_inner_add_le (hT : T.IsPositive) (x y : F) :
    √⟪x + y, T (x + y)⟫_ℝ ≤ √⟪x, T x⟫_ℝ + √⟪y, T y⟫_ℝ := by
  have hx := hT.inner_nonneg_right x
  have hy := hT.inner_nonneg_right y
  have hxy : ⟪x, T y⟫_ℝ ≤ √⟪x, T x⟫_ℝ * √⟪y, T y⟫_ℝ := by
    rw [← Real.sqrt_mul hx]
    exact Real.le_sqrt_of_sq_le (hT.sq_inner_apply_le x y)
  have hyx : ⟪y, T x⟫_ℝ = ⟪x, T y⟫_ℝ := by
    rw [real_inner_comm, hT.inner_left_eq_inner_right]
  rw [Real.sqrt_le_left (by positivity)]
  simp only [map_add, inner_add_left, inner_add_right]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, hxy, hyx]

/-- **Cauchy–Schwarz inequality** for the dual weighted norms of a positive invertible operator
`T` on a real inner product space: `|⟪x, y⟫| ≤ ‖x‖_T ‖y‖_{T⁻¹}`, where `‖x‖_T = √⟪x, T x⟫`. -/
theorem IsPositive.abs_inner_le_sqrt_mul_sqrt_ringInverse (hT : T.IsPositive) (hTu : IsUnit T)
    (x y : F) :
    |⟪x, y⟫_ℝ| ≤ √⟪x, T x⟫_ℝ * √⟪y, Ring.inverse T y⟫_ℝ := by
  have h := hT.ringInverse.sq_inner_apply_le (T x) y
  rw [ringInverse_apply_apply hTu, hT.inner_left_eq_inner_right, apply_ringInverse_apply hTu,
    real_inner_comm x (T x)] at h
  rw [← Real.sqrt_mul (hT.inner_nonneg_right x)]
  exact Real.abs_le_sqrt h

/-- **The inverse is antitone in the Loewner order**, in the form of quadratic forms: for a
positive invertible operator `T`, `c > 0` and `c • T ≤ S`, `c ⟪x, S⁻¹ x⟫ ≤ ⟪x, T⁻¹ x⟫`, that is
`c S⁻¹ ≤ T⁻¹`. -/
theorem IsPositive.mul_inner_ringInverse_le_of_smul_le {S : F →L[ℝ] F} (hT : T.IsPositive)
    (hTu : IsUnit T) {c : ℝ} (hc : 0 < c) (hTS : c • T ≤ S) (x : F) :
    c * ⟪x, Ring.inverse S x⟫_ℝ ≤ ⟪x, Ring.inverse T x⟫_ℝ := by
  by_cases hSu : IsUnit S
  · -- with `v = S⁻¹ x`, `0 ≤ ⟪T⁻¹ x - c v, T (T⁻¹ x - c v)⟫` and `c ⟪v, T v⟫ ≤ ⟪v, S v⟫ = ⟪v, x⟫`
    set v := Ring.inverse S x
    have hv : S v = x := apply_ringInverse_apply hSu x
    have hw := hT.inner_nonneg_right (Ring.inverse T x - c • v)
    have hST := (le_def.1 hTS).inner_nonneg_right v
    have hTv : ⟪Ring.inverse T x, T v⟫_ℝ = ⟪x, v⟫_ℝ := by
      rw [← hT.inner_left_eq_inner_right, apply_ringInverse_apply hTu]
    simp only [map_sub, map_smul, apply_ringInverse_apply hTu, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, hTv, sub_apply, smul_apply, hv, RCLike.conj_to_real]
      at hw hST
    rw [real_inner_comm x (Ring.inverse T x), real_inner_comm x v] at hw
    rw [real_inner_comm x v] at hST
    nlinarith [hT.inner_nonneg_right v]
  · rw [Ring.inverse_non_unit S hSu, zero_apply, inner_zero_right, mul_zero]
    exact hT.ringInverse.inner_nonneg_right x

/-- An operator above a positive invertible operator in the Loewner order is invertible, on a
finite-dimensional real inner product space. -/
theorem IsPositive.isUnit_of_le [FiniteDimensional ℝ F] {S : F →L[ℝ] F} (hT : T.IsPositive)
    (hTu : IsUnit T) (hTS : T ≤ S) : IsUnit S := by
  rw [isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [coe_coe] at hv
  -- `⟪v, T v⟫ ≤ ⟪v, S v⟫ = 0`, so `T v = 0` by the Cauchy–Schwarz inequality
  have hST := (le_def.1 hTS).inner_nonneg_right v
  rw [sub_apply, hv, inner_sub_right, inner_zero_right, zero_sub, neg_nonneg] at hST
  have hTv : ⟪v, T v⟫_ℝ = 0 := le_antisymm hST (hT.inner_nonneg_right v)
  have h := hT.sq_inner_apply_le (T v) v
  rw [hTv, mul_zero] at h
  have hT0 : T v = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    nlinarith [sq_nonneg ⟪T v, T v⟫_ℝ]
  rw [← ringInverse_apply_apply hTu v, hT0, map_zero]

end Real

end ContinuousLinearMap

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The eigenvalues of a positive invertible operator on a finite-dimensional inner product space
are positive: an eigenvalue `0` would have an eigenvector in the kernel. -/
theorem IsPositive.eigenvalues_pos {T : E →ₗ[𝕜] E} {n : ℕ} (hT : T.IsPositive) (hTu : IsUnit T)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 0 < hT.isSymmetric.eigenvalues hn i := by
  refine (hT.nonneg_eigenvalues hn i).lt_of_ne fun h0 ↦ ?_
  have h := hT.isSymmetric.apply_eigenvectorBasis hn i
  rw [← h0, RCLike.ofReal_zero, zero_smul] at h
  have hb : hT.isSymmetric.eigenvectorBasis hn i = 0 := by
    simpa [(LinearMap.isUnit_iff_ker_eq_bot T).1 hTu] using LinearMap.mem_ker.2 h
  simpa [hb] using (hT.isSymmetric.eigenvectorBasis hn).orthonormal.1 i

end LinearMap

section DetTrace

open Finset Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For a positive operator `T` on a real inner product space of dimension `d`,
`det T ≤ (trace T / d) ^ d`. -/
theorem LinearMap.IsPositive.det_le_trace_div_finrank_pow {T : E →ₗ[ℝ] E} (hT : T.IsPositive) :
    LinearMap.det T ≤ (LinearMap.trace ℝ E T / finrank ℝ E) ^ finrank ℝ E := by
  rw [hT.isSymmetric.det_eq_prod_eigenvalues rfl, hT.isSymmetric.trace_eq_sum_eigenvalues rfl]
  simpa using Real.prod_le_sum_div_card_pow univ fun i _ ↦ hT.nonneg_eigenvalues rfl i

/-- For a positive continuous linear operator `T` on a real inner product space of dimension
`d`, `det T ≤ (trace T / d) ^ d`. -/
theorem ContinuousLinearMap.IsPositive.det_le_trace_div_finrank_pow {T : E →L[ℝ] E}
    (hT : T.IsPositive) :
    LinearMap.det (T : E →ₗ[ℝ] E) ≤
      (LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) / finrank ℝ E) ^ finrank ℝ E :=
  hT.toLinearMap.det_le_trace_div_finrank_pow

/-- For positive operators `A` and `B` on a real inner product space of dimension `d`,
`det A * det B ≤ (trace (A B) / d) ^ d`. With `A = V⁻¹` for a positive invertible `V`, this is
`det B ≤ det V * (trace (V⁻¹ B) / d) ^ d`. -/
theorem LinearMap.IsPositive.det_mul_det_le_trace_comp_div_finrank_pow {A B : E →ₗ[ℝ] E}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    LinearMap.det A * LinearMap.det B ≤
      (LinearMap.trace ℝ E (A ∘ₗ B) / finrank ℝ E) ^ finrank ℝ E := by
  -- `√A B √A` is positive, with determinant `det A * det B` and trace `trace (A B)`
  set S := hA.sqrt
  have hS : S ∘ₗ S = A := hA.sqrt_sq
  have hC : (S ∘ₗ B ∘ₗ S).IsPositive := by
    have h := hB.conj_adjoint S
    rwa [LinearMap.IsSymmetric.adjoint_eq hA.sqrt_isSymmetric] at h
  have hdet : LinearMap.det (S ∘ₗ B ∘ₗ S) = LinearMap.det A * LinearMap.det B := by
    rw [← hS, LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_comp]
    ring
  have htr : LinearMap.trace ℝ E (S ∘ₗ B ∘ₗ S) = LinearMap.trace ℝ E (A ∘ₗ B) := by
    rw [← LinearMap.comp_assoc, ← LinearMap.trace_comp_comm', ← LinearMap.comp_assoc, hS]
  rw [← hdet, ← htr]
  exact hC.det_le_trace_div_finrank_pow

/-- For positive continuous linear operators `A` and `B` on a real inner product space of
dimension `d`, `det A * det B ≤ (trace (A B) / d) ^ d`. -/
theorem ContinuousLinearMap.IsPositive.det_mul_det_le_trace_comp_div_finrank_pow
    {A B : E →L[ℝ] E} (hA : A.IsPositive) (hB : B.IsPositive) :
    LinearMap.det (A : E →ₗ[ℝ] E) * LinearMap.det (B : E →ₗ[ℝ] E) ≤
      (LinearMap.trace ℝ E (A ∘L B : E →ₗ[ℝ] E) / finrank ℝ E) ^ finrank ℝ E :=
  hA.toLinearMap.det_mul_det_le_trace_comp_div_finrank_pow hB.toLinearMap

end DetTrace
