/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Continuous linear functionals on inner product spaces

A continuous linear functional `y` on a finite-dimensional inner product space is determined by
its values on an orthonormal basis `b`: `y = ∑ i, y (b i) • ⟪b i, ·⟫`. This is the continuous
version of `Basis.sum_dual_apply_smul_coord`, whose coordinate functionals are, for an orthonormal
basis, the inner products `⟪b i, ·⟫`. It is the identity behind unbiased estimates of a loss
functional from its values in the directions of a basis.

On a real inner product space, complete or not, the norm is smooth away from `0`, so a unit vector
`e` has a unique norming functional: a functional `q` of norm at most `1` with `q e = 1` is the
inner product `⟪e, ·⟫`. For instance, if `x` is a nearest point of the closure of a set `V` to a
point `z` outside this closure, a subgradient of the distance to `V` at `z` within the whole space
has norm at most `1` and takes the value `‖z - x‖` at `z - x`
(`HasSubgradientWithinAt.apply_sub_eq_norm_of_infDist_eq`), so it is the inner product
`⟪(z - x) / ‖z - x‖, ·⟫` with the unit vector from `x` to `z`.

## Main statements

* `OrthonormalBasis.sum_apply_smul_innerSL`: `∑ i, y (b i) • innerSL 𝕜 (b i) = y`.
* `LMLExplore.inner_sub_inner_smul_self_eq_zero`, `LMLExplore.norm_sub_inner_smul_self_le`: for a
  unit vector `e`, the component `v - ⟪e, v⟫ • e` of `v` is orthogonal to `e` and not longer
  than `v`.
* `ContinuousLinearMap.eq_innerSL_of_norm_le_one`: a functional of norm at most `1` taking the
  value `1` at a unit vector `e` is `innerSL ℝ e`.
-/

public section

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A continuous linear functional is the sum of its values on an orthonormal basis times the
corresponding coordinate functionals: `y = ∑ i, y (b i) • ⟪b i, ·⟫`. -/
lemma sum_apply_smul_innerSL (b : OrthonormalBasis ι 𝕜 E) (y : E →L[𝕜] 𝕜) :
    ∑ i, y (b i) • innerSL 𝕜 (b i) = y := by
  ext v
  have h := congr($(b.toBasis.sum_dual_apply_smul_coord (y : E →ₗ[𝕜] 𝕜)) v)
  simpa [OrthonormalBasis.repr_apply_apply] using h

end OrthonormalBasis

open scoped RealInnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E}

/-- For a unit vector `e`, the component `v - ⟪e, v⟫ • e` of `v` is orthogonal to `e`. -/
lemma inner_sub_inner_smul_self_eq_zero (he : ‖e‖ = 1) (v : E) : ⟪e, v - ⟪e, v⟫ • e⟫ = 0 := by
  simp [inner_sub_right, inner_smul_right, he]

/-- For a unit vector `e`, the component `v - ⟪e, v⟫ • e` of `v` orthogonal to `e` is not longer
than `v`. -/
lemma norm_sub_inner_smul_self_le (he : ‖e‖ = 1) (v : E) : ‖v - ⟪e, v⟫ • e‖ ≤ ‖v‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (x := v - ⟪e, v⟫ • e) (y := ⟪e, v⟫ • e)
    (by rw [real_inner_smul_right, real_inner_comm e, inner_sub_inner_smul_self_eq_zero he,
      mul_zero])
  rw [sub_add_cancel] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (by nlinarith [mul_self_nonneg ‖⟪e, v⟫ • e‖])

end LMLExplore

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Uniqueness of norming functionals** in a real inner product space: a continuous linear
functional `q` of norm at most `1` that takes the value `1` at a unit vector `e` is the inner
product `⟪e, ·⟫`. -/
theorem eq_innerSL_of_norm_le_one {q : E →L[ℝ] ℝ} {e : E} (hq : ‖q‖ ≤ 1) (he : ‖e‖ = 1)
    (hqe : q e = 1) : q = innerSL ℝ e := by
  ext v
  -- Decompose `v` along `e` and its orthogonal complement, and show that `q` vanishes on `w`.
  set w := v - ⟪e, v⟫ • e with hw_def
  have hew : ⟪e, w⟫ = 0 := LMLExplore.inner_sub_inner_smul_self_eq_zero he v
  -- `1 + t q w = q (e + t w) ≤ ‖e + t w‖ ≤ (1 + ‖e + t w‖ ^ 2) / 2 = 1 + t ^ 2 ‖w‖ ^ 2 / 2`.
  have key (t : ℝ) : t * q w ≤ t ^ 2 * ‖w‖ ^ 2 / 2 := by
    have h₁ : q (e + t • w) ≤ ‖e + t • w‖ :=
      (le_abs_self _).trans ((q.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hq))
    have h₂ : ‖e + t • w‖ ^ 2 = 1 + t ^ 2 * ‖w‖ ^ 2 := by
      have hetw : ⟪e, t • w⟫ = 0 := by rw [real_inner_smul_right, hew, mul_zero]
      rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_real hetw, ← sq, ← sq, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs, he, one_pow]
    rw [map_add, map_smul, hqe, smul_eq_mul] at h₁
    nlinarith [sq_nonneg (‖e + t • w‖ - 1)]
  have hqw : q w = 0 := by
    -- Take `t = q w / s` with `s = ‖w‖ ^ 2 + 1`: then `2 s (q w) ^ 2 ≤ (q w) ^ 2 ‖w‖ ^ 2`.
    set s := ‖w‖ ^ 2 + 1 with hs
    have hpos : 0 < s := by positivity
    have h := mul_le_mul_of_nonneg_left (key (q w / s)) (by positivity : (0 : ℝ) ≤ 2 * s ^ 2)
    have e₁ : 2 * s ^ 2 * (q w / s * q w) = 2 * s * q w ^ 2 := by field_simp
    have e₂ : 2 * s ^ 2 * ((q w / s) ^ 2 * ‖w‖ ^ 2 / 2) = q w ^ 2 * ‖w‖ ^ 2 := by field_simp
    rw [e₁, e₂, hs] at h
    nlinarith [sq_nonneg (q w), mul_nonneg (sq_nonneg (q w)) (sq_nonneg ‖w‖)]
  have hv : v = w + ⟪e, v⟫ • e := by rw [hw_def, sub_add_cancel]
  rw [hv]
  simp [hqw, hqe, inner_add_right, inner_smul_right, hew, he]

end ContinuousLinearMap
