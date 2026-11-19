/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.CStarAlgebra.Matrix
public import LMLExplore.Analysis.InnerProductSpace.EllipticalPotential
public import LMLExplore.Analysis.InnerProductSpace.PiL2
public import LMLExplore.Analysis.InnerProductSpace.Ridge
public import Mathlib.Algebra.Order.Star.Real

/-!
# Design matrices of regularized least squares

For a square matrix `V₀` indexed by a finite type `ι` and vectors `x 0, x 1, … : ι → ℝ`, the
*design matrix* with regularizer `V₀` is `V_t(V₀) = V₀ + ∑_{s < t} x s x sᵀ`, the matrix form of
the design operator `LMLExplore.designOp` on `EuclideanSpace ℝ ι`. Ridge regression with
parameter `λ` uses `V_t(λ) = V_t(λ • 1)`. The weighted norm `‖v‖²_{V⁻¹}` is `v ⬝ᵥ V⁻¹ *ᵥ v`.

Under `Matrix.toEuclideanCLM` the design matrix acts as the design operator of the vectors
`toLp 2 (x s)` (`LMLExplore.toEuclideanCLM_designMatrix`), and this file specializes the theory of
design operators to matrices: positivity, the rank-one updates of the inverse and of the
determinant, the determinant bounds and the elliptical potential lemma of [LS, Section 19.2], and
the ridge estimate. A bound `‖x s‖ ≤ L` on the Euclidean norm reads `x s ⬝ᵥ x s ≤ L ^ 2`, and the
dimension `d` is `Fintype.card ι`.

## Main definitions

* `LMLExplore.designMatrix V₀ x t`: the design matrix `V_t(V₀)`.

## Main statements

* `LMLExplore.toEuclideanCLM_designMatrix`: the design matrix acts as the design operator.
* `LMLExplore.designMatrix_mulVec`, `LMLExplore.dotProduct_designMatrix_mulVec`:
  `V_t(V₀) v = V₀ v + ∑_{s < t} (x s ⬝ᵥ v) • x s` and
  `v ⬝ᵥ V_t(V₀) v = v ⬝ᵥ V₀ v + ∑_{s < t} (x s ⬝ᵥ v)²`.
* `LMLExplore.posSemidef_designMatrix`, `LMLExplore.posDef_designMatrix`: the design matrix is
  positive semidefinite (definite) for a positive semidefinite (definite) regularizer.
* `LMLExplore.inv_designMatrix_succ`: the rank-one update of the inverse (Sherman–Morrison).
* `LMLExplore.det_designMatrix_succ`: `det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})` [LS, (19.9)],
  and `LMLExplore.det_designMatrix_eq_mul_prod`.
* `LMLExplore.trace_designMatrix`, `LMLExplore.det_designMatrix_le`:
  `det V_t(V₀) ≤ ((trace V₀ + ∑_{s < t} x s ⬝ᵥ x s) / d) ^ d`.
* `LMLExplore.log_det_designMatrix_div_le`, `LMLExplore.det_designMatrix_div_pow_le`,
  `LMLExplore.log_det_designMatrix_div_pow_le`: the determinant bounds of
  [LS, Lemma 19.4] and [LS, (20.9)].
* `LMLExplore.sum_min_one_dotProduct_inv_designMatrix_mulVec_le_log_det`,
  `LMLExplore.sum_min_one_dotProduct_inv_designMatrix_smul_one_mulVec_le`: the elliptical
  potential lemma [LS, Lemma 19.4].
* `LMLExplore.ofLp_ridgeEstimate`: the ridge estimate is `V_t(λ)⁻¹ ∑_{s < t} y s • x s`.

## Implementation notes

The design matrix, its determinant recursion `det_designMatrix_succ`, the determinant bounds
`log_det_designMatrix_div_le` and `det_designMatrix_div_pow_le` and the elliptical potential lemma
`sum_min_one_dotProduct_inv_designMatrix_mulVec_le_log_det` correspond to the matrix versions
`regGram`, `det_regGram_succ`, `log_det_regGram_le` and `sum_min_one_mahalanobisSq_inv_regGram_le`
of the LMLPapers project (Rémy Degenne, <https://github.com/LeanMachineLearning/LMLPapers>). The
proofs here are new: they transfer the operator results through `Matrix.toEuclideanCLM`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 19.2, Lemma 19.4 and equations (19.9) and (20.9).
-/

public section

open Finset Matrix WithLp Real

namespace LMLExplore

variable {ι : Type*} {V₀ : Matrix ι ι ℝ} {lam : ℝ}

/-- The **design matrix** `V_t(V₀) = V₀ + ∑_{s < t} x s x sᵀ` with regularizer `V₀`. Ridge
regression with parameter `λ` uses `V₀ = λ • 1`. -/
noncomputable def designMatrix (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) (t : ℕ) : Matrix ι ι ℝ :=
  V₀ + ∑ s ∈ range t, vecMulVec (x s) (x s)

/-- The defining equation of `designMatrix`. -/
theorem designMatrix_def (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) (t : ℕ) :
    designMatrix V₀ x t = V₀ + ∑ s ∈ range t, vecMulVec (x s) (x s) :=
  (rfl)

@[simp]
theorem designMatrix_zero (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) : designMatrix V₀ x 0 = V₀ := by
  simp [designMatrix]

/-- The design matrix is updated by a rank-one term at each step. -/
theorem designMatrix_succ (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) (t : ℕ) :
    designMatrix V₀ x (t + 1) = designMatrix V₀ x t + vecMulVec (x t) (x t) := by
  rw [designMatrix, designMatrix, sum_range_succ, add_assoc]

/-- The design matrix `V_t(V₀)` only depends on the vectors `x s` for `s < t`. -/
theorem designMatrix_congr {x x' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, x s = x' s) :
    designMatrix V₀ x t = designMatrix V₀ x' t := by
  rw [designMatrix, designMatrix, sum_congr rfl fun s hs ↦ by rw [h s (mem_range.1 hs)]]

/-- The design matrix is positive semidefinite for a positive semidefinite regularizer `V₀`. -/
theorem posSemidef_designMatrix [Finite ι] (hV₀ : V₀.PosSemidef) (x : ℕ → ι → ℝ) (t : ℕ) :
    (designMatrix V₀ x t).PosSemidef :=
  hV₀.add <| posSemidef_sum _ fun s _ ↦ by
    simpa using posSemidef_vecMulVec_self_star (x s)

/-- The design matrix is positive definite for a positive definite regularizer `V₀`. -/
theorem posDef_designMatrix [Finite ι] (hV₀ : V₀.PosDef) (x : ℕ → ι → ℝ) (t : ℕ) :
    (designMatrix V₀ x t).PosDef :=
  hV₀.add_posSemidef <| posSemidef_sum _ fun s _ ↦ by
    simpa using posSemidef_vecMulVec_self_star (x s)

/-- The design matrix `V_t(λ)` is positive definite for `λ > 0`. -/
theorem posDef_designMatrix_smul_one [Finite ι] [DecidableEq ι] (hlam : 0 < lam) (x : ℕ → ι → ℝ)
    (t : ℕ) :
    (designMatrix (lam • 1) x t).PosDef :=
  posDef_designMatrix (PosDef.one.smul hlam) x t

variable [Fintype ι]

/-- The action of the design matrix: `V_t(V₀) v = V₀ v + ∑_{s < t} (x s ⬝ᵥ v) • x s`. -/
@[simp]
theorem designMatrix_mulVec (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) (t : ℕ) (v : ι → ℝ) :
    designMatrix V₀ x t *ᵥ v = V₀ *ᵥ v + ∑ s ∈ range t, (x s ⬝ᵥ v) • x s := by
  simp [designMatrix, add_mulVec, sum_mulVec, vecMulVec_mulVec]

/-- The quadratic form of the design matrix:
`v ⬝ᵥ V_t(V₀) v = v ⬝ᵥ V₀ v + ∑_{s < t} (x s ⬝ᵥ v)²`. -/
theorem dotProduct_designMatrix_mulVec (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) (t : ℕ) (v : ι → ℝ) :
    v ⬝ᵥ designMatrix V₀ x t *ᵥ v = v ⬝ᵥ V₀ *ᵥ v + ∑ s ∈ range t, (x s ⬝ᵥ v) ^ 2 := by
  rw [designMatrix_mulVec, dotProduct_add, dotProduct_sum]
  simp [dotProduct_comm v, sq]

/-- The trace of the design matrix: `trace V_t(V₀) = trace V₀ + ∑_{s < t} x s ⬝ᵥ x s`. -/
@[simp]
theorem trace_designMatrix (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) (t : ℕ) :
    (designMatrix V₀ x t).trace = V₀.trace + ∑ s ∈ range t, x s ⬝ᵥ x s := by
  simp [designMatrix, trace_sum]

variable [DecidableEq ι]

/-- The design matrix acts on Euclidean space as the design operator of the vectors
`toLp 2 (x s)`, with regularizer the action of `V₀`. -/
theorem toEuclideanCLM_designMatrix (V₀ : Matrix ι ι ℝ) (x : ℕ → ι → ℝ) (t : ℕ) :
    toEuclideanCLM (𝕜 := ℝ) (designMatrix V₀ x t) =
      designOp (toEuclideanCLM (𝕜 := ℝ) V₀) (fun s ↦ toLp 2 (x s)) t := by
  simp only [designMatrix, designOp_def, map_add, map_sum, toEuclideanCLM_vecMulVec_of_trivialStar]

/-- **Sherman–Morrison formula** for the design matrix: for a positive definite regularizer `V₀`,
`V_{t+1}⁻¹ = V_t⁻¹ - (1 + ‖x t‖²_{V_t⁻¹})⁻¹ • (V_t⁻¹ x t) (V_t⁻¹ x t)ᵀ`. -/
theorem inv_designMatrix_succ (hV₀ : V₀.PosDef) (x : ℕ → ι → ℝ) (t : ℕ) :
    (designMatrix V₀ x (t + 1))⁻¹ = (designMatrix V₀ x t)⁻¹ -
      (1 + x t ⬝ᵥ (designMatrix V₀ x t)⁻¹ *ᵥ x t)⁻¹ •
        vecMulVec ((designMatrix V₀ x t)⁻¹ *ᵥ x t) ((designMatrix V₀ x t)⁻¹ *ᵥ x t) := by
  apply EquivLike.injective (toEuclideanCLM (𝕜 := ℝ) (n := ι))
  simp only [map_sub, map_smul, toEuclideanCLM_inv, toEuclideanCLM_vecMulVec_of_trivialStar,
    ← toEuclideanCLM_toLp]
  simpa only [← toEuclideanCLM_designMatrix, inner_ringInverse_toEuclideanCLM, ofLp_toLp] using
    ringInverse_designOp_succ hV₀.isPositive_toEuclideanCLM hV₀.isUnit_toEuclideanCLM
      (fun s ↦ toLp 2 (x s)) t

/-- The determinant of the design matrix after a rank-one update (the matrix determinant lemma,
[LS, (19.9)]): for a positive definite regularizer `V₀`,
`det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})`. -/
theorem det_designMatrix_succ (hV₀ : V₀.PosDef) (x : ℕ → ι → ℝ) (t : ℕ) :
    (designMatrix V₀ x (t + 1)).det =
      (designMatrix V₀ x t).det * (1 + x t ⬝ᵥ (designMatrix V₀ x t)⁻¹ *ᵥ x t) := by
  have h := det_designOp_succ hV₀.isPositive_toEuclideanCLM
    hV₀.isUnit_toEuclideanCLM (fun s ↦ toLp 2 (x s)) t
  rwa [← toEuclideanCLM_designMatrix, ← toEuclideanCLM_designMatrix, det_toEuclideanCLM,
    det_toEuclideanCLM, inner_ringInverse_toEuclideanCLM, ofLp_toLp] at h

/-- For a positive definite regularizer `V₀`,
`det V_t = det V₀ * ∏_{s < t} (1 + ‖x s‖²_{V_s⁻¹})`. -/
theorem det_designMatrix_eq_mul_prod (hV₀ : V₀.PosDef) (x : ℕ → ι → ℝ) (t : ℕ) :
    (designMatrix V₀ x t).det =
      V₀.det * ∏ s ∈ range t, (1 + x s ⬝ᵥ (designMatrix V₀ x s)⁻¹ *ᵥ x s) := by
  have h := det_designOp_eq_mul_prod hV₀.isPositive_toEuclideanCLM
    hV₀.isUnit_toEuclideanCLM (fun s ↦ toLp 2 (x s)) t
  simp_rw [← toEuclideanCLM_designMatrix, det_toEuclideanCLM,
    inner_ringInverse_toEuclideanCLM] at h
  exact h

/-- For a positive semidefinite regularizer `V₀`,
`det V_t(V₀) ≤ ((trace V₀ + ∑_{s < t} x s ⬝ᵥ x s) / d) ^ d`, with `d = Fintype.card ι`. -/
theorem det_designMatrix_le (hV₀ : V₀.PosSemidef) (x : ℕ → ι → ℝ) (t : ℕ) :
    (designMatrix V₀ x t).det ≤
      ((V₀.trace + ∑ s ∈ range t, x s ⬝ᵥ x s) / Fintype.card ι) ^ Fintype.card ι := by
  have h := det_designOp_le (isPositive_toEuclideanCLM_iff.2 hV₀) (fun s ↦ toLp 2 (x s)) t
  simp_rw [← toEuclideanCLM_designMatrix, det_toEuclideanCLM, trace_toEuclideanCLM,
    EuclideanSpace.norm_toLp_sq, finrank_euclideanSpace] at h
  exact h

/-- The determinant bound of [LS, Lemma 19.4]: for a positive definite regularizer `V₀`, if
`x s ⬝ᵥ x s ≤ L ^ 2` for all `s < t`, then
`log (det V_t(V₀) / det V₀) ≤ d log ((trace V₀ + t L²) / (d det (V₀) ^ (1 / d)))`, with
`d = Fintype.card ι`. -/
theorem log_det_designMatrix_div_le (hV₀ : V₀.PosDef) (x : ℕ → ι → ℝ) {t : ℕ} {L : ℝ}
    (hx : ∀ s < t, x s ⬝ᵥ x s ≤ L ^ 2) :
    log ((designMatrix V₀ x t).det / V₀.det) ≤
      Fintype.card ι * log ((V₀.trace + t * L ^ 2) /
        (Fintype.card ι * V₀.det ^ (Fintype.card ι : ℝ)⁻¹)) := by
  have h := log_det_designOp_div_le hV₀.isPositive_toEuclideanCLM hV₀.isUnit_toEuclideanCLM
    (fun s ↦ toLp 2 (x s)) fun s hs ↦ EuclideanSpace.norm_toLp_le_abs_of_dotProduct_le_sq (hx s hs)
  rwa [← toEuclideanCLM_designMatrix, det_toEuclideanCLM, det_toEuclideanCLM,
    trace_toEuclideanCLM, finrank_euclideanSpace, sq_abs] at h

/-- [LS, (20.9)]: for `λ > 0`, if `x s ⬝ᵥ x s ≤ L ^ 2` for all `s < t`, then
`det V_t(λ) / λ ^ d ≤ (1 + t L² / (λ d)) ^ d`, with `d = Fintype.card ι`. -/
theorem det_designMatrix_div_pow_le (hlam : 0 < lam) (x : ℕ → ι → ℝ) {t : ℕ} {L : ℝ}
    (hx : ∀ s < t, x s ⬝ᵥ x s ≤ L ^ 2) :
    (designMatrix (lam • 1) x t).det / lam ^ Fintype.card ι ≤
      (1 + t * L ^ 2 / (lam * Fintype.card ι)) ^ Fintype.card ι := by
  have h := det_designOp_div_pow_le hlam (fun s ↦ toLp 2 (x s))
    fun s hs ↦ EuclideanSpace.norm_toLp_le_abs_of_dotProduct_le_sq (hx s hs)
  rwa [← toEuclideanCLM_smul_one, ← toEuclideanCLM_designMatrix, det_toEuclideanCLM,
    finrank_euclideanSpace, sq_abs] at h

/-- [LS, (20.9)] in logarithmic form: for `λ > 0`, if `x s ⬝ᵥ x s ≤ L ^ 2` for all `s < t`, then
`log (det V_t(λ) / λ ^ d) ≤ d log (1 + t L² / (λ d))`, with `d = Fintype.card ι`. -/
theorem log_det_designMatrix_div_pow_le (hlam : 0 < lam) (x : ℕ → ι → ℝ) {t : ℕ}
    {L : ℝ} (hx : ∀ s < t, x s ⬝ᵥ x s ≤ L ^ 2) :
    log ((designMatrix (lam • 1) x t).det / lam ^ Fintype.card ι) ≤
      Fintype.card ι * log (1 + t * L ^ 2 / (lam * Fintype.card ι)) := by
  have h := log_det_designOp_div_pow_le hlam (fun s ↦ toLp 2 (x s))
    fun s hs ↦ EuclideanSpace.norm_toLp_le_abs_of_dotProduct_le_sq (hx s hs)
  rwa [← toEuclideanCLM_smul_one, ← toEuclideanCLM_designMatrix, det_toEuclideanCLM,
    finrank_euclideanSpace, sq_abs] at h

/-- **Elliptical potential lemma** for matrices, log-determinant form [LS, Lemma 19.4]: for a
positive definite regularizer `V₀` and the design matrices `V_t = designMatrix V₀ x t`,
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V₀)`. -/
theorem sum_min_one_dotProduct_inv_designMatrix_mulVec_le_log_det (hV₀ : V₀.PosDef)
    (x : ℕ → ι → ℝ) (n : ℕ) :
    ∑ t ∈ range n, min 1 (x t ⬝ᵥ (designMatrix V₀ x t)⁻¹ *ᵥ x t) ≤
      2 * log ((designMatrix V₀ x n).det / V₀.det) := by
  have h := sum_min_one_inner_inverse_designOp_le_log_det
    hV₀.isPositive_toEuclideanCLM hV₀.isUnit_toEuclideanCLM (fun s ↦ toLp 2 (x s)) n
  simp_rw [← toEuclideanCLM_designMatrix, inner_ringInverse_toEuclideanCLM,
    det_toEuclideanCLM] at h
  exact h

/-- **Elliptical potential lemma** for matrices with the ridge regularizer [LS, Lemma 19.4]: for
`λ > 0`, if `x t ⬝ᵥ x t ≤ L ^ 2` for all `t < n`, then
`∑_{t < n} min 1 ‖x t‖²_{V_t(λ)⁻¹} ≤ 2 d log (1 + n L² / (λ d))`, with `d = Fintype.card ι`. -/
theorem sum_min_one_dotProduct_inv_designMatrix_smul_one_mulVec_le (hlam : 0 < lam)
    (x : ℕ → ι → ℝ) {n : ℕ} {L : ℝ} (hx : ∀ t < n, x t ⬝ᵥ x t ≤ L ^ 2) :
    ∑ t ∈ range n, min 1 (x t ⬝ᵥ (designMatrix (lam • 1) x t)⁻¹ *ᵥ x t) ≤
      2 * Fintype.card ι * log (1 + n * L ^ 2 / (lam * Fintype.card ι)) := by
  have h := sum_min_one_dotProduct_inv_designMatrix_mulVec_le_log_det
    (PosDef.one.smul hlam : (lam • 1 : Matrix ι ι ℝ).PosDef) x n
  rw [det_smul, det_one, mul_one] at h
  rw [mul_assoc]
  exact h.trans (by gcongr; exact log_det_designMatrix_div_pow_le hlam x hx)

/-- The ridge estimate of the vectors `toLp 2 (x s)` is `V_t(λ)⁻¹ ∑_{s < t} y s • x s`. -/
theorem ofLp_ridgeEstimate (lam : ℝ) (x : ℕ → ι → ℝ) (y : ℕ → ℝ) (t : ℕ) :
    ofLp (ridgeEstimate lam (fun s ↦ toLp 2 (x s)) y t) =
      (designMatrix (lam • 1) x t)⁻¹ *ᵥ ∑ s ∈ range t, y s • x s := by
  rw [ridgeEstimate_def, ← toEuclideanCLM_smul_one, ← toEuclideanCLM_designMatrix,
    ← toEuclideanCLM_inv, ofLp_toEuclideanCLM]
  simp

end LMLExplore
