/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.DesignOperator

/-!
# Regularized least squares

Given covariates `x : ℕ → E` in a real inner product space, responses `y : ℕ → ℝ` and a
regularization parameter `λ > 0`, the *ridge estimate* after `t` observations is
`θ̂_t = V_t⁻¹ ∑_{s < t} y s • x s`, where `V_t = designOp λ x t`. It is the unique minimizer of
the regularized squared loss `L_t(θ) = ∑_{s < t} (y s - ⟪θ, x s⟫)² + λ ‖θ‖²`; more precisely,
`L_t(θ) = L_t(θ̂_t) + ⟪θ - θ̂_t, V_t (θ - θ̂_t)⟫`. In the linear model `y s = ⟪θ, x s⟫ + η s`, its
error is `θ̂_t - θ = V_t⁻¹ (∑_{s < t} η s • x s - λ • θ)`, so that
`‖θ̂_t - θ‖_{V_t} ≤ √λ ‖θ‖ + ‖∑_{s < t} η s • x s‖_{V_t⁻¹}`, with `‖v‖_V = √⟪v, V v⟫`.

## Main definitions

* `LMLExplore.ridgeLoss lam x y t θ`: the regularized squared loss `L_t(θ)`.
* `LMLExplore.ridgeEstimate lam x y t`: the ridge estimate `θ̂_t`.

## Main statements

* `LMLExplore.designOp_ridgeEstimate`: the normal equations `V_t θ̂_t = ∑_{s < t} y s • x s`.
* `LMLExplore.ridgeLoss_eq_ridgeLoss_ridgeEstimate_add`:
  `L_t(θ) = L_t(θ̂_t) + ⟪θ - θ̂_t, V_t (θ - θ̂_t)⟫`.
* `LMLExplore.isMinOn_ridgeLoss`, `LMLExplore.eq_ridgeEstimate_of_ridgeLoss_le`: `θ̂_t` is the
  unique minimizer of `L_t` [LS, (19.4)–(19.6)].
* `LMLExplore.ridgeEstimate_sub_eq`: the error `θ̂_t - θ = V_t⁻¹ (∑_{s < t} η s • x s - λ • θ)`
  in the linear model.
* `LMLExplore.sqrt_inner_ridgeEstimate_sub_le`: the bound
  `‖θ̂_t - θ‖_{V_t} ≤ √λ ‖θ‖ + ‖∑_{s < t} η s • x s‖_{V_t⁻¹}` in the linear model, the
  deterministic part of the confidence ellipsoids of ridge regression.

The bound `sqrt_inner_ridgeEstimate_sub_le` follows the matrix version
`sqrt_mahalanobisSq_sub_ridgeEstimate_le` of the LMLPapers project (Rémy Degenne,
<https://github.com/LeanMachineLearning/LMLPapers>), restated here for operators with a new proof.

## References

* Y. Abbasi-Yadkori, D. Pál and Cs. Szepesvári, *Improved algorithms for linear stochastic
  bandits*, NeurIPS 2011, proof of Theorem 2.
* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 19.3 and the proof of Theorem 20.5.
-/

public section

open Finset
open scoped InnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {lam : ℝ}

/-- The **regularized squared loss** `L_t(θ) = ∑_{s < t} (y s - ⟪θ, x s⟫)² + λ ‖θ‖²`. -/
noncomputable def ridgeLoss (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (θ : E) : ℝ :=
  ∑ s ∈ range t, (y s - ⟪θ, x s⟫_ℝ) ^ 2 + lam * ‖θ‖ ^ 2

/-- The **ridge estimate** `θ̂_t = V_t⁻¹ ∑_{s < t} y s • x s`, where `V_t = designOp λ x t`. -/
noncomputable def ridgeEstimate (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) : E :=
  Ring.inverse (designOp lam x t) (∑ s ∈ range t, y s • x s)

/-- The defining equation of `ridgeLoss`. -/
theorem ridgeLoss_def (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (θ : E) :
    ridgeLoss lam x y t θ = ∑ s ∈ range t, (y s - ⟪θ, x s⟫_ℝ) ^ 2 + lam * ‖θ‖ ^ 2 :=
  (rfl)

/-- The defining equation of `ridgeEstimate`. -/
theorem ridgeEstimate_def (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    ridgeEstimate lam x y t = Ring.inverse (designOp lam x t) (∑ s ∈ range t, y s • x s) :=
  (rfl)

/-- The regularized squared loss is the quadratic function
`L_t(θ) = ∑_{s < t} y s ² - 2 ⟪θ, ∑_{s < t} y s • x s⟫ + ⟪θ, V_t θ⟫`. -/
theorem ridgeLoss_eq (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (θ : E) :
    ridgeLoss lam x y t θ = ∑ s ∈ range t, y s ^ 2 - 2 * ⟪θ, ∑ s ∈ range t, y s • x s⟫_ℝ +
      ⟪θ, designOp lam x t θ⟫_ℝ := by
  rw [ridgeLoss, inner_designOp_apply_self, inner_sum]
  simp only [inner_smul_right]
  have h : ∑ s ∈ range t, (y s - ⟪θ, x s⟫_ℝ) ^ 2 = ∑ s ∈ range t, y s ^ 2 -
      2 * ∑ s ∈ range t, y s * ⟪θ, x s⟫_ℝ + ∑ s ∈ range t, ⟪x s, θ⟫_ℝ ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun s _ ↦ by rw [real_inner_comm θ (x s)]; ring
  rw [h]
  ring

variable [CompleteSpace E]

/-- The **normal equations**: for `λ > 0`, `V_t θ̂_t = ∑_{s < t} y s • x s`. -/
theorem designOp_ridgeEstimate (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    designOp lam x t (ridgeEstimate lam x y t) = ∑ s ∈ range t, y s • x s :=
  (designOp lam x t).apply_ringInverse_apply (isUnit_designOp hlam x t) _

/-- For `λ > 0`, the regularized squared loss is
`L_t(θ) = L_t(θ̂_t) + ⟪θ - θ̂_t, V_t (θ - θ̂_t)⟫`. -/
theorem ridgeLoss_eq_ridgeLoss_ridgeEstimate_add (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ)
    (t : ℕ) (θ : E) :
    ridgeLoss lam x y t θ = ridgeLoss lam x y t (ridgeEstimate lam x y t) +
      ⟪θ - ridgeEstimate lam x y t, designOp lam x t (θ - ridgeEstimate lam x y t)⟫_ℝ := by
  have hsymm : ⟪ridgeEstimate lam x y t, designOp lam x t θ⟫_ℝ
      = ⟪θ, designOp lam x t (ridgeEstimate lam x y t)⟫_ℝ := by
    rw [← (isPositive_designOp hlam.le x t).inner_left_eq_inner_right, real_inner_comm]
  rw [ridgeLoss_eq, ridgeLoss_eq, ← designOp_ridgeEstimate hlam x y t, map_sub, inner_sub_left,
    inner_sub_right, inner_sub_right]
  linarith

/-- For `λ > 0`, the ridge estimate minimizes the regularized squared loss. -/
theorem ridgeLoss_ridgeEstimate_le (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (θ : E) :
    ridgeLoss lam x y t (ridgeEstimate lam x y t) ≤ ridgeLoss lam x y t θ := by
  rw [ridgeLoss_eq_ridgeLoss_ridgeEstimate_add hlam x y t θ]
  exact le_add_of_nonneg_right ((isPositive_designOp hlam.le x t).inner_nonneg_right _)

/-- For `λ > 0`, the ridge estimate is a minimizer of the regularized squared loss on the whole
space. -/
theorem isMinOn_ridgeLoss (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    IsMinOn (ridgeLoss lam x y t) Set.univ (ridgeEstimate lam x y t) :=
  isMinOn_univ_iff.2 (ridgeLoss_ridgeEstimate_le hlam x y t)

/-- For `λ > 0`, the ridge estimate is the unique minimizer of the regularized squared loss. -/
theorem eq_ridgeEstimate_of_ridgeLoss_le (hlam : 0 < lam) {x : ℕ → E} {y : ℕ → ℝ} {t : ℕ}
    {θ : E} (h : ridgeLoss lam x y t θ ≤ ridgeLoss lam x y t (ridgeEstimate lam x y t)) :
    θ = ridgeEstimate lam x y t := by
  rw [ridgeLoss_eq_ridgeLoss_ridgeEstimate_add hlam x y t θ] at h
  have h1 := mul_norm_sq_le_inner_designOp_apply lam x t (θ - ridgeEstimate lam x y t)
  have h2 : ‖θ - ridgeEstimate lam x y t‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  rw [← sub_eq_zero]
  simpa using h2

/-- The **error of the ridge estimate** in the linear model `y s = ⟪θ, x s⟫ + η s`: for `λ > 0`,
`θ̂_t - θ = V_t⁻¹ (∑_{s < t} η s • x s - λ • θ)`. -/
theorem ridgeEstimate_sub_eq (hlam : 0 < lam) (x : ℕ → E) {y η : ℕ → ℝ} (θ : E) (t : ℕ)
    (hy : ∀ s, y s = ⟪θ, x s⟫_ℝ + η s) :
    ridgeEstimate lam x y t - θ =
      Ring.inverse (designOp lam x t) (∑ s ∈ range t, η s • x s - lam • θ) := by
  have hb : ∑ s ∈ range t, y s • x s
      = designOp lam x t θ + (∑ s ∈ range t, η s • x s - lam • θ) := by
    simp only [designOp_apply, hy, add_smul, sum_add_distrib, real_inner_comm θ]
    abel
  rw [ridgeEstimate, hb, map_add,
    (designOp lam x t).ringInverse_apply_apply (isUnit_designOp hlam x t), add_sub_cancel_left]

/-- **Deterministic confidence bound** in the linear model `y s = ⟪θ, x s⟫ + η s`: for `λ > 0`,
`‖θ̂_t - θ‖_{V_t} ≤ √λ ‖θ‖ + ‖S_t‖_{V_t⁻¹}`, where `S_t = ∑_{s < t} η s • x s`. -/
theorem sqrt_inner_ridgeEstimate_sub_le (hlam : 0 < lam) (x : ℕ → E) {y η : ℕ → ℝ} (θ : E)
    (t : ℕ) (hy : ∀ s, y s = ⟪θ, x s⟫_ℝ + η s) :
    √⟪ridgeEstimate lam x y t - θ, designOp lam x t (ridgeEstimate lam x y t - θ)⟫_ℝ ≤
      √lam * ‖θ‖ + √⟪∑ s ∈ range t, η s • x s,
        Ring.inverse (designOp lam x t) (∑ s ∈ range t, η s • x s)⟫_ℝ := by
  set V := designOp lam x t
  set S := ∑ s ∈ range t, η s • x s
  -- `‖θ̂_t - θ‖_{V_t} = ‖S_t - λ θ‖_{V_t⁻¹}`, then the triangle inequality for `‖·‖_{V_t⁻¹}`
  have heq : ⟪ridgeEstimate lam x y t - θ, V (ridgeEstimate lam x y t - θ)⟫_ℝ =
      ⟪-(lam • θ) + S, Ring.inverse V (-(lam • θ) + S)⟫_ℝ := by
    rw [ridgeEstimate_sub_eq hlam x θ t hy, V.apply_ringInverse_apply (isUnit_designOp hlam x t),
      real_inner_comm, neg_add_eq_sub]
  have hθ : √⟪-(lam • θ), Ring.inverse V (-(lam • θ))⟫_ℝ ≤ √lam * ‖θ‖ := by
    rw [Real.sqrt_le_left (by positivity)]
    simp [inner_smul_left, inner_smul_right, mul_pow, Real.sq_sqrt hlam.le]
    nlinarith [mul_inner_ringInverse_designOp_apply_le hlam x t θ]
  rw [heq]
  exact ((isPositive_designOp hlam.le x t).ringInverse.sqrt_inner_add_le _ _).trans
    (add_le_add_left hθ _)

end LMLExplore
