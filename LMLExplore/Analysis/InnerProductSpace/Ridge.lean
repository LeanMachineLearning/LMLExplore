/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.DesignOperator

/-!
# Regularized least squares

Given covariates `x : ℕ → E` in a real inner product space, responses `y : ℕ → ℝ` and a
regularization parameter `λ > 0`, the *ridge estimate* after `t` observations is
`θ̂_t = V_t⁻¹ ∑_{s < t} y s • x s`, where `V_t = designOp (λ • 1) x t`. It is the unique
minimizer of the regularized squared loss `L_t(θ) = ∑_{s < t} (y s - ⟪θ, x s⟫)² + λ ‖θ‖²`; more
precisely, `L_t(θ) = L_t(θ̂_t) + ⟪θ - θ̂_t, V_t (θ - θ̂_t)⟫`. In the linear model
`y s = ⟪θ, x s⟫ + η s`, its error is `θ̂_t - θ = V_t⁻¹ (∑_{s < t} η s • x s - λ • θ)`, so that
`‖θ̂_t - θ‖_{V_t} ≤ √λ ‖θ‖ + ‖∑_{s < t} η s • x s‖_{V_t⁻¹}`, with `‖v‖_V = √⟪v, V v⟫`.

## Main definitions

* `LMLExplore.ridgeLoss lam x y t θ`: the regularized squared loss `L_t(θ)`.
* `LMLExplore.ridgeEstimate lam x y t`: the ridge estimate `θ̂_t`.

## Main statements

* `LMLExplore.ridgeEstimate_congr`: `θ̂_t` only depends on the first `t` observations.
* `LMLExplore.designOp_ridgeEstimate`: the normal equations `V_t θ̂_t = ∑_{s < t} y s • x s`.
* `LMLExplore.ridgeLoss_eq_ridgeLoss_add_of_designOp_apply_eq`: for every solution `θ₀` of the
  normal equations, `L_t(θ) = L_t(θ₀) + ⟪θ - θ₀, V_t (θ - θ₀)⟫`; for the ridge estimate this is
  `LMLExplore.ridgeLoss_eq_ridgeLoss_ridgeEstimate_add`.
* `LMLExplore.isMinOn_ridgeLoss`, `LMLExplore.eq_ridgeEstimate_of_ridgeLoss_le`: `θ̂_t` is the
  unique minimizer of `L_t` [LS, (19.4)–(19.6)].
* `LMLExplore.ridgeEstimate_sub_eq`: the error `θ̂_t - θ = V_t⁻¹ (∑_{s < t} η s • x s - λ • θ)`
  in the linear model.
* `LMLExplore.sqrt_inner_ridgeEstimate_sub_le`: the bound
  `‖θ̂_t - θ‖_{V_t} ≤ √λ ‖θ‖ + ‖∑_{s < t} η s • x s‖_{V_t⁻¹}` in the linear model, the
  deterministic part of the confidence ellipsoids of ridge regression.
* `LMLExplore.abs_inner_ridgeEstimate_sub_le`: on the confidence ellipsoid
  `‖θ̂_t - θ‖_{V_t} ≤ r`, the prediction error is `|⟪θ̂_t - θ, v⟫| ≤ r ‖v‖_{V_t⁻¹}`.

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

/-- The **ridge estimate** `θ̂_t = V_t⁻¹ ∑_{s < t} y s • x s`, where
`V_t = designOp (λ • 1) x t`. -/
noncomputable def ridgeEstimate (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) : E :=
  Ring.inverse (designOp (lam • 1) x t) (∑ s ∈ range t, y s • x s)

/-- The defining equation of `ridgeLoss`. -/
theorem ridgeLoss_def (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (θ : E) :
    ridgeLoss lam x y t θ = ∑ s ∈ range t, (y s - ⟪θ, x s⟫_ℝ) ^ 2 + lam * ‖θ‖ ^ 2 :=
  (rfl)

/-- The defining equation of `ridgeEstimate`. -/
theorem ridgeEstimate_def (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    ridgeEstimate lam x y t = Ring.inverse (designOp (lam • 1) x t) (∑ s ∈ range t, y s • x s) :=
  (rfl)

/-- The ridge estimate `θ̂_t` only depends on the covariates `x s` and the responses `y s` for
`s < t`. -/
theorem ridgeEstimate_congr {x x' : ℕ → E} {y y' : ℕ → ℝ} {t : ℕ} (hx : ∀ s < t, x s = x' s)
    (hy : ∀ s < t, y s = y' s) :
    ridgeEstimate lam x y t = ridgeEstimate lam x' y' t := by
  rw [ridgeEstimate, ridgeEstimate, designOp_congr hx,
    sum_congr rfl fun s hs ↦ by rw [hx s (mem_range.1 hs), hy s (mem_range.1 hs)]]

/-- The regularized squared loss is the quadratic function
`L_t(θ) = ∑_{s < t} y s ² - 2 ⟪θ, ∑_{s < t} y s • x s⟫ + ⟪θ, V_t θ⟫`. -/
theorem ridgeLoss_eq (lam : ℝ) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (θ : E) :
    ridgeLoss lam x y t θ = ∑ s ∈ range t, y s ^ 2 - 2 * ⟪θ, ∑ s ∈ range t, y s • x s⟫_ℝ +
      ⟪θ, designOp (lam • 1) x t θ⟫_ℝ := by
  rw [ridgeLoss, inner_designOp_smul_one_apply_self, inner_sum]
  simp only [inner_smul_right]
  have h : ∑ s ∈ range t, (y s - ⟪θ, x s⟫_ℝ) ^ 2 = ∑ s ∈ range t, y s ^ 2 -
      2 * ∑ s ∈ range t, y s * ⟪θ, x s⟫_ℝ + ∑ s ∈ range t, ⟪x s, θ⟫_ℝ ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun s _ ↦ by rw [real_inner_comm θ (x s)]; ring
  rw [h]
  ring

/-- The **normal equations**: for `λ > 0`, `V_t θ̂_t = ∑_{s < t} y s • x s`. -/
theorem designOp_ridgeEstimate (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    designOp (lam • 1) x t (ridgeEstimate lam x y t) = ∑ s ∈ range t, y s • x s :=
  ContinuousLinearMap.apply_ringInverse_apply (isUnit_designOp_smul_one hlam x t) _

/-- The regularized squared loss around a solution `θ₀` of the normal equations
`V_t θ₀ = ∑_{s < t} y s • x s`: `L_t(θ) = L_t(θ₀) + ⟪θ - θ₀, V_t (θ - θ₀)⟫`. -/
theorem ridgeLoss_eq_ridgeLoss_add_of_designOp_apply_eq {x : ℕ → E} {y : ℕ → ℝ} {t : ℕ} {θ₀ : E}
    (h₀ : designOp (lam • 1) x t θ₀ = ∑ s ∈ range t, y s • x s) (θ : E) :
    ridgeLoss lam x y t θ = ridgeLoss lam x y t θ₀ +
      ⟪θ - θ₀, designOp (lam • 1) x t (θ - θ₀)⟫_ℝ := by
  have hsymm : ⟪θ₀, designOp (lam • 1) x t θ⟫_ℝ = ⟪θ, designOp (lam • 1) x t θ₀⟫_ℝ := by
    simp only [designOp_smul_one_apply, inner_add_right, inner_sum, real_inner_smul_right]
    congr 1
    · rw [real_inner_comm]
    · exact sum_congr rfl fun s _ ↦ by rw [real_inner_comm θ₀ (x s), real_inner_comm θ (x s),
        mul_comm]
  rw [ridgeLoss_eq, ridgeLoss_eq, ← h₀, map_sub, inner_sub_left, inner_sub_right,
    inner_sub_right]
  linarith

/-- For `λ > 0`, the regularized squared loss is
`L_t(θ) = L_t(θ̂_t) + ⟪θ - θ̂_t, V_t (θ - θ̂_t)⟫`. -/
theorem ridgeLoss_eq_ridgeLoss_ridgeEstimate_add (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ)
    (t : ℕ) (θ : E) :
    ridgeLoss lam x y t θ = ridgeLoss lam x y t (ridgeEstimate lam x y t) +
      ⟪θ - ridgeEstimate lam x y t, designOp (lam • 1) x t (θ - ridgeEstimate lam x y t)⟫_ℝ :=
  ridgeLoss_eq_ridgeLoss_add_of_designOp_apply_eq (designOp_ridgeEstimate hlam x y t) θ

/-- For `λ > 0`, the ridge estimate minimizes the regularized squared loss. -/
theorem ridgeLoss_ridgeEstimate_le (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (θ : E) :
    ridgeLoss lam x y t (ridgeEstimate lam x y t) ≤ ridgeLoss lam x y t θ := by
  rw [ridgeLoss_eq_ridgeLoss_ridgeEstimate_add hlam x y t θ]
  exact le_add_of_nonneg_right ((isPositive_designOp_smul_one hlam.le x t).inner_nonneg_right _)

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
      Ring.inverse (designOp (lam • 1) x t) (∑ s ∈ range t, η s • x s - lam • θ) := by
  have hb : ∑ s ∈ range t, y s • x s
      = designOp (lam • 1) x t θ + (∑ s ∈ range t, η s • x s - lam • θ) := by
    simp only [designOp_smul_one_apply, hy, add_smul, sum_add_distrib, real_inner_comm θ]
    abel
  rw [ridgeEstimate, hb, map_add,
    ContinuousLinearMap.ringInverse_apply_apply (isUnit_designOp_smul_one hlam x t),
    add_sub_cancel_left]

/-- **Deterministic confidence bound** in the linear model `y s = ⟪θ, x s⟫ + η s`: for `λ > 0`,
`‖θ̂_t - θ‖_{V_t} ≤ √λ ‖θ‖ + ‖S_t‖_{V_t⁻¹}`, where `S_t = ∑_{s < t} η s • x s`. -/
theorem sqrt_inner_ridgeEstimate_sub_le (hlam : 0 < lam) (x : ℕ → E) {y η : ℕ → ℝ} (θ : E)
    (t : ℕ) (hy : ∀ s, y s = ⟪θ, x s⟫_ℝ + η s) :
    √⟪ridgeEstimate lam x y t - θ, designOp (lam • 1) x t (ridgeEstimate lam x y t - θ)⟫_ℝ ≤
      √lam * ‖θ‖ + √⟪∑ s ∈ range t, η s • x s,
        Ring.inverse (designOp (lam • 1) x t) (∑ s ∈ range t, η s • x s)⟫_ℝ := by
  set V := designOp (lam • 1) x t
  set S := ∑ s ∈ range t, η s • x s
  -- `‖θ̂_t - θ‖_{V_t} = ‖S_t - λ θ‖_{V_t⁻¹}`, then the triangle inequality for `‖·‖_{V_t⁻¹}`
  have heq : ⟪ridgeEstimate lam x y t - θ, V (ridgeEstimate lam x y t - θ)⟫_ℝ =
      ⟪-(lam • θ) + S, Ring.inverse V (-(lam • θ) + S)⟫_ℝ := by
    rw [ridgeEstimate_sub_eq hlam x θ t hy,
      ContinuousLinearMap.apply_ringInverse_apply (isUnit_designOp_smul_one hlam x t),
      real_inner_comm, neg_add_eq_sub]
  have hθ : √⟪-(lam • θ), Ring.inverse V (-(lam • θ))⟫_ℝ ≤ √lam * ‖θ‖ := by
    rw [Real.sqrt_le_left (by positivity)]
    simp [inner_smul_left, inner_smul_right, mul_pow, Real.sq_sqrt hlam.le]
    nlinarith [mul_inner_ringInverse_designOp_apply_le hlam x t θ]
  rw [heq]
  exact ((isPositive_designOp_smul_one hlam.le x t).ringInverse.sqrt_inner_add_le _ _).trans
    (add_le_add_left hθ _)

/-- **Prediction error of the ridge estimate**: for `λ > 0`, if `θ` lies in the confidence
ellipsoid `‖θ̂_t - θ‖_{V_t} ≤ r`, then `|⟪θ̂_t - θ, v⟫| ≤ r ‖v‖_{V_t⁻¹}` for every `v`. -/
theorem abs_inner_ridgeEstimate_sub_le (hlam : 0 < lam) (x : ℕ → E) (y : ℕ → ℝ) (t : ℕ)
    {θ : E} {r : ℝ}
    (hθ : √⟪ridgeEstimate lam x y t - θ,
      designOp (lam • 1) x t (ridgeEstimate lam x y t - θ)⟫_ℝ ≤ r) (v : E) :
    |⟪ridgeEstimate lam x y t - θ, v⟫_ℝ| ≤
      r * √⟪v, Ring.inverse (designOp (lam • 1) x t) v⟫_ℝ :=
  ((isPositive_designOp_smul_one hlam.le x t).abs_inner_le_sqrt_mul_sqrt_ringInverse
    (isUnit_designOp_smul_one hlam x t) _ v).trans
      (mul_le_mul_of_nonneg_right hθ (Real.sqrt_nonneg _))

end LMLExplore
