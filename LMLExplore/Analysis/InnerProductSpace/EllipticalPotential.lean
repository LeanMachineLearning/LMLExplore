/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.DesignOperator
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic

/-!
# The elliptical potential lemma

Let `V_t = designOp V₀ x t = V₀ + ∑_{s < t} x s ⊗ x s` be the design operators of a sequence `x`
in a finite-dimensional real inner product space, with a positive definite regularizer `V₀`. The
*elliptical potential* `∑_{t < n} ‖x t‖²_{V_t⁻¹}` controls the width of the confidence ellipsoids
of least squares along the played actions. By the determinant update
`det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})` and the scalar inequality
`min 1 u ≤ 2 log (1 + u)` (`Real.min_one_le_two_mul_log_one_add`), its truncation satisfies
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V₀)`.

When the current vector is included in the design operator, no truncation is needed: by the
Sherman–Morrison formula `‖x t‖²_{V_{t+1}⁻¹} = u / (1 + u)` with `u = ‖x t‖²_{V_t⁻¹}`
(`LMLExplore.inner_ringInverse_designOp_succ`), and
`u / (1 + u) ≤ log (1 + u)`, so `∑_{t < n} ‖x t‖²_{V_{t+1}⁻¹} ≤ log (det V_n / det V₀)`. This is the
log-determinant lemma of the Online Newton Step [Ora, Lemma 7.29], which uses it for the vectors
`√μ • g t`.

## Main statements

* `LMLExplore.sum_min_one_inner_inverse_designOp_le_log_det`: the elliptical potential lemma in
  log-determinant form [LS, Lemma 19.4, first inequality], for a positive definite `V₀`. With
  `LMLExplore.log_det_designOp_div_le` it gives the second inequality of [LS, Lemma 19.4].
* `LMLExplore.sum_inner_ringInverse_designOp_succ_le_log_det`: the log-determinant lemma
  `∑_{t < n} ‖x t‖²_{V_{t+1}⁻¹} ≤ log (det V_n / det V₀)` [Ora, Lemma 7.29], and
  `LMLExplore.mul_sum_inner_ringInverse_designOp_sqrt_smul_succ_le_log_det`, its form
  `μ ∑_{t < n} ‖g t‖²_{S_t⁻¹} ≤ log (det S_{n-1} / det V₀)` for the design operators
  `S_t = V₀ + μ ∑_{s ≤ t} g s ⊗ g s` of the vectors `√μ • g s`.

The design-operator version follows the matrix version `sum_min_one_mahalanobisSq_inv_regGram_le`
of the LMLPapers project (Rémy Degenne, <https://github.com/LeanMachineLearning/LMLPapers>),
restated here for operators with new proofs.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 19.4.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Lemma 7.29.
-/

public section

open ContinuousLinearMap InnerProductSpace Finset Real
open scoped InnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Elliptical potential lemma**, log-determinant form [LS, Lemma 19.4]: for a positive definite
regularizer `V₀` (positive and invertible) and the design operators `V_t = designOp V₀ x t`,
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V₀)`. -/
theorem sum_min_one_inner_inverse_designOp_le_log_det {V₀ : E →L[ℝ] E} (hV₀ : V₀.IsPositive)
    (hV₀u : IsUnit V₀) (x : ℕ → E) (n : ℕ) :
    ∑ t ∈ range n, min 1 ⟪x t, Ring.inverse (designOp V₀ x t) (x t)⟫_ℝ ≤
      2 * log (LinearMap.det (designOp V₀ x n : E →ₗ[ℝ] E) / LinearMap.det (V₀ : E →ₗ[ℝ] E)) := by
  have h0 : LinearMap.det (V₀ : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearMap.isUnit_det _ (hV₀u.map toLinearMapRingHom)).ne_zero
  rw [det_designOp_eq_mul_prod hV₀ hV₀u, mul_div_cancel_left₀ _ h0, log_prod fun t _ ↦
      ((isPositive_designOp hV₀ x t).one_add_inner_ringInverse_pos _).ne', mul_sum]
  exact sum_le_sum fun t _ ↦ min_one_le_two_mul_log_one_add
    ((isPositive_designOp hV₀ x t).ringInverse.inner_nonneg_right (x t))

/-- **The log-determinant lemma** [Ora, Lemma 7.29]: for a positive definite regularizer `V₀`
(positive and invertible) and the design operators `V_t = designOp V₀ x t`, the weighted norms of
the vectors in the design operators that include them satisfy
`∑_{t < n} ‖x t‖²_{V_{t+1}⁻¹} ≤ log (det V_n / det V₀)`. -/
theorem sum_inner_ringInverse_designOp_succ_le_log_det {V₀ : E →L[ℝ] E} (hV₀ : V₀.IsPositive)
    (hV₀u : IsUnit V₀) (x : ℕ → E) (n : ℕ) :
    ∑ t ∈ range n, ⟪x t, Ring.inverse (designOp V₀ x (t + 1)) (x t)⟫_ℝ ≤
      log (LinearMap.det (designOp V₀ x n : E →ₗ[ℝ] E) / LinearMap.det (V₀ : E →ₗ[ℝ] E)) := by
  have h0 : LinearMap.det (V₀ : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearMap.isUnit_det _ (hV₀u.map toLinearMapRingHom)).ne_zero
  rw [det_designOp_eq_mul_prod hV₀ hV₀u, mul_div_cancel_left₀ _ h0, log_prod fun t _ ↦
      ((isPositive_designOp hV₀ x t).one_add_inner_ringInverse_pos _).ne']
  refine sum_le_sum fun t _ ↦ ?_
  -- `u / (1 + u) = 1 - (1 + u)⁻¹ ≤ log (1 + u)`
  have hpos := (isPositive_designOp hV₀ x t).one_add_inner_ringInverse_pos (x t)
  have h := one_sub_inv_le_log_of_pos hpos
  rw [inner_ringInverse_designOp_succ hV₀ hV₀u]
  convert h using 1
  field_simp
  ring

/-- **The log-determinant lemma** for the Online Newton Step [Ora, Lemma 7.29]: for a positive
definite regularizer `V₀`, `μ ≥ 0` and the design operators
`S_t = V₀ + μ ∑_{s ≤ t} g s ⊗ g s = designOp V₀ (√μ • g) (t + 1)`, which include the current
vector, `μ ∑_{t < n} ‖g t‖²_{S_t⁻¹} ≤ log (det S_{n-1} / det V₀)`, where `S_{n-1}` is
`designOp V₀ (√μ • g) n`. -/
theorem mul_sum_inner_ringInverse_designOp_sqrt_smul_succ_le_log_det {V₀ : E →L[ℝ] E}
    (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) {μ : ℝ} (hμ : 0 ≤ μ) (g : ℕ → E) (n : ℕ) :
    μ * ∑ t ∈ range n,
        ⟪g t, Ring.inverse (designOp V₀ (fun s ↦ √μ • g s) (t + 1)) (g t)⟫_ℝ ≤
      log (LinearMap.det (designOp V₀ (fun s ↦ √μ • g s) n : E →ₗ[ℝ] E) /
        LinearMap.det (V₀ : E →ₗ[ℝ] E)) := by
  refine le_of_eq_of_le ?_ (sum_inner_ringInverse_designOp_succ_le_log_det hV₀ hV₀u _ n)
  rw [mul_sum]
  refine sum_congr rfl fun t _ ↦ ?_
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  linear_combination -⟪g t, Ring.inverse (designOp V₀ (fun s ↦ √μ • g s) (t + 1)) (g t)⟫_ℝ *
    mul_self_sqrt hμ

end LMLExplore
