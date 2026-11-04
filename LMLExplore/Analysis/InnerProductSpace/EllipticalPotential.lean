/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.DesignOperator
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic

/-!
# The elliptical potential lemma

Let `V : ℕ → E →L[ℝ] E` be a sequence of operators on a finite-dimensional real inner product
space, with `V 0` positive definite and rank-one updates `V (t + 1) = V t + x t ⊗ x t`. The
*elliptical potential* `∑_{t < n} ‖x t‖²_{V_t⁻¹}` controls the width of the confidence ellipsoids
of ridge regression along the played actions. By the determinant update
`det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})` and the scalar inequality
`min 1 u ≤ 2 log (1 + u)` (`Real.min_one_le_two_mul_log_one_add`), its truncation satisfies
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V_0)`.

## Main statements

* `LMLExplore.isPositive_of_add_rankOne`, `LMLExplore.isUnit_of_add_rankOne`: the rank-one updates
  of a positive definite `V_0` stay positive and invertible.
* `LMLExplore.sum_min_one_inner_inverse_le_log_det`: the elliptical potential lemma in
  log-determinant form [LS, Lemma 19.4, first inequality], for a positive definite `V_0`.
* `LMLExplore.sum_min_one_inner_inverse_designOp_le_log_det`: its specialization to the design
  operators `V_t = designOp λ x t`, for which `V_0 = λ • 1`.
* `LMLExplore.log_det_designOp_div_pow_le`: `log (det V_t / λ ^ d) ≤ d log (1 + t L² / (λ d))`
  for vectors bounded by `L` [LS, (20.9)].
* `LMLExplore.sum_min_one_inner_inverse_designOp_le_mul_log`: the elliptical potential lemma for
  vectors bounded by `L`, `∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 d log (1 + n L² / (λ d))`
  [LS, Lemma 19.4, second inequality, for `V_0 = λ • 1`].

The design-operator version follows the matrix version `sum_min_one_mahalanobisSq_inv_regGram_le`
of the LMLPapers project (Rémy Degenne, <https://github.com/LeanMachineLearning/LMLPapers>),
restated here for operators with new proofs.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 19.4.
-/

public section

open ContinuousLinearMap InnerProductSpace Finset Real
open scoped InnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- If `V 0` is positive and `V (t + 1) = V t + x t ⊗ x t`, then every `V t` is positive. -/
theorem isPositive_of_add_rankOne {V : ℕ → E →L[ℝ] E} {x : ℕ → E}
    (hV : ∀ t, V (t + 1) = V t + rankOne ℝ (x t) (x t)) (hV0 : (V 0).IsPositive) (t : ℕ) :
    (V t).IsPositive := by
  induction t with
  | zero => exact hV0
  | succ t ih =>
    rw [hV]
    exact ih.add (isPositive_rankOne_self _)

omit [FiniteDimensional ℝ E] in
/-- If `V 0` is positive and invertible and `V (t + 1) = V t + x t ⊗ x t`, then every `V t` is
invertible. -/
theorem isUnit_of_add_rankOne {V : ℕ → E →L[ℝ] E} {x : ℕ → E}
    (hV : ∀ t, V (t + 1) = V t + rankOne ℝ (x t) (x t)) (hV0 : (V 0).IsPositive)
    (hV0u : IsUnit (V 0)) (t : ℕ) :
    IsUnit (V t) := by
  induction t with
  | zero => exact hV0u
  | succ t ih =>
    rw [hV]
    exact isUnit_add_rankOne ih _ _
      ((isPositive_of_add_rankOne hV hV0 t).one_add_inner_ringInverse_pos _).ne'

/-- **Elliptical potential lemma**, log-determinant form [LS, Lemma 19.4]: if `V 0` is positive
definite and `V (t + 1) = V t + x t ⊗ x t`, then
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V_0)`. -/
theorem sum_min_one_inner_inverse_le_log_det {V : ℕ → E →L[ℝ] E} {x : ℕ → E}
    (hV : ∀ t, V (t + 1) = V t + rankOne ℝ (x t) (x t)) (hV0 : (V 0).IsPositive)
    (hV0u : IsUnit (V 0)) (n : ℕ) :
    ∑ t ∈ range n, min 1 ⟪x t, Ring.inverse (V t) (x t)⟫_ℝ ≤
      2 * log (LinearMap.det (V n : E →ₗ[ℝ] E) / LinearMap.det (V 0 : E →ₗ[ℝ] E)) := by
  have hu (t : ℕ) : 0 ≤ ⟪x t, Ring.inverse (V t) (x t)⟫_ℝ :=
    (isPositive_of_add_rankOne hV hV0 t).ringInverse.inner_nonneg_right (x t)
  have h0 : LinearMap.det (V 0 : E →ₗ[ℝ] E) ≠ 0 :=
    (LinearMap.isUnit_det _ (hV0u.map toLinearMapRingHom)).ne_zero
  rw [det_eq_mul_prod_of_add_rankOne hV (isUnit_of_add_rankOne hV hV0 hV0u),
    mul_div_cancel_left₀ _ h0, log_prod fun t _ ↦
      ((isPositive_of_add_rankOne hV hV0 t).one_add_inner_ringInverse_pos _).ne', mul_sum]
  exact sum_le_sum fun t _ ↦ min_one_le_two_mul_log_one_add (hu t)

/-- **Elliptical potential lemma** for design operators [LS, Lemma 19.4]: for `λ > 0`,
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V_0)`, where `V_t = designOp λ x t`. -/
theorem sum_min_one_inner_inverse_designOp_le_log_det {lam : ℝ} (hlam : 0 < lam) (x : ℕ → E)
    (n : ℕ) :
    ∑ t ∈ range n, min 1 ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ ≤
      2 * log (LinearMap.det (designOp lam x n : E →ₗ[ℝ] E) /
        LinearMap.det (designOp lam x 0 : E →ₗ[ℝ] E)) :=
  have := FiniteDimensional.complete ℝ E
  sum_min_one_inner_inverse_le_log_det (designOp_succ lam x) (isPositive_designOp hlam.le x 0)
    (isUnit_designOp hlam x 0) n

/-- [LS, (20.9)] in logarithmic form: for `λ > 0`, if `‖x s‖ ≤ L` for all `s < t`, then
`log (det V_t(λ) / λ ^ d) ≤ d log (1 + t L² / (λ d))`. -/
theorem log_det_designOp_div_pow_le {lam : ℝ} (hlam : 0 < lam) (x : ℕ → E) {t : ℕ} {L : ℝ}
    (hx : ∀ s < t, ‖x s‖ ≤ L) :
    log (LinearMap.det (designOp lam x t : E →ₗ[ℝ] E) / lam ^ Module.finrank ℝ E) ≤
      Module.finrank ℝ E * log (1 + t * L ^ 2 / (lam * Module.finrank ℝ E)) := by
  rw [← log_pow]
  exact log_le_log (div_pos (det_designOp_pos hlam _ t) (pow_pos hlam _))
    (det_designOp_div_pow_le hlam x hx)

/-- **Elliptical potential lemma** for design operators and bounded vectors [LS, Lemma 19.4]: for
`λ > 0`, if `‖x t‖ ≤ L` for all `t < n`, then
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 d log (1 + n L² / (λ d))`, where `V_t = designOp λ x t`. -/
theorem sum_min_one_inner_inverse_designOp_le_mul_log {lam : ℝ} (hlam : 0 < lam) (x : ℕ → E)
    {n : ℕ} {L : ℝ} (hx : ∀ t < n, ‖x t‖ ≤ L) :
    ∑ t ∈ range n, min 1 ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ ≤
      2 * (Module.finrank ℝ E * log (1 + n * L ^ 2 / (lam * Module.finrank ℝ E))) := by
  refine (sum_min_one_inner_inverse_designOp_le_log_det hlam x n).trans ?_
  rw [det_designOp_zero]
  gcongr
  exact log_det_designOp_div_pow_le hlam x hx

end LMLExplore
