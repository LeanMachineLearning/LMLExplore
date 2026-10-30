/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.DesignOperator

/-!
# The elliptical potential lemma

For `λ > 0` and a sequence `x : ℕ → E` in a finite-dimensional real inner product space, with
design operators `V_t = designOp λ x t`, the *elliptical potential* `∑_{t < n} ‖x t‖²_{V_t⁻¹}`
controls the width of the confidence ellipsoids of ridge regression along the played actions. By
the determinant update `det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})` and the scalar inequality
`min 1 u ≤ 2 log (1 + u)`, its truncation satisfies
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V_0)`.

## Main statements

* `LMLExplore.min_one_le_two_mul_log_one_add`: `min 1 u ≤ 2 log (1 + u)` for `u ≥ 0`.
* `LMLExplore.sum_min_one_inner_inverse_designOp_le_log_det`: the elliptical potential lemma in
  log-determinant form [LS, Lemma 19.4, first inequality], for `V_0 = λ • 1`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 19.4.
-/

public section

open Finset Real
open scoped InnerProductSpace

namespace LMLExplore

/-- For `u ≥ 0`, `min 1 u ≤ 2 log (1 + u)`. -/
theorem min_one_le_two_mul_log_one_add {u : ℝ} (hu : 0 ≤ u) : min 1 u ≤ 2 * log (1 + u) := by
  have hpos : 0 < u + 2 := by linarith
  have h : min 1 u ≤ 2 * (2 * u / (u + 2)) := by
    rw [show 2 * (2 * u / (u + 2)) = 4 * u / (u + 2) by ring, le_div_iff₀ hpos]
    rcases le_total u 2 with hu2 | hu2
    · nlinarith [mul_le_mul_of_nonneg_right (min_le_right 1 u) hpos.le,
        mul_nonneg hu (sub_nonneg.2 hu2)]
    · nlinarith [mul_le_mul_of_nonneg_right (min_le_left 1 u) hpos.le]
  linarith [le_log_one_add_of_nonneg hu]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {lam : ℝ}

/-- **Elliptical potential lemma**, log-determinant form [LS, Lemma 19.4]: for `λ > 0`,
`∑_{t < n} min 1 ‖x t‖²_{V_t⁻¹} ≤ 2 log (det V_n / det V_0)`, where `V_t = designOp λ x t`. -/
theorem sum_min_one_inner_inverse_designOp_le_log_det (hlam : 0 < lam) (x : ℕ → E) (n : ℕ) :
    ∑ t ∈ range n, min 1 ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ ≤
      2 * log (LinearMap.det (designOp lam x n : E →ₗ[ℝ] E) /
        LinearMap.det (designOp lam x 0 : E →ₗ[ℝ] E)) := by
  have hu (t : ℕ) : 0 ≤ ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ :=
    (isPositive_designOp hlam.le x t).ringInverse.inner_nonneg_right (x t)
  rw [det_designOp_eq_mul_prod hlam, det_designOp_zero,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hlam.ne'),
    log_prod fun t _ ↦ (by linarith [hu t] : (0 : ℝ) < 1 + _).ne', mul_sum]
  exact sum_le_sum fun t _ ↦ min_one_le_two_mul_log_one_add (hu t)

end LMLExplore
