/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.RankOne
public import TauCeti.Analysis.InnerProductSpace.Frame

/-!
# Design operators of regularized least squares

For `λ : ℝ` and a sequence `x : ℕ → E` in a real inner product space, the *design operator*
`V_t(λ) = λ • 1 + ∑_{s < t} x s ⊗ x s`, where `x ⊗ x = rankOne ℝ x x` is the operator
`v ↦ ⟪x, v⟫ • x`, is the regularized Gram operator of ridge regression and of linear bandit
algorithms. Its unregularized part is Tau Ceti's frame operator of the family `(x s)_{s < t}`.
The weighted norm `‖v‖²_{V⁻¹}` is `⟪v, V⁻¹ v⟫`, with `V⁻¹ = Ring.inverse V`.

## Main definitions

* `LMLExplore.designOp lam x t`: the design operator `V_t(λ)`.

## Main statements

* `LMLExplore.toLinearMap_designOp`: `V_t(λ) = λ • id + frameOperator ℝ (fun s : Fin t ↦ x s)`.
* `LMLExplore.isPositive_designOp`: `V_t(λ)` is positive for `λ ≥ 0`;
  `LMLExplore.mul_norm_sq_le_inner_designOp_apply`: `λ ‖v‖² ≤ ⟪v, V_t(λ) v⟫`.
* `LMLExplore.isUnit_designOp`: `V_t(λ)` is invertible for `λ > 0`.
* `LMLExplore.inner_ring_inverse_apply_self_nonneg`: `0 ≤ ⟪v, V⁻¹ v⟫` for a positive `V`.
* `LMLExplore.ring_inverse_designOp_succ`: the rank-one update of the inverse
  (Sherman–Morrison formula).
* `LMLExplore.det_designOp_succ`: `det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})`, and
  `LMLExplore.det_designOp_eq_mul_prod`: `det V_t = λ ^ d * ∏_{s < t} (1 + ‖x s‖²_{V_s⁻¹})`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 19.2 and equation (19.9).
-/

public section

open ContinuousLinearMap InnerProductSpace Finset Module
open scoped InnerProductSpace

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {lam : ℝ}

/-- The **design operator** `V_t(λ) = λ • 1 + ∑_{s < t} x s ⊗ x s`, where `x ⊗ x` is the
rank-one operator `v ↦ ⟪x, v⟫ • x`. -/
noncomputable def designOp (lam : ℝ) (x : ℕ → E) (t : ℕ) : E →L[ℝ] E :=
  lam • 1 + ∑ s ∈ range t, rankOne ℝ (x s) (x s)

theorem designOp_apply (lam : ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    designOp lam x t v = lam • v + ∑ s ∈ range t, ⟪x s, v⟫_ℝ • x s := by
  simp [designOp]

@[simp]
theorem designOp_zero (lam : ℝ) (x : ℕ → E) : designOp lam x 0 = lam • 1 := by
  simp [designOp]

/-- The design operator is updated by a rank-one term at each step. -/
theorem designOp_succ (lam : ℝ) (x : ℕ → E) (t : ℕ) :
    designOp lam x (t + 1) = designOp lam x t + rankOne ℝ (x t) (x t) := by
  rw [designOp, designOp, sum_range_succ, add_assoc]

theorem inner_designOp_apply_self (lam : ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    ⟪v, designOp lam x t v⟫_ℝ = lam * ‖v‖ ^ 2 + ∑ s ∈ range t, ⟪x s, v⟫_ℝ ^ 2 := by
  rw [designOp_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, inner_sum]
  congr 1
  refine sum_congr rfl fun s _ ↦ ?_
  rw [inner_smul_right, real_inner_comm (x s) v, sq]

/-- The design operator is `λ • id` plus Tau Ceti's frame operator of `(x s)_{s < t}`. -/
theorem toLinearMap_designOp (lam : ℝ) (x : ℕ → E) (t : ℕ) :
    (designOp lam x t : E →ₗ[ℝ] E) =
      lam • LinearMap.id + TauCeti.frameOperator ℝ (fun s : Fin t ↦ x s) := by
  ext v
  simp [designOp_apply, TauCeti.frameOperator_apply,
    Fin.sum_univ_eq_sum_range (fun s ↦ ⟪x s, v⟫_ℝ • x s)]

/-- The design operator is positive for `λ ≥ 0`. -/
theorem isPositive_designOp (hlam : 0 ≤ lam) (x : ℕ → E) (t : ℕ) :
    (designOp lam x t).IsPositive :=
  (isPositive_one.smul_of_nonneg hlam).add (isPositive_sum _ fun _ _ ↦ isPositive_rankOne_self _)

theorem mul_norm_sq_le_inner_designOp_apply (lam : ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    lam * ‖v‖ ^ 2 ≤ ⟪v, designOp lam x t v⟫_ℝ := by
  rw [inner_designOp_apply_self]
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- The design operator is invertible for `λ > 0`. -/
theorem isUnit_designOp [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    IsUnit (designOp lam x t) := by
  have := FiniteDimensional.complete ℝ E
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro v hv
  have h := mul_norm_sq_le_inner_designOp_apply lam x t v
  rw [ContinuousLinearMap.coe_coe] at hv
  rw [hv, inner_zero_right] at h
  have : ‖v‖ ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
  simpa using this

/-- For a positive operator `V`, the weighted square norm `⟪v, V⁻¹ v⟫` is nonnegative. -/
theorem inner_ring_inverse_apply_self_nonneg {V : E →L[ℝ] E} (hV : V.IsPositive) (v : E) :
    0 ≤ ⟪v, Ring.inverse V v⟫_ℝ := by
  by_cases hu : IsUnit V
  · have hv : V (Ring.inverse V v) = v := by
      change (V * Ring.inverse V) v = v
      rw [Ring.mul_inverse_cancel V hu]
      rfl
    calc 0 ≤ ⟪V (Ring.inverse V v), Ring.inverse V v⟫_ℝ := hV.inner_nonneg_left _
      _ = ⟪v, Ring.inverse V v⟫_ℝ := by rw [hv]
  · simp [Ring.inverse_non_unit V hu]

/-- **Sherman–Morrison formula** for the design operator: for `λ > 0`,
`V_{t+1}⁻¹ = V_t⁻¹ - (1 + ‖x t‖²_{V_t⁻¹})⁻¹ • (V_t⁻¹ x t) ⊗ (V_t⁻¹ x t)`. -/
theorem ring_inverse_designOp_succ [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E)
    (t : ℕ) :
    Ring.inverse (designOp lam x (t + 1)) = Ring.inverse (designOp lam x t) -
      (1 + ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ)⁻¹ •
        rankOne ℝ (Ring.inverse (designOp lam x t) (x t))
          (Ring.inverse (designOp lam x t) (x t)) := by
  rw [designOp_succ]
  exact ring_inverse_add_rankOne_self (isUnit_designOp hlam x t)
    (isPositive_designOp hlam.le x t).isSymmetric (x t) (add_pos_of_pos_of_nonneg one_pos
      (inner_ring_inverse_apply_self_nonneg (isPositive_designOp hlam.le x t) _)).ne'

theorem det_designOp_zero [FiniteDimensional ℝ E] (lam : ℝ) (x : ℕ → E) :
    LinearMap.det (designOp lam x 0 : E →ₗ[ℝ] E) = lam ^ finrank ℝ E := by
  simp [LinearMap.det_smul]

/-- The determinant of the design operator after a rank-one update [LS, (19.9)]: for `λ > 0`,
`det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})`. -/
theorem det_designOp_succ [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    LinearMap.det (designOp lam x (t + 1) : E →ₗ[ℝ] E) =
      LinearMap.det (designOp lam x t : E →ₗ[ℝ] E) *
        (1 + ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ) := by
  rw [designOp_succ, det_add_rankOne (isUnit_designOp hlam x t)]

/-- For `λ > 0`, `det V_t = λ ^ d * ∏_{s < t} (1 + ‖x s‖²_{V_s⁻¹})`. -/
theorem det_designOp_eq_mul_prod [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    LinearMap.det (designOp lam x t : E →ₗ[ℝ] E) =
      lam ^ finrank ℝ E * ∏ s ∈ range t, (1 + ⟪x s, Ring.inverse (designOp lam x s) (x s)⟫_ℝ) := by
  induction t with
  | zero => simp
  | succ t ih => rw [det_designOp_succ hlam, ih, prod_range_succ, mul_assoc]

theorem det_designOp_pos [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    0 < LinearMap.det (designOp lam x t : E →ₗ[ℝ] E) := by
  rw [det_designOp_eq_mul_prod hlam]
  exact mul_pos (pow_pos hlam _) (prod_pos fun s _ ↦ add_pos_of_pos_of_nonneg one_pos
    (inner_ring_inverse_apply_self_nonneg (isPositive_designOp hlam.le x s) _))

end LMLExplore
