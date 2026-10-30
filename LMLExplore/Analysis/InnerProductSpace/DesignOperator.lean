/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Positive
public import LMLExplore.Analysis.InnerProductSpace.RankOne
public import TauCeti.Analysis.InnerProductSpace.Frame

/-!
# Design operators of regularized least squares

For `λ : ℝ` and a sequence `x : ℕ → E` in a real inner product space, the *design operator*
`V_t(λ) = λ • 1 + ∑_{s < t} x s ⊗ x s`, where `x ⊗ x = rankOne ℝ x x` is the operator
`v ↦ ⟪x, v⟫ • x`, is the regularized Gram operator of ridge regression and of linear bandit
algorithms. Its unregularized part is Tau Ceti's frame operator of the family `(x s)_{s < t}`.
The weighted norm `‖v‖²_{V⁻¹}` is `⟪v, V⁻¹ v⟫`, with `V⁻¹ = Ring.inverse V`; it is nonnegative
for positive `V` by `ContinuousLinearMap.IsPositive.ringInverse`.

## Main definitions

* `LMLExplore.designOp lam x t`: the design operator `V_t(λ)`.

## Main statements

* `LMLExplore.toLinearMap_designOp`: `V_t(λ) = λ • id + frameOperator ℝ (fun s : Fin t ↦ x s)`.
* `LMLExplore.isPositive_designOp`: `V_t(λ)` is positive for `λ ≥ 0`;
  `LMLExplore.mul_norm_sq_le_inner_designOp_apply`: `λ ‖v‖² ≤ ⟪v, V_t(λ) v⟫`.
* `LMLExplore.isUnit_designOp`: in a complete space (in particular in finite dimension),
  `V_t(λ)` is invertible for `λ > 0`.
* `LMLExplore.ringInverse_designOp_succ`: the rank-one update of the inverse
  (Sherman–Morrison formula).
* `LMLExplore.det_designOp_succ`: `det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})`, and
  `LMLExplore.det_designOp_eq_mul_prod`: `det V_t = λ ^ d * ∏_{s < t} (1 + ‖x s‖²_{V_s⁻¹})`.

The design operator and its determinant recursion `det_designOp_succ` follow the matrix
versions `regGram` and `det_regGram_succ` of the LMLPapers project (Rémy Degenne,
<https://github.com/LeanMachineLearning/LMLPapers>), restated here for operators with new proofs.

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

/-- Evaluation of the design operator: `V_t(λ) v = λ • v + ∑_{s < t} ⟪x s, v⟫ • x s`. -/
@[simp]
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

/-- The quadratic form of the design operator: `⟪v, V_t(λ) v⟫ = λ ‖v‖² + ∑_{s < t} ⟪x s, v⟫²`. -/
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
  simp [TauCeti.frameOperator_apply,
    Fin.sum_univ_eq_sum_range (fun s ↦ ⟪x s, v⟫_ℝ • x s)]

/-- The design operator is positive for `λ ≥ 0`. -/
theorem isPositive_designOp (hlam : 0 ≤ lam) (x : ℕ → E) (t : ℕ) :
    (designOp lam x t).IsPositive :=
  (isPositive_one.smul_of_nonneg hlam).add (isPositive_sum _ fun _ _ ↦ isPositive_rankOne_self _)

/-- The coercivity bound `λ ‖v‖² ≤ ⟪v, V_t(λ) v⟫`, valid for every `λ`. -/
theorem mul_norm_sq_le_inner_designOp_apply (lam : ℝ) (x : ℕ → E) (t : ℕ) (v : E) :
    lam * ‖v‖ ^ 2 ≤ ⟪v, designOp lam x t v⟫_ℝ := by
  rw [inner_designOp_apply_self]
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- In a complete space (in particular in finite dimension), the design operator is invertible
for `λ > 0`. -/
theorem isUnit_designOp [CompleteSpace E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    IsUnit (designOp lam x t) := by
  refine isUnit_of_forall_le_norm_inner_map _ (c := ⟨lam, hlam.le⟩) hlam fun v ↦ ?_
  rw [real_inner_comm, mul_comm]
  exact (mul_norm_sq_le_inner_designOp_apply lam x t v).trans (Real.le_norm_self _)

/-- **Sherman–Morrison formula** for the design operator: for `λ > 0`,
`V_{t+1}⁻¹ = V_t⁻¹ - (1 + ‖x t‖²_{V_t⁻¹})⁻¹ • (V_t⁻¹ x t) ⊗ (V_t⁻¹ x t)`. -/
theorem ringInverse_designOp_succ [CompleteSpace E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    Ring.inverse (designOp lam x (t + 1)) = Ring.inverse (designOp lam x t) -
      (1 + ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ)⁻¹ •
        rankOne ℝ (Ring.inverse (designOp lam x t) (x t))
          (Ring.inverse (designOp lam x t) (x t)) := by
  rw [designOp_succ]
  exact ringInverse_add_rankOne_of_isSymmetric (isUnit_designOp hlam x t)
    (isPositive_designOp hlam.le x t).isSymmetric (x t) (x t) (add_pos_of_pos_of_nonneg one_pos
      ((isPositive_designOp hlam.le x t).ringInverse.inner_nonneg_right _)).ne'

/-- The determinant of the initial design operator: `det V_0(λ) = λ ^ d`. -/
theorem det_designOp_zero (lam : ℝ) (x : ℕ → E) :
    LinearMap.det (designOp lam x 0 : E →ₗ[ℝ] E) = lam ^ finrank ℝ E := by
  simp [LinearMap.det_smul]

/-- The determinant of the design operator after a rank-one update [LS, (19.9)]: for `λ > 0`,
`det V_{t+1} = det V_t * (1 + ‖x t‖²_{V_t⁻¹})`. -/
theorem det_designOp_succ [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    LinearMap.det (designOp lam x (t + 1) : E →ₗ[ℝ] E) =
      LinearMap.det (designOp lam x t : E →ₗ[ℝ] E) *
        (1 + ⟪x t, Ring.inverse (designOp lam x t) (x t)⟫_ℝ) := by
  have := FiniteDimensional.complete ℝ E
  rw [designOp_succ, det_add_rankOne (isUnit_designOp hlam x t)]

/-- For `λ > 0`, `det V_t = λ ^ d * ∏_{s < t} (1 + ‖x s‖²_{V_s⁻¹})`. -/
theorem det_designOp_eq_mul_prod [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    LinearMap.det (designOp lam x t : E →ₗ[ℝ] E) =
      lam ^ finrank ℝ E * ∏ s ∈ range t, (1 + ⟪x s, Ring.inverse (designOp lam x s) (x s)⟫_ℝ) := by
  induction t with
  | zero => simp
  | succ t ih => rw [det_designOp_succ hlam, ih, prod_range_succ, mul_assoc]

/-- The determinant of the design operator is positive for `λ > 0`. -/
theorem det_designOp_pos [FiniteDimensional ℝ E] (hlam : 0 < lam) (x : ℕ → E) (t : ℕ) :
    0 < LinearMap.det (designOp lam x t : E →ₗ[ℝ] E) := by
  rw [det_designOp_eq_mul_prod hlam]
  exact mul_pos (pow_pos hlam _) (prod_pos fun s _ ↦ add_pos_of_pos_of_nonneg one_pos
    ((isPositive_designOp hlam.le x s).ringInverse.inner_nonneg_right _))

end LMLExplore
