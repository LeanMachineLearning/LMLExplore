/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Instances.Matrix
public import LMLExplore.Analysis.Normed.Ring.PowerBounded

/-!
# Square matrices as continuous linear operators

A real square matrix indexed by a finite type `S` acts on functions `S → ℝ` by `mulVec`. In finite
dimension every linear map is continuous, so this action is an algebra equivalence
`Matrix.toContinuousLinAlgEquiv'` between matrices and continuous linear operators on `S → ℝ`,
which is also a homeomorphism. It transfers results about operators on Banach spaces, such as the
mean ergodic theorem, to matrices. With the sup norm on `S → ℝ`, a row-stochastic matrix acts as
an operator of norm at most `1`, hence as a power-bounded operator.

## Main definitions

* `Matrix.toContinuousLinAlgEquiv'`: real square matrices as continuous linear operators on
  `S → ℝ`.

## Main statements

* `Matrix.toContinuousLinAlgEquiv'_inv`: the action of `M⁻¹` is the inverse of the action of `M`.
* `Matrix.tendsto_toContinuousLinAlgEquiv'_iff`, `Matrix.summable_toContinuousLinAlgEquiv'_iff`:
  limits and sums of matrices are those of their actions.
* `Matrix.norm_toContinuousLinAlgEquiv'_le_one`,
  `Matrix.isPowerBounded_toContinuousLinAlgEquiv'`: a row-stochastic matrix acts as a power-bounded
  operator of norm at most `1`.
-/

public section

open Filter Finset LMLExplore Topology
open scoped Ring

namespace Matrix

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Real square matrices acting on `S → ℝ` by `mulVec`, as continuous linear operators. This is
the algebra equivalence `Matrix.toLinAlgEquiv'` followed by the automatic continuity of linear
maps in finite dimension. -/
noncomputable def toContinuousLinAlgEquiv' : Matrix S S ℝ ≃ₐ[ℝ] ((S → ℝ) →L[ℝ] (S → ℝ)) :=
  toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap (S → ℝ))

@[simp]
theorem toContinuousLinAlgEquiv'_apply (M : Matrix S S ℝ) (v : S → ℝ) :
    toContinuousLinAlgEquiv' M v = M *ᵥ v :=
  (rfl)

/-- The action of the inverse of a matrix is the inverse of its action (both are `0` for a
singular matrix). -/
@[simp]
theorem toContinuousLinAlgEquiv'_inv (M : Matrix S S ℝ) :
    toContinuousLinAlgEquiv' M⁻¹ = (toContinuousLinAlgEquiv' M)⁻¹ʳ := by
  rw [nonsing_inv_eq_ringInverse, map_ringInverse]

/-- Convergence of matrices is convergence of their actions in operator norm. -/
theorem tendsto_toContinuousLinAlgEquiv'_iff {α : Type*} {l : Filter α} {f : α → Matrix S S ℝ}
    {M : Matrix S S ℝ} :
    Tendsto (fun x ↦ toContinuousLinAlgEquiv' (f x)) l (𝓝 (toContinuousLinAlgEquiv' M)) ↔
      Tendsto f l (𝓝 M) :=
  ((toContinuousLinAlgEquiv' : Matrix S S ℝ ≃ₐ[ℝ] _).toLinearEquiv.toContinuousLinearEquiv
    |>.toHomeomorph.isInducing.tendsto_nhds_iff).symm

/-- A sequence of matrices is summable exactly when their actions are. -/
theorem summable_toContinuousLinAlgEquiv'_iff {ι : Type*} {f : ι → Matrix S S ℝ} :
    Summable (fun i ↦ toContinuousLinAlgEquiv' (f i)) ↔ Summable f :=
  ((toContinuousLinAlgEquiv' : Matrix S S ℝ ≃ₐ[ℝ] _).toLinearEquiv.toContinuousLinearEquiv
    |>.summable)

variable {P : Matrix S S ℝ}

/-- A row-stochastic matrix acts on `S → ℝ` with operator norm at most `1` for the sup norm. -/
theorem norm_toContinuousLinAlgEquiv'_le_one (hP : P ∈ rowStochastic ℝ S) :
    ‖toContinuousLinAlgEquiv' P‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  rw [one_mul, pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  rw [toContinuousLinAlgEquiv'_apply, mulVec, dotProduct, Real.norm_eq_abs]
  calc |∑ j, P i j * v j| ≤ ∑ j, P i j * ‖v‖ := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg (hP.1 i j), ← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (hP.1 i j)
    _ = ‖v‖ := by rw [← sum_mul, sum_row_of_mem_rowStochastic hP i, one_mul]

/-- A row-stochastic matrix acts on `S → ℝ` as a power-bounded operator. -/
theorem isPowerBounded_toContinuousLinAlgEquiv' (hP : P ∈ rowStochastic ℝ S) :
    IsPowerBounded (toContinuousLinAlgEquiv' P) :=
  .of_norm_le_one (norm_toContinuousLinAlgEquiv'_le_one hP)

end Matrix
