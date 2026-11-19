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

A square matrix over a complete nontrivially normed field `𝕜`, indexed by a finite type `S`,
acts on functions `S → 𝕜` by `mulVec`. In finite dimension every linear map is continuous, so
this action is an algebra equivalence `Matrix.toContinuousLinAlgEquiv'` between matrices and
continuous linear operators on `S → 𝕜`, which is also a homeomorphism. It transfers results about
operators on Banach spaces, such as the mean ergodic theorem, to matrices. With the sup norm on
`S → ℝ`, a real row-stochastic matrix acts as an operator of norm at most `1`, hence as a
power-bounded operator.

## Main definitions

* `Matrix.toContinuousLinAlgEquiv'`: square matrices as continuous linear operators on `S → 𝕜`.

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

section Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable (𝕜) in
/-- Square matrices over a complete nontrivially normed field `𝕜` acting on `S → 𝕜` by `mulVec`,
as continuous linear operators. This is the algebra equivalence `Matrix.toLinAlgEquiv'` followed
by the automatic continuity of linear maps in finite dimension. The field `𝕜` is explicit, since
Lean cannot infer it when elaborating the coercion of `toContinuousLinAlgEquiv' 𝕜` to a
function. -/
noncomputable def toContinuousLinAlgEquiv' : Matrix S S 𝕜 ≃ₐ[𝕜] ((S → 𝕜) →L[𝕜] (S → 𝕜)) :=
  toLinAlgEquiv'.trans (Module.End.toContinuousLinearMap (S → 𝕜))

@[simp]
theorem toContinuousLinAlgEquiv'_apply (M : Matrix S S 𝕜) (v : S → 𝕜) :
    toContinuousLinAlgEquiv' 𝕜 M v = M *ᵥ v :=
  (rfl)

/-- The matrix of a continuous linear operator on `S → 𝕜` is the matrix of the underlying linear
map. -/
@[simp]
theorem toContinuousLinAlgEquiv'_symm_apply (f : (S → 𝕜) →L[𝕜] (S → 𝕜)) :
    (toContinuousLinAlgEquiv' 𝕜).symm f = LinearMap.toMatrix' (f : (S → 𝕜) →ₗ[𝕜] (S → 𝕜)) :=
  (rfl)

/-- The action of the inverse of a matrix is the inverse of its action (both are `0` for a
singular matrix). -/
@[simp]
theorem toContinuousLinAlgEquiv'_inv (M : Matrix S S 𝕜) :
    toContinuousLinAlgEquiv' 𝕜 M⁻¹ = (toContinuousLinAlgEquiv' 𝕜 M)⁻¹ʳ := by
  rw [nonsing_inv_eq_ringInverse, map_ringInverse]

/-- Convergence of matrices is convergence of their actions in operator norm. -/
theorem tendsto_toContinuousLinAlgEquiv'_iff {α : Type*} {l : Filter α} {f : α → Matrix S S 𝕜}
    {M : Matrix S S 𝕜} :
    Tendsto (fun x ↦ toContinuousLinAlgEquiv' 𝕜 (f x)) l (𝓝 (toContinuousLinAlgEquiv' 𝕜 M)) ↔
      Tendsto f l (𝓝 M) :=
  ((toContinuousLinAlgEquiv' 𝕜).toLinearEquiv.toContinuousLinearEquiv
    |>.toHomeomorph.isInducing.tendsto_nhds_iff).symm

/-- A sequence of matrices is summable exactly when their actions are. -/
theorem summable_toContinuousLinAlgEquiv'_iff {ι : Type*} {f : ι → Matrix S S 𝕜} :
    Summable (fun i ↦ toContinuousLinAlgEquiv' 𝕜 (f i)) ↔ Summable f :=
  ((toContinuousLinAlgEquiv' 𝕜).toLinearEquiv.toContinuousLinearEquiv
    |>.summable)

end Field

variable {P : Matrix S S ℝ}

/-- A row-stochastic matrix acts on `S → ℝ` with operator norm at most `1` for the sup norm. -/
theorem norm_toContinuousLinAlgEquiv'_le_one (hP : P ∈ rowStochastic ℝ S) :
    ‖toContinuousLinAlgEquiv' ℝ P‖ ≤ 1 := by
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
    IsPowerBounded (toContinuousLinAlgEquiv' ℝ P) :=
  .of_norm_le_one (norm_toContinuousLinAlgEquiv'_le_one hP)

end Matrix
