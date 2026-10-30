/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Symmetric
public import LMLExplore.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Positive operators: inverse, determinant and trace

The inverse of a positive operator is positive, and the eigenvalues of a positive invertible
operator are positive. The determinant of a positive operator `T` on a
real inner product space of dimension `d` is at most `(trace T / d) ^ d`: both are expressed
through the eigenvalues of `T`, which are nonnegative, and the inequality is the AM-GM
inequality.

## Main statements

* `ContinuousLinearMap.IsPositive.ringInverse`: the inverse `Ring.inverse V` of a positive
  continuous linear operator `V` is positive. In particular `0 ≤ ⟪v, V⁻¹ v⟫` for every `v`, by
  `IsPositive.inner_nonneg_right`.
* `ContinuousLinearMap.IsPositive.one_add_inner_ringInverse_pos`: for a positive operator `V` on
  a real inner product space, `0 < 1 + ⟪x, V⁻¹ x⟫`.
* `LinearMap.IsPositive.eigenvalues_pos`: the eigenvalues of a positive invertible operator on a
  finite-dimensional inner product space are positive.
* `LinearMap.IsPositive.det_le_trace_div_finrank_pow`,
  `ContinuousLinearMap.IsPositive.det_le_trace_div_finrank_pow`: for a positive operator `T`,
  `det T ≤ (trace T / d) ^ d`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  proof of Lemma 19.4.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inverse `Ring.inverse V` of a positive continuous linear operator `V` is positive.
If `V` is not invertible, then `Ring.inverse V = 0`, which is positive. -/
theorem IsPositive.ringInverse {V : E →L[𝕜] E} (hV : V.IsPositive) :
    (Ring.inverse V).IsPositive := by
  by_cases hu : IsUnit V
  · refine ⟨hV.isSymmetric.ringInverse, fun y ↦ ?_⟩
    have := hV.re_inner_nonneg_right (Ring.inverse V y)
    rwa [V.apply_ringInverse_apply hu] at this
  · rw [Ring.inverse_non_unit V hu]
    exact isPositive_zero

/-- For a positive operator `V` on a real inner product space, `0 < 1 + ⟪x, V⁻¹ x⟫`. -/
theorem IsPositive.one_add_inner_ringInverse_pos {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {V : F →L[ℝ] F} (hV : V.IsPositive) (x : F) :
    0 < 1 + ⟪x, Ring.inverse V x⟫_ℝ :=
  add_pos_of_pos_of_nonneg one_pos (hV.ringInverse.inner_nonneg_right x)

end ContinuousLinearMap

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The eigenvalues of a positive invertible operator on a finite-dimensional inner product space
are positive: an eigenvalue `0` would have an eigenvector in the kernel. -/
theorem IsPositive.eigenvalues_pos {T : E →ₗ[𝕜] E} {n : ℕ} (hT : T.IsPositive) (hTu : IsUnit T)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 0 < hT.isSymmetric.eigenvalues hn i := by
  refine (hT.nonneg_eigenvalues hn i).lt_of_ne fun h0 ↦ ?_
  have h := hT.isSymmetric.apply_eigenvectorBasis hn i
  rw [← h0, RCLike.ofReal_zero, zero_smul] at h
  have hb : hT.isSymmetric.eigenvectorBasis hn i = 0 := by
    simpa [(LinearMap.isUnit_iff_ker_eq_bot T).1 hTu] using LinearMap.mem_ker.2 h
  simpa [hb] using (hT.isSymmetric.eigenvectorBasis hn).orthonormal.1 i

end LinearMap

section DetTrace

open Finset Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For a positive operator `T` on a real inner product space of dimension `d`,
`det T ≤ (trace T / d) ^ d`. -/
theorem LinearMap.IsPositive.det_le_trace_div_finrank_pow {T : E →ₗ[ℝ] E} (hT : T.IsPositive) :
    LinearMap.det T ≤ (LinearMap.trace ℝ E T / finrank ℝ E) ^ finrank ℝ E := by
  rw [hT.isSymmetric.det_eq_prod_eigenvalues rfl, hT.isSymmetric.trace_eq_sum_eigenvalues rfl]
  simpa using Real.prod_le_sum_div_card_pow univ fun i _ ↦ hT.nonneg_eigenvalues rfl i

/-- For a positive continuous linear operator `T` on a real inner product space of dimension
`d`, `det T ≤ (trace T / d) ^ d`. -/
theorem ContinuousLinearMap.IsPositive.det_le_trace_div_finrank_pow {T : E →L[ℝ] E}
    (hT : T.IsPositive) :
    LinearMap.det (T : E →ₗ[ℝ] E) ≤
      (LinearMap.trace ℝ E (T : E →ₗ[ℝ] E) / finrank ℝ E) ^ finrank ℝ E :=
  hT.toLinearMap.det_le_trace_div_finrank_pow

end DetTrace
