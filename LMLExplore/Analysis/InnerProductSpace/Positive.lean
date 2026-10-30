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

The inverse of a positive operator is positive. The determinant of a positive operator `T` on a
real inner product space of dimension `d` is at most `(trace T / d) ^ d`: both are expressed
through the eigenvalues of `T`, which are nonnegative, and the inequality is the AM-GM
inequality.

## Main statements

* `ContinuousLinearMap.IsPositive.ringInverse`: the inverse `Ring.inverse V` of a positive
  continuous linear operator `V` is positive. In particular `0 ≤ ⟪v, V⁻¹ v⟫` for every `v`, by
  `IsPositive.inner_nonneg_right`.
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

end ContinuousLinearMap

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
