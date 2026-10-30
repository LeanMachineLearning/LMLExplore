/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace
public import LMLExplore.Analysis.MeanInequalities

/-!
# Determinant and trace of positive operators

The determinant of a positive operator `T` on a real inner product space of dimension `d` is at
most `(trace T / d) ^ d`: both are expressed through the eigenvalues of `T`, which are
nonnegative, and the inequality is the AM-GM inequality.

## Main statements

* `LinearMap.IsPositive.det_le_trace_div_finrank_pow`,
  `ContinuousLinearMap.IsPositive.det_le_trace_div_finrank_pow`: for a positive operator `T`,
  `det T ≤ (trace T / d) ^ d`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  proof of Lemma 19.4.
-/

public section

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
