/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Positive

/-!
# Determinant and trace of positive semidefinite matrices

The determinant of a real positive semidefinite `d × d` matrix `A` is at most
`(trace A / d) ^ d`. This is the matrix counterpart of
`LinearMap.IsPositive.det_le_trace_div_finrank_pow`, from which it is derived by applying it to
the positive operator `A.toEuclideanLin` on `EuclideanSpace ℝ n`.

## Main statements

* `Matrix.PosSemidef.det_le_trace_div_card_pow`: for a real positive semidefinite matrix `A`
  indexed by `n`, `A.det ≤ (A.trace / Fintype.card n) ^ Fintype.card n`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  proof of Lemma 19.4.
-/

public section

namespace Matrix.PosSemidef

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a real positive semidefinite matrix `A` indexed by `n`, of size `d = Fintype.card n`,
`A.det ≤ (A.trace / d) ^ d`. -/
theorem det_le_trace_div_card_pow {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    A.det ≤ (A.trace / Fintype.card n) ^ Fintype.card n := by
  simpa [toEuclideanLin_eq_toLin_orthonormal] using
    (isPositive_toEuclideanLin_iff.mpr hA).det_le_trace_div_finrank_pow

end Matrix.PosSemidef
