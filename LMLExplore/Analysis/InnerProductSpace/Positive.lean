/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The inverse of a positive operator

## Main statements

* `ContinuousLinearMap.IsPositive.ringInverse`: the inverse `Ring.inverse V` of a positive
  continuous linear operator `V` is positive. In particular `0 ≤ ⟪v, V⁻¹ v⟫` for every `v`, by
  `IsPositive.inner_nonneg_right`.
* `LinearMap.IsPositive.eigenvalues_pos`: the eigenvalues of a positive invertible operator on a
  finite-dimensional inner product space are positive.
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
