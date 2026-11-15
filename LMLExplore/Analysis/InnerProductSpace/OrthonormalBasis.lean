/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The norm and the coordinates in an orthonormal basis

The norm of a vector of a finite-dimensional inner product space is at most the sum of the
absolute values of its coordinates `⟪b i, y⟫` in an orthonormal basis `b` (the `ℓ²` norm of the
coordinates is at most their `ℓ¹` norm), hence at most the dimension times the largest of them.
These bounds reduce the control of a function of `‖y‖` to finitely many linear functionals, for
example the exponential moments `exp (c ‖T‖)` of a vector statistic `T` to the real exponential
moments of its coordinates.

## Main statements

* `OrthonormalBasis.norm_le_sum_norm_inner`: `‖y‖ ≤ ∑ i, ‖⟪b i, y⟫‖`.
* `OrthonormalBasis.exists_norm_le_card_mul_norm_inner`: for a nonempty index type, there is `i`
  with `‖y‖ ≤ card ι * ‖⟪b i, y⟫‖`.
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The norm of a vector is at most the sum of the norms of its coordinates in an orthonormal
basis. -/
lemma norm_le_sum_norm_inner (b : OrthonormalBasis ι 𝕜 E) (y : E) :
    ‖y‖ ≤ ∑ i, ‖⟪b i, y⟫_𝕜‖ := by
  calc ‖y‖ = ‖∑ i, ⟪b i, y⟫_𝕜 • b i‖ := by rw [b.sum_repr']
  _ ≤ ∑ i, ‖⟪b i, y⟫_𝕜 • b i‖ := norm_sum_le _ _
  _ = ∑ i, ‖⟪b i, y⟫_𝕜‖ := by simp [norm_smul, b.orthonormal.1]

/-- The norm of a vector is at most the dimension times the norm of its largest coordinate in an
orthonormal basis. -/
lemma exists_norm_le_card_mul_norm_inner [Nonempty ι] (b : OrthonormalBasis ι 𝕜 E) (y : E) :
    ∃ i, ‖y‖ ≤ Fintype.card ι * ‖⟪b i, y⟫_𝕜‖ := by
  obtain ⟨i, -, hi⟩ := Finset.univ.exists_max_image (fun i ↦ ‖⟪b i, y⟫_𝕜‖) Finset.univ_nonempty
  refine ⟨i, (b.norm_le_sum_norm_inner y).trans ?_⟩
  simpa using Finset.sum_le_card_nsmul Finset.univ _ _ fun j _ ↦ hi j (Finset.mem_univ j)

end OrthonormalBasis
