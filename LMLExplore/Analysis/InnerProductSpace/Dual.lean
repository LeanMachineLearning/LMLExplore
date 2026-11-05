/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Continuous linear functionals in an orthonormal basis

A continuous linear functional `y` on a finite-dimensional inner product space is determined by
its values on an orthonormal basis `b`: `y = ∑ i, y (b i) • ⟪b i, ·⟫`. This is the continuous
version of `Basis.sum_dual_apply_smul_coord`, whose coordinate functionals are, for an orthonormal
basis, the inner products `⟪b i, ·⟫`. It is the identity behind unbiased estimates of a loss
functional from its values in the directions of a basis.

## Main statements

* `OrthonormalBasis.sum_apply_smul_innerSL`: `∑ i, y (b i) • innerSL 𝕜 (b i) = y`.
-/

public section

namespace OrthonormalBasis

variable {ι 𝕜 E : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A continuous linear functional is the sum of its values on an orthonormal basis times the
corresponding coordinate functionals: `y = ∑ i, y (b i) • ⟪b i, ·⟫`. -/
lemma sum_apply_smul_innerSL (b : OrthonormalBasis ι 𝕜 E) (y : E →L[𝕜] 𝕜) :
    ∑ i, y (b i) • innerSL 𝕜 (b i) = y := by
  ext v
  have h := congr($(b.toBasis.sum_dual_apply_smul_coord (y : E →ₗ[𝕜] 𝕜)) v)
  simpa [OrthonormalBasis.repr_apply_apply] using h

end OrthonormalBasis
