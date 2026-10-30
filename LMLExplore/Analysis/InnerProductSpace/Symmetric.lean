/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# The inverse of a symmetric operator

## Main statements

* `LinearMap.IsSymmetric.ringInverse`: the inverse `Ring.inverse V` of a symmetric continuous
  linear operator `V` is symmetric.
-/

public section

open ContinuousLinearMap
open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inverse `Ring.inverse V` of a symmetric continuous linear operator `V` is symmetric.
If `V` is not invertible, then `Ring.inverse V = 0`, which is symmetric. -/
theorem IsSymmetric.ringInverse {V : E →L[𝕜] E} (hV : (V : E →ₗ[𝕜] E).IsSymmetric) :
    ((Ring.inverse V : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric := by
  by_cases hu : IsUnit V
  · intro y z
    rw [ContinuousLinearMap.coe_coe]
    conv_lhs => rw [← V.apply_ringInverse_apply hu z]
    conv_rhs => rw [← V.apply_ringInverse_apply hu y]
    exact (hV _ _).symm
  · rw [Ring.inverse_non_unit V hu]
    exact IsSymmetric.zero

end LinearMap
