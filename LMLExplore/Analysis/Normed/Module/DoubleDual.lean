/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# The evaluation map into the bidual

For a normed space `E` over `𝕜 = ℝ` or `ℂ`, the evaluation map
`ContinuousLinearMap.apply 𝕜 𝕜 : E →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜`, `x ↦ (u ↦ u x)`, is by
definition the inclusion `NormedSpace.inclusionInDoubleDual 𝕜 E` of `E` into its bidual. This file
states, in terms of `ContinuousLinearMap.apply`, that it is an isometry, so injective. These are
the forms used by statements that identify a point `x` with the evaluation at `x`, such as the
derivative of a Fenchel conjugate.

## Main statements

* `ContinuousLinearMap.norm_apply_apply`: `‖ContinuousLinearMap.apply 𝕜 𝕜 x‖ = ‖x‖`.
* `ContinuousLinearMap.apply_injective`: `ContinuousLinearMap.apply 𝕜 𝕜` is injective on `E`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜]

/-- The evaluation `x ↦ (u ↦ u x)` into the bidual preserves the norm: it is
`NormedSpace.inclusionInDoubleDualLi`, by definition of `NormedSpace.inclusionInDoubleDual`. -/
@[simp]
theorem norm_apply_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    ‖ContinuousLinearMap.apply 𝕜 𝕜 x‖ = ‖x‖ :=
  (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map x

/-- The evaluation `x ↦ (u ↦ u x)` into the bidual is injective: it is
`NormedSpace.inclusionInDoubleDualLi`, by definition of `NormedSpace.inclusionInDoubleDual`. -/
theorem apply_injective [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Function.Injective (ContinuousLinearMap.apply 𝕜 𝕜 : E → (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
  (NormedSpace.inclusionInDoubleDualLi 𝕜).injective

end ContinuousLinearMap
