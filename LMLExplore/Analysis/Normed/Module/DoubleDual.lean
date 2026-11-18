/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The evaluation map into the bidual

For a normed space `E` over `𝕜 = ℝ` or `ℂ`, the evaluation map
`ContinuousLinearMap.apply 𝕜 𝕜 : E →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜`, `x ↦ (u ↦ u x)`, is by
definition the inclusion `NormedSpace.inclusionInDoubleDual 𝕜 E` of `E` into its bidual. This file
states, in terms of `ContinuousLinearMap.apply`, that it is an isometry, so injective. These are
the forms used by statements that identify a point `x` with the evaluation at `x`, such as the
derivative of a Fenchel conjugate.

In finite dimension the inclusion is also surjective: every continuous linear functional on the
dual is the evaluation at a point. This is the hypothesis under which the Fenchel–Moreau theorem
applies to functions on the dual, paired with `E` by evaluation.

## Main statements

* `ContinuousLinearMap.norm_apply_apply`: `‖ContinuousLinearMap.apply 𝕜 𝕜 x‖ = ‖x‖`.
* `ContinuousLinearMap.apply_injective`: `ContinuousLinearMap.apply 𝕜 𝕜` is injective on `E`.
* `NormedSpace.surjective_inclusionInDoubleDual`: a finite-dimensional normed space is reflexive.
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

namespace NormedSpace

/-- **A finite-dimensional normed space is reflexive**: every continuous linear functional on its
dual is the evaluation at a point. In finite dimension, linear functionals are continuous
(`LinearMap.toContinuousLinearMap`), so this is the algebraic reflexivity `Module.evalEquiv`. -/
theorem surjective_inclusionInDoubleDual {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    Function.Surjective (inclusionInDoubleDual 𝕜 E) := fun φ ↦ by
  -- `φ`, read on the algebraic dual through the continuity of linear functionals.
  let ψ : Module.Dual 𝕜 (Module.Dual 𝕜 E) :=
    φ.toLinearMap ∘ₗ LinearMap.toContinuousLinearMap.toLinearMap
  refine ⟨(Module.evalEquiv 𝕜 E).symm ψ, ContinuousLinearMap.ext fun θ ↦ ?_⟩
  have h := LinearMap.congr_fun ((Module.evalEquiv 𝕜 E).apply_symm_apply ψ) θ.toLinearMap
  rw [Module.evalEquiv_apply, Module.Dual.eval_apply] at h
  rw [dual_def, ← ContinuousLinearMap.coe_coe, h]
  simp only [ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    ContinuousLinearMap.coe_coe]
  rw [show LinearMap.toContinuousLinearMap (θ : E →ₗ[𝕜] 𝕜) = θ from
    ContinuousLinearMap.coe_injective (LinearMap.coe_toContinuousLinearMap _)]

end NormedSpace
