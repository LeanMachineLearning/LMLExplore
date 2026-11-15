/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Pointwise and operator-norm convergence in finite dimension

On a finite-dimensional normed space over a complete field, a family of continuous linear maps
converges in operator norm exactly when it converges at every point. This is the `Tendsto` form of
Mathlib's `continuousAt_clm_apply`, and its proof is that of `continuousWithinAt_clm_apply`. It
upgrades pointwise limit theorems for operators, such as the mean ergodic theorem, to limits in
operator norm.

## Main statements

* `LMLExplore.tendsto_clm_apply`: a family of continuous linear maps on a finite-dimensional
  space tends to `g` iff its applications to every vector `y` tend to `g y`.
-/

public section

open Filter Module Topology

namespace LMLExplore

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional 𝕜 E]

/-- On a finite-dimensional space, a family of continuous linear maps converges in operator norm
iff it converges pointwise. -/
theorem tendsto_clm_apply {l : Filter ι} {f : ι → E →L[𝕜] F} {g : E →L[𝕜] F} :
    Tendsto f l (𝓝 g) ↔ ∀ y, Tendsto (f · y) l (𝓝 (g y)) := by
  refine ⟨fun h y ↦ ((ContinuousLinearMap.apply 𝕜 F y).continuous.tendsto g).comp h, fun h ↦ ?_⟩
  let e : (E →L[𝕜] F) ≃L[𝕜] Fin (finrank 𝕜 E) → F :=
    ((ContinuousLinearEquiv.ofFinrankEq (finrank_fin_fun 𝕜).symm).arrowCongr
      (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing _)
  rw [e.toHomeomorph.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  exact fun i ↦ h _

end LMLExplore
