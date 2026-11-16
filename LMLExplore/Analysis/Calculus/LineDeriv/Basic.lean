/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Line derivatives as derivatives along the line

Mathlib defines the line derivative of `f` at `x` in the direction `v` within a set `s` as the
derivative at `0` of `t ↦ f (x + t • v)` within the parameters `t` of the points of `s`. This file
states this as a lemma, and computes `lineDerivWithin` from `HasLineDerivWithinAt` when these
parameters have unique derivatives at `0`, as for `t ∈ [0, 1]` along a segment.

## Main statements

* `LMLExplore.hasLineDerivWithinAt_iff_hasDerivWithinAt`: `HasLineDerivWithinAt` is the
  derivative at `0` of `t ↦ f (x + t • v)` within the preimage of `s`.
* `HasLineDerivWithinAt.lineDerivWithin`: if `f` has the line derivative `f'` within `s`, and the
  preimage of `s` has unique derivatives at `0`, then `lineDerivWithin 𝕜 f s x v = f'`.
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E → F} {f' : F} {s : Set E}
  {x v : E}

namespace LMLExplore

/-- `f` has the line derivative `f'` at `x` in the direction `v` within `s` if and only if
`t ↦ f (x + t • v)` has the derivative `f'` at `0` within the parameters `t` with
`x + t • v ∈ s`. -/
theorem hasLineDerivWithinAt_iff_hasDerivWithinAt :
    HasLineDerivWithinAt 𝕜 f f' s x v ↔
      HasDerivWithinAt (fun t : 𝕜 ↦ f (x + t • v)) f' ((fun t : 𝕜 ↦ x + t • v) ⁻¹' s) 0 :=
  Iff.rfl

end LMLExplore

/-- If `f` has the line derivative `f'` at `x` in the direction `v` within `s`, and the parameters
`t` with `x + t • v ∈ s` have unique derivatives at `0`, then `f'` is the line derivative
`lineDerivWithin 𝕜 f s x v`. -/
protected theorem HasLineDerivWithinAt.lineDerivWithin (h : HasLineDerivWithinAt 𝕜 f f' s x v)
    (hs : UniqueDiffWithinAt 𝕜 ((fun t : 𝕜 ↦ x + t • v) ⁻¹' s) 0) :
    lineDerivWithin 𝕜 f s x v = f' :=
  (LMLExplore.hasLineDerivWithinAt_iff_hasDerivWithinAt.1 h).derivWithin hs
