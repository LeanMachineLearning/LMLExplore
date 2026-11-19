/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The product rule with a merely continuous factor

The product rule `(c • f)' = c' • f + c • f'` needs both factors to be differentiable. When `f`
vanishes at the point `x`, the term `c' • f x` disappears, and differentiability of `c` is no
longer needed: if `c` is only continuous at `x` and `f x = 0`, then `c • f` has derivative
`c x • f'` at `x`. Indeed `c y • f y - c x • f' (y - x)` is
`c x • (f y - f' (y - x)) + (c y - c x) • f y`, where `f y = O(y - x)` and `c y - c x = o(1)`.
As in Mathlib's product rule `HasFDerivWithinAt.smul`, the factor `c` may take values in the base
field `𝕜` or in a normed algebra `𝕜'` over it acting on `F`.

This is how a derivative is read off an identity `g y - g x = ∑ i, c i y • f i y` in which the
weights `c i` are only known to be continuous and the factors `f i` vanish at `x`. In the policy
gradient theorem the weights are the state occupancies of the current policy, which are
continuous in the policy, and the factors are the changes of the action probabilities.

## Main statements

* `HasFDerivWithinAt.smul_of_eq_zero`, `HasFDerivAt.smul_of_eq_zero`: if `f` has derivative `f'`
  at `x` and `f x = 0`, and `c` is continuous at `x`, then `fun y ↦ c y • f y` has derivative
  `c x • f'` at `x`.
-/

public section

open Asymptotics Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {𝕜' : Type*} [NormedRing 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {c : E → 𝕜'}
  {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {x : E}

/-- **Product rule with a continuous factor**: if `f` has derivative `f'` at `x` within `s` and
vanishes at `x`, and `c` is continuous at `x` within `s`, then `fun y ↦ c y • f y` has derivative
`c x • f'` at `x` within `s`. -/
theorem HasFDerivWithinAt.smul_of_eq_zero (hf : HasFDerivWithinAt f f' s x) (hfx : f x = 0)
    (hc : ContinuousWithinAt c s x) :
    HasFDerivWithinAt (fun y ↦ c y • f y) (c x • f') s x := by
  have h₁ := hf.isLittleO.const_smul_left (c x)
  -- `c y - c x = o(1)` and `f y = O(y - x)`, so their product is `o(y - x)`
  have h₂ : (fun y ↦ (c y - c x) • f y) =o[𝓝[s] x] fun y ↦ y - x := by
    have hc' : (fun y ↦ c y - c x) =o[𝓝[s] x] fun _ ↦ (1 : 𝕜) :=
      (isLittleO_one_iff 𝕜).2 (tendsto_sub_nhds_zero_iff.2 hc)
    have hfO : f =O[𝓝[s] x] fun y ↦ y - x := by simpa [hfx] using hf.isBigO_sub
    simpa using hc'.smul_isBigO hfO
  refine HasFDerivWithinAt.of_isLittleO ((h₁.add h₂).congr_left fun y ↦ ?_)
  simp only [Pi.smul_apply, hfx, sub_zero, smul_zero, FunLike.coe_smul, smul_sub,
    sub_smul]
  abel

/-- **Product rule with a continuous factor**: if `f` has derivative `f'` at `x` and vanishes at
`x`, and `c` is continuous at `x`, then `fun y ↦ c y • f y` has derivative `c x • f'` at `x`. -/
theorem HasFDerivAt.smul_of_eq_zero {f' : E →L[𝕜] F} (hf : HasFDerivAt f f' x) (hfx : f x = 0)
    (hc : ContinuousAt c x) :
    HasFDerivAt (fun y ↦ c y • f y) (c x • f') x := by
  simpa only [hasFDerivWithinAt_univ] using
    hf.hasFDerivWithinAt.smul_of_eq_zero (s := Set.univ) hfx hc.continuousWithinAt
