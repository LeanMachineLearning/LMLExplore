/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import TauCeti.Analysis.Convex.Strong

/-!
# Bregman divergences of strongly convex functions

The Bregman divergence `D_f(x, a) = f x - f a - f' (x - a)` of a function `f` that is `m`-strongly
convex on a set `s`, for a derivative `f'` of `f` within `s` at `a`, is at least
`m / 2 * ‖x - a‖ ^ 2` on `s`. This is the lower bound that controls the stability terms in the
regret bounds of follow the regularized leader and mirror descent with a strongly convex potential.

## Main statements

* `StrongConvexOn.mul_norm_sub_sq_le_bregDiv`: for `f` `m`-strongly convex on `s` and `a, x ∈ s`,
  `m / 2 * ‖x - a‖ ^ 2 ≤ D_f(x, a)`.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℝ} {f : E → ℝ}
  {f' : E →L[ℝ] ℝ} {a x : E}

/-- **Bregman divergence of a strongly convex function.** If `f` is `m`-strongly convex on `s`
and has derivative `f'` within `s` at `a ∈ s`, then for every `x ∈ s`, the Bregman divergence
`D_f(x, a)` is at least `m / 2 * ‖x - a‖ ^ 2`. -/
theorem StrongConvexOn.mul_norm_sub_sq_le_bregDiv (hf : StrongConvexOn s m f) (ha : a ∈ s)
    (hx : x ∈ s) (hf' : HasFDerivWithinAt f f' s a) :
    m / 2 * ‖x - a‖ ^ 2 ≤ bregDiv f x a f' := by
  have := hf.add_add_le_of_hasFDerivWithinAt ha hx hf'
  simp only [bregDiv]
  linarith
