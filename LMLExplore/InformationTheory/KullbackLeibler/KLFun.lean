/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Monotonicity of `klFun`

The function `klFun x = x log x + 1 - x`, whose integral against a measure `ν` of the density
`dμ/dν` is the relative entropy `KL(μ ‖ ν)`, has derivative `log x` at every `x ≠ 0`. It is hence
strictly decreasing on `[0, 1]`, from `klFun 0 = 1` to its minimum `klFun 1 = 0`. An upper bound
`c < 1` on a ratio in `[0, 1]` thus gives the positive lower bound `klFun c` on `klFun` of that
ratio, as in the lower bound `q klFun (p / q) ≤ d(p, q)` on the binary relative entropy
(`LMLExplore.mul_klFun_div_le_klBerReal`).

## Main statements

* `InformationTheory.strictAntiOn_klFun`: `klFun` is strictly decreasing on `[0, 1]`.
-/

public section

open Real Set

namespace InformationTheory

/-- `klFun x = x log x + 1 - x` is strictly decreasing on `[0, 1]`. -/
lemma strictAntiOn_klFun : StrictAntiOn klFun (Icc 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc 0 1) continuous_klFun.continuousOn fun x hx ↦ ?_
  rw [interior_Icc] at hx
  rw [deriv_klFun]
  exact log_neg hx.1 hx.2

end InformationTheory
