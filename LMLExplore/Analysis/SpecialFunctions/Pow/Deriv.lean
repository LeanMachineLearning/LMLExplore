/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of exponentials in the exponent

A complement to `Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean`.

## Main statements

* `Real.hasDerivAt_const_rpow_sub_one_mul_div`: for `x > 0` with `log x ≠ 0`, the function
  `κ ↦ x ^ (κ - 1) (κ log x - 1) / (log x) ^ 2` is an antiderivative of `κ ↦ κ x ^ (κ - 1)`.
-/

public section

namespace Real

/-- An antiderivative of `κ ↦ κ x ^ (κ - 1)`, for `x > 0` with `log x ≠ 0`. -/
theorem hasDerivAt_const_rpow_sub_one_mul_div {x : ℝ} (hx : 0 < x) (hlog : log x ≠ 0) (κ : ℝ) :
    HasDerivAt (fun κ ↦ x ^ (κ - 1) * (κ * log x - 1) / log x ^ 2) (κ * x ^ (κ - 1)) κ := by
  have h_pow : HasDerivAt (fun κ ↦ x ^ (κ - 1)) (x ^ (κ - 1) * log x) κ :=
    HasDerivAt.comp_sub_const κ 1 (hasStrictDerivAt_const_rpow hx (κ - 1)).hasDerivAt
  refine ((h_pow.mul (((hasDerivAt_id κ).mul_const (log x)).sub_const 1)).div_const
    (log x ^ 2)).congr_deriv ?_
  simp only [id]
  field_simp
  ring

end Real
