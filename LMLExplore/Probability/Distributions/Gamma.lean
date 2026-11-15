/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The density of the gamma law of shape two

The density of Mathlib's gamma law `gammaMeasure 2 r` at `x ≥ 0` is `r ^ 2 * x * exp (- r x)`.

## Main statements

* `ProbabilityTheory.gammaPDF_two`: the density of `Gamma(2, r)` on `[0, ∞)`.
-/

public section

open Real

namespace ProbabilityTheory

/-- The density of `Gamma(2, r)` on `[0, ∞)` is `r ^ 2 * x * exp (- r x)`. -/
theorem gammaPDF_two {r x : ℝ} (hx : 0 ≤ x) :
    gammaPDF 2 r x = ENNReal.ofReal (r ^ 2 * x * exp (-(r * x))) := by
  rw [gammaPDF_of_nonneg hx, Real.Gamma_two, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, div_one]

end ProbabilityTheory
