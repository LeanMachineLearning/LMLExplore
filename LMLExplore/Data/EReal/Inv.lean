/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.EReal.Inv

/-!
# Multiplying an extended real by the inverse of a nonnegative real

## Main statements

* `EReal.coe_nnreal_inv_mul`: multiplying an extended real `a` by the inverse `r⁻¹` of a
  nonnegative real, taken in `ℝ≥0` and cast to `EReal`, is dividing `a` by `r`. This holds also for
  `r = 0`, where both sides vanish. It converts between the forms `ε * log μ` and `log μ / r` of
  the bounds of a large deviation principle with speed `ε = r⁻¹`.
-/

public section

open scoped NNReal

namespace EReal

/-- Multiplying an extended real `a` by `r⁻¹`, for `r : ℝ≥0`, is dividing `a` by `r`, also for
`r = 0`, where both sides vanish. -/
lemma coe_nnreal_inv_mul (r : ℝ≥0) (a : EReal) :
    (((r⁻¹ : ℝ≥0) : ℝ) : EReal) * a = a / ((r : ℝ) : EReal) := by
  rw [NNReal.coe_inv, EReal.coe_inv, EReal.div_eq_inv_mul]

end EReal
