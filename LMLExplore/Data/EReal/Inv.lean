/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.EReal.Inv

/-!
# Multiplying an extended real by the inverse of a real

## Main statements

* `EReal.coe_inv_mul`: multiplying an extended real `a` by the inverse `x⁻¹` of a real, taken in
  `ℝ` and cast to `EReal`, is dividing `a` by `x`. This holds also for `x = 0`, where both sides
  vanish. It converts between the forms `ε * log μ` and `log μ / r` of the bounds of a large
  deviation principle with speed `ε = r⁻¹`.
-/

public section

namespace EReal

/-- Multiplying an extended real `a` by `x⁻¹`, for `x : ℝ`, is dividing `a` by `x`, also for
`x = 0`, where both sides vanish. -/
lemma coe_inv_mul (x : ℝ) (a : EReal) : ((x⁻¹ : ℝ) : EReal) * a = a / (x : EReal) := by
  rw [EReal.coe_inv, EReal.div_eq_inv_mul]

end EReal
