/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.EReal.Inv

/-!
# Dividing an extended real by a real

## Main statements

* `EReal.coe_inv_mul`: multiplying an extended real `a` by the inverse `x⁻¹` of a real, taken in
  `ℝ` and cast to `EReal`, is dividing `a` by `x`. This holds also for `x = 0`, where both sides
  vanish. It converts between the forms `ε * log μ` and `log μ / r` of the bounds of a large
  deviation principle with speed `ε = r⁻¹`.
* `EReal.coe_nnreal_inv_natCast_mul`: the case of the speed `1 / n`, written `(n : ℝ≥0)⁻¹` as in
  `TauCeti.Probability.HasLDP`: multiplying `a` by `(n : ℝ≥0)⁻¹` is dividing `a` by `n`.
* `EReal.coe_le_div_natCast_iff`, `EReal.coe_lt_div_natCast_iff`, `EReal.div_natCast_le_coe_iff`,
  `EReal.div_natCast_lt_coe_iff`: for `0 < n`, comparing `y / n` with a real `r` is comparing `y`
  with the real `n * r`. They turn a bound on a normalized exponent into a bound on the exponent.
-/

public section

open scoped NNReal

namespace EReal

/-- Multiplying an extended real `a` by `x⁻¹`, for `x : ℝ`, is dividing `a` by `x`, also for
`x = 0`, where both sides vanish. -/
lemma coe_inv_mul (x : ℝ) (a : EReal) : ((x⁻¹ : ℝ) : EReal) * a = a / (x : EReal) := by
  rw [EReal.coe_inv, EReal.div_eq_inv_mul]

/-- Multiplying an extended real `a` by the speed `(n : ℝ≥0)⁻¹`, for `n : ℕ`, is dividing `a`
by `n`, also for `n = 0`, where both sides vanish. This is the form of the bounds of a large
deviation principle with speed `1 / n`. -/
lemma coe_nnreal_inv_natCast_mul (n : ℕ) (a : EReal) :
    (((n⁻¹ : ℝ≥0) : ℝ) : EReal) * a = a / (n : EReal) := by
  rw [NNReal.coe_inv, coe_inv_mul, NNReal.coe_natCast, EReal.coe_natCast]

variable {n : ℕ} {r : ℝ} {y : EReal}

/-- For `0 < n`, a real `r` is at most `y / n` if and only if the real `n * r` is at most `y`. -/
lemma coe_le_div_natCast_iff (hn : 0 < n) : (r : EReal) ≤ y / n ↔ ((n * r : ℝ) : EReal) ≤ y := by
  rw [le_div_iff_mul_le (by exact_mod_cast hn) (natCast_ne_top n), mul_comm, ← EReal.coe_natCast,
    ← coe_mul]

/-- For `0 < n`, a real `r` is below `y / n` if and only if the real `n * r` is below `y`. -/
lemma coe_lt_div_natCast_iff (hn : 0 < n) : (r : EReal) < y / n ↔ ((n * r : ℝ) : EReal) < y := by
  rw [lt_div_iff (by exact_mod_cast hn) (natCast_ne_top n), mul_comm, ← EReal.coe_natCast,
    ← coe_mul]

/-- For `0 < n`, `y / n` is at most a real `r` if and only if `y` is at most the real `n * r`. -/
lemma div_natCast_le_coe_iff (hn : 0 < n) : y / n ≤ r ↔ y ≤ ((n * r : ℝ) : EReal) := by
  rw [div_le_iff_le_mul (by exact_mod_cast hn) (natCast_ne_top n), ← EReal.coe_natCast, ← coe_mul]

/-- For `0 < n`, `y / n` is below a real `r` if and only if `y` is below the real `n * r`. -/
lemma div_natCast_lt_coe_iff (hn : 0 < n) : y / n < r ↔ y < ((n * r : ℝ) : EReal) := by
  rw [div_lt_iff (by exact_mod_cast hn) (natCast_ne_top n), mul_comm, ← EReal.coe_natCast,
    ← coe_mul]

end EReal
