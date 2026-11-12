/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.EReal.Inv
import Mathlib.Basic.ENNReal.Inv

/-!
# Inverses of extended reals and their positive parts

## Main statements

* `EReal.toENNReal_inv_natCast`: the positive part of the inverse of a nonzero natural number,
  `((n : EReal)⁻¹).toENNReal = (n : ℝ≥0∞)⁻¹`.
-/

public section

open scoped ENNReal

namespace EReal

/-- The positive part of the inverse of a nonzero natural number in `EReal` is its inverse in
`ℝ≥0∞`. For `n = 0` the two sides differ: `(0 : EReal)⁻¹ = 0` while `(0 : ℝ≥0∞)⁻¹ = ∞`. -/
lemma toENNReal_inv_natCast {n : ℕ} (hn : n ≠ 0) : ((n : EReal)⁻¹).toENNReal = (n : ℝ≥0∞)⁻¹ := by
  rw [← EReal.coe_natCast, ← coe_inv, toENNReal_of_ne_top (coe_ne_top _)]
  simp [ENNReal.ofReal_inv_of_pos, Nat.pos_of_ne_zero hn]

end EReal
