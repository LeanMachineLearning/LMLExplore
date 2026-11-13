/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.EReal.Inv
import Mathlib.Basic.ENNReal.Inv

/-!
# Inverses of extended reals and their positive parts

## Main statements

* `EReal.toENNReal_inv`: the positive part of the inverse of a positive extended real is the
  inverse of its positive part, `x⁻¹.toENNReal = x.toENNReal⁻¹` for `0 < x`.
-/

public section

open scoped ENNReal

namespace EReal

/-- The positive part of the inverse of a positive extended real is the inverse of its positive
part. For `x = 0` the two sides differ: `(0 : EReal)⁻¹ = 0` while `(0 : ℝ≥0∞)⁻¹ = ∞`. -/
lemma toENNReal_inv {x : EReal} (hx : 0 < x) : x⁻¹.toENNReal = x.toENNReal⁻¹ := by
  induction x with
  | bot => exact absurd hx (not_lt.2 bot_le)
  | top => simp
  | coe x =>
    have hx' : 0 < x := EReal.coe_pos.1 hx
    rw [← coe_inv, toENNReal_of_ne_top (coe_ne_top _), toENNReal_of_ne_top (coe_ne_top _)]
    simp [ENNReal.ofReal_inv_of_pos hx']

end EReal
