/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Cast.WithTop

/-!
# Extended natural numbers and natural numbers

This file relates `WithTop ℕ` to `ℕ` through the cast `(n : WithTop ℕ)`, which is `Nat.cast`
rather than the coercion `WithTop.some n`.

## Main statements

* `ENat.natCast_toNat_min`: the minimum of `t : WithTop ℕ` and the cast `(n : WithTop ℕ)` is
  finite, so its value as a natural number casts back to it.
* `WithTop.untopA_natCast`, `WithTop.natCast_untopA`: `WithTop.untopA` inverts the cast
  `ℕ → WithTop ℕ` on finite values.
-/

public section

namespace ENat

/-- The minimum of `t : WithTop ℕ` and the cast `(n : WithTop ℕ)` is finite, so its value as a
natural number casts back to it. -/
theorem natCast_toNat_min (t : WithTop ℕ) (n : ℕ) :
    ((ENat.toNat (min t n) : ℕ) : WithTop ℕ) = min t n :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (min_le_right _ _))

end ENat

namespace WithTop

/-- `WithTop.untopA` of the cast `(n : WithTop ℕ)` is `n`. -/
@[simp]
theorem untopA_natCast (n : ℕ) : (n : WithTop ℕ).untopA = n := by
  rw [Nat.cast_withTop, untopA_eq_untop coe_ne_top, untop_coe]

/-- The value `x.untopA` of a finite `x : WithTop ℕ` casts back to `x`. -/
theorem natCast_untopA {x : WithTop ℕ} (hx : x ≠ ⊤) : (x.untopA : WithTop ℕ) = x := by
  rw [Nat.cast_withTop, untopA_eq_untop hx, coe_untop]

end WithTop
