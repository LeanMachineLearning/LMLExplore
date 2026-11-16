/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.ENat.Basic

/-!
# The minimum of an extended natural number and a natural number

## Main statements

* `ENat.natCast_toNat_min`: the minimum of `t : WithTop ℕ` and the cast `(n : WithTop ℕ)` is
  finite, so its value as a natural number casts back to it.
-/

public section

namespace ENat

/-- The minimum of `t : WithTop ℕ` and the cast `(n : WithTop ℕ)` is finite, so its value as a
natural number casts back to it. -/
theorem natCast_toNat_min (t : WithTop ℕ) (n : ℕ) :
    ((ENat.toNat (min t n) : ℕ) : WithTop ℕ) = min t n :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (min_le_right _ _))

end ENat
