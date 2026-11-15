/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# A multiple of the ceiling of a quotient

For `0 < b` in a linearly ordered semifield with a floor, `b` times the natural ceiling of `a / b`
is at least `a`. This chooses a natural number of steps of size `b` that cover `a`.

## Main statements

* `Nat.le_mul_ceil_div`: `a ≤ b * ⌈a / b⌉₊` for `0 < b`.
-/

public section

namespace Nat

variable {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  {a b : K}

/-- For `0 < b`, `b` times the natural ceiling of `a / b` is at least `a`. -/
theorem le_mul_ceil_div (hb : 0 < b) : a ≤ b * ⌈a / b⌉₊ :=
  (div_le_iff₀' hb).1 (le_ceil _)

end Nat
