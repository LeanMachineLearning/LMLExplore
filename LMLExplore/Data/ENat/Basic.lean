/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Cast.WithTop

/-!
# Extended natural numbers and natural numbers

This file relates `WithTop ℕ` to `ℕ` through the cast `(n : WithTop ℕ)`, which is `Nat.cast`
rather than the coercion `WithTop.some n`, and records how `ENat.toENNReal` acts on the
successor `t + 1` of `t : WithTop ℕ`.

## Main statements

* `ENat.natCast_toNat_min`: the minimum of `t : WithTop ℕ` and the cast `(n : WithTop ℕ)` is
  finite, so its value as a natural number casts back to it.
* `ENat.toENNReal_add_one`: `ENat.toENNReal (t + 1) = ENat.toENNReal t + 1` for `t : WithTop ℕ`.
* `WithTop.untopA_natCast`, `WithTop.natCast_untopA`: `WithTop.untopA` inverts the cast
  `ℕ → WithTop ℕ` on finite values.
* `WithTop.ne_top_of_le_natCast`: an element below the cast of a natural number is finite.
* `WithTop.exists_eq_natCast_of_ne_top`, `WithTop.exists_eq_natCast_of_forall_ne_top`: a finite
  element of `WithTop ℕ` is the cast of a natural number, and a function with finite values in
  `WithTop ℕ` is the cast of a function with values in `ℕ`.
-/

public section

namespace ENat

/-- The minimum of `t : WithTop ℕ` and the cast `(n : WithTop ℕ)` is finite, so its value as a
natural number casts back to it. -/
theorem natCast_toNat_min (t : WithTop ℕ) (n : ℕ) :
    ((ENat.toNat (min t n) : ℕ) : WithTop ℕ) = min t n :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (min_le_right _ _))

/-- The successor `t + 1` of `t : WithTop ℕ` maps to `ENat.toENNReal t + 1`. This is
`ENat.toENNReal_add` with the addition of `WithTop ℕ`, as in `τ ω + 1` for a random time `τ` with
values in `WithTop ℕ`: `simp` does not apply `ENat.toENNReal_add` to such terms, which are not
`ℕ∞`-typed up to reducible transparency. -/
@[simp]
theorem toENNReal_add_one (t : WithTop ℕ) :
    ENat.toENNReal (t + 1 : WithTop ℕ) = ENat.toENNReal t + 1 :=
  (ENat.toENNReal_add t 1).trans (by rw [ENat.toENNReal_one])

end ENat

namespace WithTop

/-- `WithTop.untopA` of the cast `(n : WithTop ℕ)` is `n`. -/
@[simp]
theorem untopA_natCast (n : ℕ) : (n : WithTop ℕ).untopA = n := by
  rw [Nat.cast_withTop, untopA_eq_untop coe_ne_top, untop_coe]

/-- The value `x.untopA` of a finite `x : WithTop ℕ` casts back to `x`. -/
theorem natCast_untopA {x : WithTop ℕ} (hx : x ≠ ⊤) : (x.untopA : WithTop ℕ) = x := by
  rw [Nat.cast_withTop, untopA_eq_untop hx, coe_untop]

/-- An element of `WithTop α` below the cast `(n : WithTop α)` of a natural number is finite. -/
theorem ne_top_of_le_natCast {α : Type*} [AddMonoidWithOne α] [PartialOrder α] {x : WithTop α}
    {n : ℕ} (h : x ≤ n) : x ≠ ⊤ :=
  ne_top_of_le_ne_top (natCast_ne_top n) h

/-- A finite element of `WithTop ℕ` is the cast `(n : WithTop ℕ)` of a natural number. Unlike
`ENat.ne_top_iff_exists`, stated for `ℕ∞`, the cast is the one into `WithTop ℕ`, so the equation
rewrites terms of type `WithTop ℕ`. -/
theorem exists_eq_natCast_of_ne_top {x : WithTop ℕ} (hx : x ≠ ⊤) : ∃ n : ℕ, x = n :=
  ⟨x.untopA, (natCast_untopA hx).symm⟩

/-- A function with finite values in `WithTop ℕ` is the cast of a function with values in `ℕ`. -/
theorem exists_eq_natCast_of_forall_ne_top {α : Type*} {f : α → WithTop ℕ} (h : ∀ a, f a ≠ ⊤) :
    ∃ g : α → ℕ, f = fun a ↦ (g a : WithTop ℕ) :=
  ⟨fun a ↦ (f a).untopA, funext fun a ↦ (natCast_untopA (h a)).symm⟩

end WithTop
