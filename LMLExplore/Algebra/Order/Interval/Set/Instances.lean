/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Interval.Set.Defs

/-!
# Multiplying by the unit interval in an ordered semiring

In an ordered semiring, multiplying by `γ ≥ 0` maps the unit interval `[0, 1]` into `[0, γ]`.
This complements the unit-interval lemmas of `Mathlib.Algebra.Order.Interval.Set.Instances`.

## Main statements

* `Set.mul_mem_Icc_zero`: `c * γ ∈ [0, γ]` for `c ∈ [0, 1]` and `0 ≤ γ`.
-/

public section

namespace Set

variable {α : Type*} [Semiring α] [PartialOrder α] [IsOrderedRing α]

/-- An element of `[0, 1]` multiplied by `γ ≥ 0` lies in `[0, γ]`. -/
theorem mul_mem_Icc_zero {γ c : α} (hγ : 0 ≤ γ) (hc : c ∈ Icc (0 : α) 1) : c * γ ∈ Icc 0 γ :=
  ⟨mul_nonneg hc.1 hγ, mul_le_of_le_one_left hγ hc.2⟩

end Set
