/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# Numberings of a type

A numbering of a type `α` is an equivalence `e : α ≃ Fin n`. The elements other than the element
of number `0` have positive numbers. The bandits whose means are in arithmetic progression along a
numbering of the arms, as in the lower bounds of [D23, Theorem 8] and [CL16, Theorem 1], use this
fact to compute their complexities.

## Main statements

* `Equiv.one_le_numbering`: every element other than the one of number `0` has number `≥ 1`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [CL16] A. Carpentier and A. Locatelli, *Tight (lower) bounds for the fixed budget best arm
  identification bandit problem*, COLT 2016.
-/

public section

namespace Equiv

variable {α : Type*} {n : ℕ}

/-- In a numbering `e` of `α`, every element other than the element `a₀` of number `0` has a
positive number. -/
theorem one_le_numbering (e : α ≃ Fin n) {a₀ a : α} (ha₀ : (e a₀ : ℕ) = 0)
    (ha : a ≠ a₀) : 1 ≤ (e a : ℕ) :=
  Nat.one_le_iff_ne_zero.2 fun h ↦ ha (e.injective (Fin.ext (h.trans ha₀.symm)))

end Equiv
