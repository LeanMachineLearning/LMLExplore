/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The telescoping series `∑ 1 / ((i + 1) (i + 2))`

Since `1 / ((i + 1) (i + 2)) = 1 / (i + 1) - 1 / (i + 2)`, the partial sums of the series
`∑ 1 / ((i + 1) (i + 2))` telescope to `1 - 1 / (n + 1)`, so they are at most `1`. A union bound
that spends the confidence `δ / ((i + 1) (i + 2))` on the `i`-th of countably many events, as in
the time-uniform deviation bounds of [LS, Lemma 33.8], thus spends at most `δ` in total.

## Main statements

* `LMLExplore.sum_range_inv_add_one_mul_add_two`:
  `∑ i < n, 1 / ((i + 1) (i + 2)) = 1 - 1 / (n + 1)`.
* `LMLExplore.sum_range_inv_add_one_mul_add_two_le_one`: `∑ i < n, 1 / ((i + 1) (i + 2)) ≤ 1`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset

namespace LMLExplore

variable {α : Type*}

/-- The partial sums of the telescoping series
`∑ 1 / ((i + 1) (i + 2)) = ∑ (1 / (i + 1) - 1 / (i + 2))` are `1 - 1 / (n + 1)`. -/
theorem sum_range_inv_add_one_mul_add_two [Field α] [CharZero α] (n : ℕ) :
    ∑ i ∈ range n, ((i + 1 : α) * (i + 2))⁻¹ = 1 - (n + 1 : α)⁻¹ := by
  have h (i : ℕ) : ((i + 1 : α) * (i + 2))⁻¹ = ((i : α) + 1)⁻¹ - (((i + 1 : ℕ) : α) + 1)⁻¹ := by
    have h1 : (i + 1 : α) ≠ 0 := Nat.cast_add_one_ne_zero i
    have h2 : (i + 2 : α) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (i + 1)
    rw [Nat.cast_add_one, add_assoc, one_add_one_eq_two]
    field_simp
    ring
  rw [sum_congr rfl fun i _ ↦ h i, sum_range_sub' (fun i : ℕ ↦ ((i : α) + 1)⁻¹) n]
  simp

/-- The partial sums of the series `∑ 1 / ((i + 1) (i + 2))` are at most `1`. -/
theorem sum_range_inv_add_one_mul_add_two_le_one [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (n : ℕ) : ∑ i ∈ range n, ((i + 1 : α) * (i + 2))⁻¹ ≤ 1 := by
  rw [sum_range_inv_add_one_mul_add_two]
  exact sub_le_self _ (by positivity)

end LMLExplore
