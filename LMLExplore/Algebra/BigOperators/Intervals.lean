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
# The telescoping series `∑ 1 / ((i + 1) (i + 2))` and sums of clipped indices

Since `1 / ((i + 1) (i + 2)) = 1 / (i + 1) - 1 / (i + 2)`, the partial sums of the series
`∑ 1 / ((i + 1) (i + 2))` telescope to `1 - 1 / (n + 1)`, so they are at most `1`. A union bound
that spends the confidence `δ / ((i + 1) (i + 2))` on the `i`-th of countably many events, as in
the time-uniform deviation bounds of [LS, Lemma 33.8], thus spends at most `δ` in total.

## Main statements

* `LMLExplore.sum_range_inv_add_one_mul_add_two`:
  `∑ i < n, 1 / ((i + 1) (i + 2)) = 1 - 1 / (n + 1)`.
* `LMLExplore.sum_range_inv_add_one_mul_add_two_le_one`: `∑ i < n, 1 / ((i + 1) (i + 2)) ≤ 1`.
* `LMLExplore.sum_range_succ_comp_max_one`:
  `∑ j < n + 1, f (max 1 j) = ∑ j < n, f (j + 1) + f 1`. Clipping the index at `1` only changes
  the term `j = 0`, as for the confidence widths `max(1, N)^{-1/2}` of optimistic algorithms.
* `LMLExplore.sum_range_add_ite`:
  `∑ k < m + L, (if m ≤ k ∧ k < m + L then F k else 0) = ∑ j < L, F (m + j)`, reindexing a sum
  over a final block of indices.

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

/-- Clipping the index at `1` only changes the term `j = 0`:
`∑_{j < n + 1} f (max 1 j) = ∑_{j < n} f (j + 1) + f 1`. -/
theorem sum_range_succ_comp_max_one {M : Type*} [AddCommMonoid M] [Semiring α] [LinearOrder α]
    [IsOrderedRing α] (f : α → M) (n : ℕ) :
    ∑ j ∈ range (n + 1), f (max 1 (j : α)) = ∑ j ∈ range n, f ((j : α) + 1) + f 1 := by
  rw [sum_range_succ']
  simp [max_eq_right (le_add_of_nonneg_left (Nat.cast_nonneg (α := α) _))]

/-- A sum over the indices `k < m + L` restricted to the indices `m ≤ k < m + L` is a sum over
the shifted indices `j < L`:
`∑_{k < m + L} (if m ≤ k ∧ k < m + L then F k else 0) = ∑_{j < L} F (m + j)`. -/
theorem sum_range_add_ite {M : Type*} [AddCommMonoid M] (m L : ℕ) (F : ℕ → M) :
    ∑ k ∈ range (m + L), (if m ≤ k ∧ k < m + L then F k else 0) = ∑ j ∈ range L, F (m + j) := by
  rw [sum_range_add, sum_eq_zero fun k hk ↦ ite_eq_right fun h ↦ by simp at hk; lia, zero_add]
  exact sum_congr rfl fun j hj ↦ ite_eq_left ⟨by lia, by simp at hj; lia⟩

end LMLExplore
