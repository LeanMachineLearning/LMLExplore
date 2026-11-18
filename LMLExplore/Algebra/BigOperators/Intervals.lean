/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic

/-!
# The telescoping series `∑ 1 / ((i + 1) (i + 2))` and sums of clipped and shifted indices

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
* `LMLExplore.prod_range_add_mod`, `LMLExplore.sum_range_add_mod`:
  `∑ x < K, f ((z + x) % K) = ∑ x < K, f x`, a sum over a full period of residues does not depend
  on its starting point.
* `LMLExplore.two_mul_sum_range_sub`: `2 * ∑ i < n, (n - i) = n * (n + 1)`, Gauss' summation
  formula for the reflected indices `n - i`.
* `LMLExplore.two_mul_sum_range_cast_add_one`: `2 * ∑ i < n, (i + 1) = n * (n + 1)` in a
  commutative semiring, Gauss' summation formula for the weights `i + 1`.
* `LMLExplore.apply_sum_range_congr`: a function `f t (∑ s < t, c s)` of the partial sum of `c`
  depends only on the values `c s` for `s < t`.

## Implementation notes

`LMLExplore.sum_range_add_mod` and `LMLExplore.two_mul_sum_range_sub` are adapted from the helpers
of the same names in `EValuesResearch/Results/RunningMaxima.lean` (commit `ffba78a`) of the paper
project `RemyDegenne/evalues_research`.

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

/-- A product over a full period of residues modulo `K` does not depend on its starting point `z`:
`∏_{x < K} f ((z + x) % K) = ∏_{x < K} f x`. -/
@[to_additive /-- A sum over a full period of residues modulo `K` does not depend on its starting
point `z`: `∑_{x < K} f ((z + x) % K) = ∑_{x < K} f x`. -/]
theorem prod_range_add_mod {M : Type*} [CommMonoid M] (f : ℕ → M) (K z : ℕ) :
    ∏ x ∈ range K, f ((z + x) % K) = ∏ x ∈ range K, f x := by
  rcases K with _ | K
  · simp
  rw [← Fin.prod_univ_eq_prod_range (fun x ↦ f ((z + x) % (K + 1))),
    ← Fin.prod_univ_eq_prod_range f]
  exact Fintype.prod_equiv (Equiv.addLeft (Fin.ofNat (K + 1) z)) _ _ fun x ↦ by simp [Fin.val_add]

/-- Gauss' summation formula for the reflected indices `n - i`:
`2 * ∑_{i < n} (n - i) = n * (n + 1)`. -/
theorem two_mul_sum_range_sub (n : ℕ) : 2 * ∑ i ∈ range n, (n - i) = n * (n + 1) := by
  have h : ∑ i ∈ range n, (n - i) = ∑ i ∈ range (n + 1), i := by
    rw [sum_range_succ', add_zero, ← sum_range_reflect (fun i ↦ i + 1)]
    exact sum_congr rfl fun i hi ↦ by have := mem_range.1 hi; omega
  rw [h, mul_comm 2, sum_range_id_mul_two, Nat.add_sub_cancel, mul_comm]

/-- Gauss' summation formula for the weights `i + 1`, in a commutative semiring:
`2 * ∑_{i < n} (i + 1) = n * (n + 1)`. -/
theorem two_mul_sum_range_cast_add_one [CommSemiring α] (n : ℕ) :
    2 * ∑ i ∈ range n, ((i : α) + 1) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- A function `f t (∑ s < t, c s)` of the partial sum of `c` up to `t` depends only on the values
`c s` for `s < t`. -/
theorem apply_sum_range_congr {M β : Type*} [AddCommMonoid M] (f : ℕ → M → β) {t : ℕ}
    {c c' : ℕ → M} (h : ∀ s < t, c s = c' s) :
    f t (∑ s ∈ range t, c s) = f t (∑ s ∈ range t, c' s) := by
  rw [sum_congr rfl fun s hs ↦ h s (mem_range.1 hs)]

end LMLExplore
