/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Absolute values of a family with zero sum

If `∑ b ∈ s, u b = 0` in a linearly ordered additive group, the positive and the nonpositive
entries of `u` have opposite sums, so `∑ b ∈ s, |u b|` is twice the sum of the positive entries.
For the difference `u = q - p` of two probability vectors, this is the identity between the `ℓ¹`
distance and twice the largest difference `q(B) - p(B)` over sets `B`, which reduces deviation
bounds in `ℓ¹` to bounds on the sets `B`.

## Main statements

* `Finset.sum_abs_eq_two_nsmul_sum_filter_pos`: `∑ b ∈ s, |u b| = 2 • ∑ b ∈ s with 0 < u b, u b`
  when `∑ b ∈ s, u b = 0`.
-/

public section

namespace Finset

variable {β M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

/-- A family with zero sum has absolute values summing to twice the sum of its positive
entries. -/
theorem sum_abs_eq_two_nsmul_sum_filter_pos {s : Finset β} {u : β → M}
    (hu : ∑ b ∈ s, u b = 0) : ∑ b ∈ s, |u b| = 2 • ∑ b ∈ s with 0 < u b, u b := by
  rw [← sum_filter_add_sum_filter_not s (fun b ↦ 0 < u b)] at hu ⊢
  rw [sum_congr rfl fun b hb ↦ abs_of_pos (mem_filter.1 hb).2,
    sum_congr rfl fun b hb ↦ abs_of_nonpos (not_lt.1 (mem_filter.1 hb).2), sum_neg_distrib,
    eq_neg_of_add_eq_zero_right hu, neg_neg, two_nsmul]

end Finset
