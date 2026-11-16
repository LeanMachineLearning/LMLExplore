/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Numberings of a type

A numbering of a type `α` is an equivalence `e : α ≃ Fin n`. The elements other than the element
of number `0` have positive numbers, and a product over `α` of a function of the numbers is the
product over `{0, …, n - 1}`. The bandits whose means are in arithmetic progression along a
numbering of the arms, as in the lower bounds of [D23, Theorem 8] and [CL16, Theorem 1], use these
facts to compute their complexities.

## Main statements

* `Equiv.one_le_numbering`: every element other than the one of number `0` has number `≥ 1`.
* `Equiv.prod_numbering_eq_prod_range`, `Equiv.sum_numbering_eq_sum_range`:
  `∏_b f (e b) = ∏_{i < n} f i` and `∑_b f (e b) = ∑_{i < n} f i`.

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

/-- For a numbering `e` of `α`, the product over `α` of `f (e b)` is the product of `f i` over
`i < n`. -/
@[to_additive /-- For a numbering `e` of `α`, the sum over `α` of `f (e b)` is the sum of `f i`
over `i < n`. -/]
theorem prod_numbering_eq_prod_range [Fintype α] {M : Type*} [CommMonoid M] (e : α ≃ Fin n)
    (f : ℕ → M) : ∏ b, f (e b) = ∏ i ∈ Finset.range n, f i :=
  (e.prod_comp fun i ↦ f i).trans (Fin.prod_univ_eq_prod_range f n)

end Equiv
