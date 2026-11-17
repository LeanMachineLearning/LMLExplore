/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Bounds on the mean of a finite family

The mean `(∑ i ∈ s, f i) / #s` of a family over a nonempty finite set `s` lies between any bounds
of its entries. This is `Finset.le_expect` and `Finset.expect_le` for the average `𝔼 i ∈ s, f i`,
stated for the quotient of the sum by the cardinality, the form in which the empirical means of
samples are written.

## Main statements

* `Finset.sum_div_card_mem_Icc`: if `f i ∈ [a, b]` for every `i ∈ s`, with `s` nonempty, then
  `(∑ i ∈ s, f i) / #s ∈ [a, b]`.
* `Finset.sum_one_sub_div_card`: the mean of the `1 - f i` is `1` minus the mean of the `f i`.
* `Finset.le_add_of_sum_div_card_le`: an entry within `D` of every entry is at most `D` plus any
  upper bound of the mean.
-/

public section

open scoped BigOperators

namespace Finset

variable {ι K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The mean of the entries of a family over a nonempty finite set lies in every interval
`[a, b]` that contains these entries. -/
theorem sum_div_card_mem_Icc {s : Finset ι} (hs : s.Nonempty) {f : ι → K} {a b : K}
    (hf : ∀ i ∈ s, f i ∈ Set.Icc a b) : (∑ i ∈ s, f i) / #s ∈ Set.Icc a b := by
  rw [← expect_eq_sum_div_card]
  exact ⟨le_expect hs fun i hi ↦ (hf i hi).1, expect_le hs fun i hi ↦ (hf i hi).2⟩

/-- If `f j ≤ f i + D` for every `i ∈ s`, where `j ∈ s`, and the mean of the `f i` over `s` is at
most `B`, then `f j ≤ B + D`: an entry that is smallest up to `D` is at most the mean up to `D`. -/
theorem le_add_of_sum_div_card_le {s : Finset ι} {f : ι → K} {j : ι} (hj : j ∈ s) {B D : K}
    (hf : ∀ i ∈ s, f j ≤ f i + D) (hB : (∑ i ∈ s, f i) / #s ≤ B) : f j ≤ B + D :=
  calc f j = 𝔼 _i ∈ s, f j := (expect_const ⟨j, hj⟩ _).symm
    _ ≤ 𝔼 i ∈ s, (f i + D) := expect_le_expect hf
    _ = (∑ i ∈ s, f i) / #s + D := by
      rw [expect_add_distrib, expect_const ⟨j, hj⟩, expect_eq_sum_div_card]
    _ ≤ B + D := by gcongr

/-- The mean of the `1 - f i` over a nonempty finite set is `1` minus the mean of the `f i`. -/
theorem sum_one_sub_div_card {R : Type*} [DivisionRing R] [CharZero R] {s : Finset ι}
    (hs : s.Nonempty) (f : ι → R) :
    (∑ i ∈ s, (1 - f i)) / #s = 1 - (∑ i ∈ s, f i) / #s := by
  have hs0 : (#s : R) ≠ 0 := Nat.cast_ne_zero.2 hs.card_pos.ne'
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sub_div, div_self hs0]

end Finset
