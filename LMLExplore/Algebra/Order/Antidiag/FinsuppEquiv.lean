/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# The number of vectors of natural numbers with a given sum

The functions `f : ι → ℕ` supported in a finite set `s` with `∑ i ∈ s, f i = n` form the finset
`Finset.piAntidiag s n`. They are the `(#s + n - 1).choose n` multisets of size `n` on `s`
(stars and bars), which is at most `(n + 1) ^ (#s - 1)`: such a vector is determined by its values
outside one point of `s`, which lie in `{0, …, n}`.

In the method of types of information theory, these vectors are the types of the sequences of
length `n` with letters in `s`, and the bound is the polynomial bound on the number of types.
-/

public section

namespace Finset

variable {ι : Type*} [DecidableEq ι]

/-- **Stars and bars**: there are `(#s + n - 1).choose n` functions `f : ι → ℕ` supported in `s`
with `∑ i ∈ s, f i = n`. -/
theorem card_piAntidiag_nat_eq_choose (s : Finset ι) (n : ℕ) :
    #(piAntidiag s n) = (#s + n - 1).choose n := by
  rw [← card_finsuppAntidiag_nat_eq_choose, finsuppAntidiag, card_map, card_attach]

/-- There are at most `(n + 1) ^ (#s - 1)` functions `f : ι → ℕ` supported in `s` with
`∑ i ∈ s, f i = n`. -/
theorem card_piAntidiag_nat_le_pow (s : Finset ι) (n : ℕ) :
    #(piAntidiag s n) ≤ (n + 1) ^ (#s - 1) := by
  rw [card_piAntidiag_nat_eq_choose]
  rcases Nat.eq_zero_or_pos #s with hs | hs
  · rw [hs]
    rcases n with _ | n <;> simp
  · rw [show #s + n - 1 = n + (#s - 1) by omega, Nat.choose_symm_add]
    exact Nat.choose_add_le_add_one_pow n (#s - 1)

end Finset
