/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Nat.Nth

/-!
# The `k`-th number satisfying a predicate, below a count

For a predicate `p` on `ℕ`, `Nat.count p n` is the number of `s < n` satisfying `p`, and
`Nat.nth p k` the `k`-th of all the numbers satisfying `p`. Mathlib's statements on `Nat.nth p k`
are conditioned on `k` being less than the cardinality of `p` when it is finite. This file states
them under the hypothesis `k < Nat.count p n`, which bounds this cardinality, and compares the
counts and the `k`-th numbers of two predicates that agree below `n`. These are the facts used to
index the subsequence of the rounds `s < n` satisfying `p`, such as the rounds of nonzero feedback
of an online learner, by `k < Nat.count p n`.

## Main statements

* `Nat.nth_mem_of_lt_count`, `Nat.count_nth_of_lt_count`: for `k < count p n`, the number
  `nth p k` satisfies `p` and has `k` numbers satisfying `p` below it.
* `Nat.count_eq_count_of_forall_lt_iff`, `Nat.nth_eq_nth_of_forall_lt_iff`: two predicates that
  agree below `n` have the same count at `n` and the same `k`-th number for `k` below this count.
-/

public section

namespace Nat

variable {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n k : ℕ}

/-- For `k` below the number of `s < n` satisfying `p`, the `k`-th number satisfying `p`
satisfies `p`. -/
theorem nth_mem_of_lt_count (hk : k < count p n) : p (nth p k) :=
  nth_mem k fun hf ↦ hk.trans_le (count_le_card hf n)

/-- For `k` below the number of `s < n` satisfying `p`, there are `k` numbers satisfying `p` below
the `k`-th of them. -/
theorem count_nth_of_lt_count (hk : k < count p n) : count p (nth p k) = k :=
  count_nth fun hf ↦ hk.trans_le (count_le_card hf n)

/-- Two predicates that agree below `n` have the same number of `s < n` satisfying them. -/
theorem count_eq_count_of_forall_lt_iff (hpq : ∀ s < n, p s ↔ q s) : count p n = count q n := by
  simp only [count_eq_card_filter_range]
  exact congrArg Finset.card (Finset.filter_congr fun s hs ↦ hpq s (Finset.mem_range.mp hs))

omit [DecidablePred p] in
/-- Two predicates that agree below `n` have the same `k`-th number, for `k` below the number of
`s < n` satisfying them. -/
theorem nth_eq_nth_of_forall_lt_iff (hpq : ∀ s < n, p s ↔ q s) (hk : k < count q n) :
    nth p k = nth q k := by
  classical
  -- the `k`-th number satisfying `q` is below `n`, so it satisfies `p`, with `k` numbers
  -- satisfying `p` below it
  have h_lt : nth q k < n := nth_lt_of_lt_count hk
  have hp : p (nth q k) := (hpq _ h_lt).mpr (nth_mem_of_lt_count hk)
  have h_count : count p (nth q k) = k := by
    rw [count_eq_count_of_forall_lt_iff fun s hs ↦ hpq s (hs.trans h_lt),
      count_nth_of_lt_count hk]
  rw [← nth_count hp, h_count]

end Nat
