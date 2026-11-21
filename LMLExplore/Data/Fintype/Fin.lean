/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Fintype.Fin

/-!
# Thresholds of antitone families indexed by `Fin n`

For an antitone family `y : Fin n → β`, the indices `j` with `c ≤ y j` form an initial segment,
so at least `k` of them satisfy the threshold exactly when the index `k - 1` does. This reads the
`k`-th largest value of a sorted family off a count, as in the step-up procedures of multiple
testing.

## Main statements

* `Antitone.le_card_filter_le_iff`: for `1 ≤ k ≤ n`, `k ≤ #{j | c ≤ y j} ↔ c ≤ y (k - 1)`.
-/

public section

open Finset

namespace Antitone

variable {β : Type*} [LinearOrder β] {n : ℕ} {y : Fin n → β}

/-- At least `k` indices of an antitone family `y : Fin n → β` satisfy the threshold `c ≤ y j`
exactly when the index `k - 1` does, for `1 ≤ k ≤ n`. -/
theorem le_card_filter_le_iff (hy : Antitone y) {k : ℕ} (hk0 : 0 < k) (hkn : k ≤ n) (c : β) :
    k ≤ #{j | c ≤ y j} ↔ c ≤ y ⟨k - 1, by omega⟩ := by
  constructor
  · intro h
    by_contra hc
    have hsub : ({j | c ≤ y j} : Finset (Fin n)) ⊆ ({j | (j : ℕ) < k - 1} : Finset (Fin n)) :=
      fun j hj ↦ by
        rw [mem_filter] at hj ⊢
        exact ⟨mem_univ j, not_le.1 fun hjk ↦ hc (hj.2.trans (hy (Fin.mk_le_mk.2 hjk)))⟩
    have := (card_le_card hsub).trans_eq Fin.card_filter_val_lt
    omega
  · intro hc
    refine (min_eq_right hkn).symm.le.trans
      ((Fin.card_filter_val_lt (m := k)).symm.le.trans (card_le_card fun j hj ↦ ?_))
    rw [mem_filter] at hj ⊢
    exact ⟨mem_univ j, hc.trans (hy (Fin.mk_le_mk.2 (by omega)))⟩

end Antitone
