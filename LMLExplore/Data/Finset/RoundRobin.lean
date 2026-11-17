/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.CardIntervalMod
public import LMLExplore.Data.List.GetD

/-!
# Round robins over a finite set

A round robin over a nonempty finite set `S` enumerates the elements of `S` cyclically, in the
order of the bijection `S.equivFin` between `S` and `Fin #S`. During `#S * d` rounds, it visits
each element of `S` exactly `d` times. Elimination algorithms for best arm identification, such as
successive rejects, pull the arms that survive a phase in such a round robin.

## Main definitions

* `Finset.roundRobinOn S r`: the element visited at offset `r` of the round robin over `S`.
* `Finset.roundRobinList S n`: the list of the elements visited during the first `n` rounds of the
  round robin over `S`.

## Main statements

* `Finset.roundRobinOn_mem`: the round robin over a nonempty set visits its elements.
* `Finset.card_filter_roundRobinOn_eq`: during `#S * d` rounds, the round robin over `S` visits
  each element of `S` exactly `d` times.
* `Finset.count_roundRobinList`, `Finset.count_roundRobinList_card_mul`: the number of occurrences
  of an element in the list of the first `n` rounds of a round robin.
-/

public section

namespace Finset

variable {α : Type*} [Nonempty α]

/-- The element visited at offset `r` of a round robin over the finite set `S` (an arbitrary
element if `S` is empty). -/
noncomputable def roundRobinOn (S : Finset α) (r : ℕ) : α :=
  if h : S.Nonempty then (S.equivFin.symm ⟨r % #S, Nat.mod_lt _ h.card_pos⟩ : α)
  else Classical.arbitrary α

lemma roundRobinOn_def (S : Finset α) (r : ℕ) :
    roundRobinOn S r = if h : S.Nonempty
      then (S.equivFin.symm ⟨r % #S, Nat.mod_lt _ h.card_pos⟩ : α) else Classical.arbitrary α :=
  (rfl)

lemma roundRobinOn_mem {S : Finset α} (hS : S.Nonempty) (r : ℕ) : roundRobinOn S r ∈ S := by
  simp only [roundRobinOn, hS, dite_true, coe_mem]

/-- A round robin over `S` during `#S * d` rounds visits each element of `S` exactly `d` times. -/
lemma card_filter_roundRobinOn_eq [DecidableEq α] (S : Finset α) (d : ℕ) (a : α) :
    #{r ∈ range (#S * d) | roundRobinOn S r = a} = if a ∈ S then d else 0 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  split_ifs with ha
  · have h_iff (r : ℕ) : roundRobinOn S r = a ↔ r ≡ (S.equivFin ⟨a, ha⟩ : ℕ) [MOD #S] := by
      have : roundRobinOn S r = a ↔
          S.equivFin.symm ⟨r % #S, Nat.mod_lt _ hS.card_pos⟩ = ⟨a, ha⟩ := by
        simp only [roundRobinOn, hS, dite_true, Subtype.ext_iff]
      simp [this, Equiv.symm_apply_eq, Fin.ext_iff, Nat.ModEq,
        Nat.mod_eq_of_lt (S.equivFin ⟨a, ha⟩).isLt]
    simp [h_iff, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hS.card_pos,
      hS.card_pos]
  · rw [card_eq_zero, filter_eq_empty_iff]
    exact fun r _ h ↦ ha (h ▸ roundRobinOn_mem hS r)

/-- The list of the elements visited during the first `n` rounds of the round robin over the finite
set `S`. -/
noncomputable def roundRobinList (S : Finset α) (n : ℕ) : List α :=
  (List.range n).map (roundRobinOn S)

lemma roundRobinList_def (S : Finset α) (n : ℕ) :
    roundRobinList S n = (List.range n).map (roundRobinOn S) := (rfl)

@[simp]
lemma length_roundRobinList (S : Finset α) (n : ℕ) : (roundRobinList S n).length = n := by
  simp [roundRobinList]

@[simp]
lemma getElem_roundRobinList (S : Finset α) (n j : ℕ) (hj : j < (roundRobinList S n).length) :
    (roundRobinList S n)[j] = roundRobinOn S j := by
  simp [roundRobinList]

/-- The first `n` rounds of the round robin over `S` visit `a` as many times as there are rounds
`r < n` at which it visits `a`. -/
lemma count_roundRobinList [DecidableEq α] (S : Finset α) (n : ℕ) (a : α) :
    (roundRobinList S n).count a = #{r ∈ range n | roundRobinOn S r = a} := by
  rw [List.count_eq_sum_range_getD _ a a, card_filter, length_roundRobinList]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [List.getD_eq_getElem _ _ (by rw [length_roundRobinList]; exact mem_range.1 hj),
    getElem_roundRobinList]

/-- The first `#S * d` rounds of the round robin over `S` visit each element of `S` exactly `d`
times. -/
lemma count_roundRobinList_card_mul [DecidableEq α] (S : Finset α) (d : ℕ) (a : α) :
    (roundRobinList S (#S * d)).count a = if a ∈ S then d else 0 := by
  rw [count_roundRobinList, card_filter_roundRobinOn_eq]

end Finset
