/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions

/-!
# Counting the pulls of each arm

Facts about LML's `pullCount` that hold for any sequence of actions `A : ℕ → Ω → α`.

## Main statements

* `pullCount_eq_zero_iff`, `pullCount_eq_one_iff`: characterisations of an arm pulled zero times
  and exactly once before a given round.
* `exists_pullCount_eq_zero_of_lt_card`: before round `Fintype.card α`, some arm has not been
  pulled yet.
* `pullCount_card_eq_one_of_forall_pullCount_action_eq_zero`: if each of the first
  `Fintype.card α` rounds plays an arm not pulled before, then every arm is pulled exactly once
  during those rounds.
-/

public section

open Finset Learning

namespace LMLExplore

variable {α Ω : Type*} [DecidableEq α] {A : ℕ → Ω → α} {a : α} {n : ℕ} {ω : Ω}

/-- An arm has not been pulled before round `n` if and only if no round `s < n` played it. -/
lemma pullCount_eq_zero_iff : pullCount A a n ω = 0 ↔ ∀ s < n, A s ω ≠ a := by
  simp [pullCount, filter_eq_empty_iff]

/-- An arm has been pulled exactly once before round `n` if and only if exactly one round `s < n`
played it. -/
lemma pullCount_eq_one_iff :
    pullCount A a n ω = 1 ↔ ∃ s < n, A s ω = a ∧ ∀ t < n, A t ω = a → t = s := by
  simp [pullCount, card_eq_one, eq_singleton_iff_unique_mem, and_assoc]

variable [Fintype α]

/-- Before round `Fintype.card α`, some arm has not been pulled yet. -/
lemma exists_pullCount_eq_zero_of_lt_card (hn : n < Fintype.card α) :
    ∃ b, pullCount A b n ω = 0 := by
  by_contra! h0
  have : Fintype.card α ≤ n := calc
    Fintype.card α = ∑ _ : α, 1 := by simp
    _ ≤ ∑ a, pullCount A a n ω := sum_le_sum fun a _ ↦ Nat.one_le_iff_ne_zero.mpr (h0 a)
    _ = n := sum_pullCount
  omega

/-- If every round before `Fintype.card α` plays an arm that has not been pulled before, then every
arm is pulled exactly once during the first `Fintype.card α` rounds. -/
lemma pullCount_card_eq_one_of_forall_pullCount_action_eq_zero
    (hA : ∀ n < Fintype.card α, pullCount A (A n ω) n ω = 0) (a : α) :
    pullCount A a (Fintype.card α) ω = 1 := by
  -- The arms played during the first `Fintype.card α` rounds are pairwise distinct.
  have h_inj : Set.InjOn (A · ω) (range (Fintype.card α)) := by
    intro s hs t ht hst
    by_contra hne
    wlog hlt : s < t generalizing s t
    · exact this ht hs hst.symm (Ne.symm hne) (by omega)
    exact pullCount_eq_zero_iff.mp (hA t (by simpa using ht)) s hlt hst
  -- Hence every arm is played during those rounds, at a single round.
  have h_univ : (range (Fintype.card α)).image (A · ω) = univ :=
    eq_univ_of_card _ (by rw [card_image_of_injOn h_inj, card_range])
  obtain ⟨s, hs, rfl⟩ := mem_image.mp (h_univ ▸ mem_univ a)
  exact pullCount_eq_one_iff.mpr
    ⟨s, by simpa using hs, rfl, fun t ht hts ↦ h_inj (by simpa using ht) hs hts⟩

end LMLExplore
