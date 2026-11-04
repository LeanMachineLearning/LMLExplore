/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Finset.Max

/-!
# Subsets of the largest values

For a function `f` with values in a linear order and a finite set `s`, every size `j ≤ #s` is the
size of a subset `t ⊆ s` of largest values: `f` is at least as large on `t` as on the rest of `s`.
Such a set is a set of `j` arms with the largest gaps in the analysis of elimination algorithms
for best arm identification. Ties are broken arbitrarily, so the set is not unique.
-/

public section

namespace Finset

variable {ι β : Type*} [DecidableEq ι] [LinearOrder β]

/-- For every `j ≤ #s`, the finite set `s` has a subset `t` of size `j` on which `f` is at least
its values on `s \ t`. -/
theorem exists_subset_card_eq_forall_le (f : ι → β) {s : Finset ι} {j : ℕ} (hj : j ≤ #s) :
    ∃ t ⊆ s, #t = j ∧ ∀ b ∈ t, ∀ c ∈ s \ t, f c ≤ f b := by
  induction j with
  | zero => exact ⟨∅, empty_subset _, card_empty, by simp⟩
  | succ j ih =>
    obtain ⟨t, hts, htj, ht⟩ := ih (by omega)
    obtain ⟨x, hx, hx_max⟩ := exists_max_image (s \ t) f
      (card_pos.1 (by rw [card_sdiff_of_subset hts]; omega))
    have hxt : x ∉ t := (mem_sdiff.1 hx).2
    refine ⟨insert x t, insert_subset (mem_sdiff.1 hx).1 hts,
      by rw [card_insert_of_notMem hxt, htj], fun b hb c hc ↦ ?_⟩
    rw [mem_sdiff, mem_insert, not_or] at hc
    rcases mem_insert.1 hb with rfl | hb
    · exact hx_max c (mem_sdiff.2 ⟨hc.1, hc.2.2⟩)
    · exact ht b hb c (mem_sdiff.2 ⟨hc.1, hc.2.2⟩)

end Finset
