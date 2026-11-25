/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Finset.Max

/-!
# Subsets of the largest values

For a function `f` with values in a linear order and a finite set `s`, every size `j ≤ #s` is the
size of a subset `t ⊆ s` of largest values: `f` is at least as large on `t` as on the rest of `s`.
Such a set is a set of `j` arms with the largest gaps in the analysis of elimination algorithms
for best arm identification. Ties are broken arbitrarily, so the set is not unique.

Comparing a set with such a set of largest values is done by exchanges: `induction_on_exchange`
proves a property of every set `A` of the size of a set `T` by exchanging, one at a time, a member
of `A \ T` for a member of `T \ A`.
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

/-- **Induction by exchanges**: a property `p` holds for every set `A` of the size of `T` if it
holds for `T` and if it holds for `A` whenever it holds for the set `insert j (A.erase i)`
obtained by exchanging a member `i ∈ A \ T` for a member `j ∈ T \ A`, which is one step closer
to `T`. -/
theorem induction_on_exchange {T : Finset ι} {p : Finset ι → Prop} (base : p T)
    (step : ∀ A i j, #A = #T → i ∈ A → i ∉ T → j ∈ T → j ∉ A → p (insert j (A.erase i)) → p A)
    (A : Finset ι) (hA : #A = #T) : p A := by
  -- Induction on the number of members of `A` outside `T`.
  induction hn : #(A \ T) generalizing A with
  | zero => rwa [eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hn)) hA.ge]
  | succ n ih =>
    obtain ⟨i, hi⟩ : (A \ T).Nonempty := card_pos.1 (by omega)
    obtain ⟨j, hj⟩ : (T \ A).Nonempty := card_pos.1 (by rw [card_sdiff_comm hA.symm]; omega)
    rw [mem_sdiff] at hi hj
    have hset : insert j (A.erase i) \ T = (A \ T).erase i := by
      ext l
      simp only [mem_sdiff, mem_insert, mem_erase]
      constructor
      · rintro ⟨rfl | ⟨hli, hlA⟩, hlT⟩
        · exact absurd hj.1 hlT
        · exact ⟨hli, hlA, hlT⟩
      · rintro ⟨hli, hlA, hlT⟩
        exact ⟨Or.inr ⟨hli, hlA⟩, hlT⟩
    refine step A i j hA hi.1 hi.2 hj.1 hj.2 (ih _ ?_ ?_)
    · rw [card_insert_of_notMem fun h ↦ hj.2 (mem_of_mem_erase h), card_erase_add_one hi.1, hA]
    · rw [hset, card_erase_of_mem (mem_sdiff.2 hi), hn, Nat.add_sub_cancel]

end Finset
