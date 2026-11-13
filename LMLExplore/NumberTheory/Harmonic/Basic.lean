/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Tactic.Ring

/-!
# Harmonic numbers as sums of reversed inverses and of inverse ranks

The harmonic number `H_K = ∑_{i = 1}^K 1 / i`, minus its first term, is the sum
`∑_{j < K - 1} 1 / (K - j) = 1 / K + ⋯ + 1 / 2` of the inverses taken in decreasing order of the
denominators. Such sums appear when the `j`-th phase of an elimination algorithm with `K` arms
pulls `K - j` arms, as in successive rejects for best arm identification.

The harmonic number `H_K` also bounds the sum of the inverse ranks of `K` elements ranked by a
function `f` with values in a linear order, where the rank `#{c | f c ≤ f b}` of `b` counts ties
at their largest rank. This compares sums of the form `∑_b x_b` with `max_b r_b x_b`, as in the
comparison of the complexities `H₁` and `H₂` of best arm identification, without sorting.

## Main statements

* `LMLExplore.sum_range_inv_add_one_sub_eq_harmonic_sub_one`:
  `∑_{j < m} 1 / (m + 1 - j) = H_{m + 1} - 1`.
* `LMLExplore.sum_range_inv_sub_eq_harmonic_sub_one`: `∑_{j < K - 1} 1 / (K - j) = H_K - 1` for
  `K ≠ 0`.
* `harmonic_mono`: the harmonic numbers are monotone.
* `Finset.sum_inv_card_filter_le_le_harmonic`: `∑_{b ∈ s} 1 / #{c ∈ s | f c ≤ f b} ≤ H_{#s}`.
-/

public section

open Finset

namespace LMLExplore

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- `∑_{j < m} 1 / (m + 1 - j) = H_{m + 1} - 1`, with `H` the harmonic numbers. -/
theorem sum_range_inv_add_one_sub_eq_harmonic_sub_one (m : ℕ) :
    ∑ j ∈ range m, ((m + 1 - j : 𝕜))⁻¹ = harmonic (m + 1) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ', harmonic_succ (m + 1)]
    push_cast
    rw [sum_congr rfl fun j _ ↦ by rw [show (m + 1 + 1 - (j + 1) : 𝕜) = m + 1 - j by ring], ih]
    ring

/-- `∑_{j < K - 1} 1 / (K - j) = H_K - 1` for `K ≠ 0`, with `H` the harmonic numbers. -/
theorem sum_range_inv_sub_eq_harmonic_sub_one {K : ℕ} (hK : K ≠ 0) :
    ∑ j ∈ range (K - 1), ((K - j : 𝕜))⁻¹ = harmonic K - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
  rw [Nat.succ_sub_one, Nat.cast_succ]
  exact sum_range_inv_add_one_sub_eq_harmonic_sub_one m

end LMLExplore

/-- The harmonic numbers are monotone. -/
theorem harmonic_mono : Monotone harmonic :=
  monotone_nat_of_le_succ fun n ↦ by
    rw [harmonic_succ]
    exact le_add_of_nonneg_right (inv_nonneg.2 (Nat.cast_nonneg _))

namespace Finset

variable {ι β 𝕜 : Type*} [LinearOrder β] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **Sum of inverse ranks.** Rank the elements of a finite set `s` by `f`, giving each element
`b` the rank `#{c ∈ s | f c ≤ f b}`, the largest rank of its block of ties. The inverse ranks sum
to at most the harmonic number `H_{#s}`. -/
theorem sum_inv_card_filter_le_le_harmonic (s : Finset ι) (f : ι → β) :
    ∑ b ∈ s, ((#{c ∈ s | f c ≤ f b} : 𝕜))⁻¹ ≤ harmonic #s := by
  classical
  induction s using Finset.induction_on_max_value f with
  | empty => simp
  | insert a s ha hmax ih =>
    -- The new element `a` has the largest value, hence the rank `#s + 1`, and adding it does not
    -- decrease the ranks of the elements of `s`.
    have h_top : {c ∈ insert a s | f c ≤ f a} = insert a s :=
      filter_true_of_mem fun c hc ↦ (mem_insert.1 hc).elim (fun h ↦ h ▸ le_rfl) (hmax c)
    have h_rank (b : ι) (hb : b ∈ s) :
        ((#{c ∈ insert a s | f c ≤ f b} : 𝕜))⁻¹ ≤ ((#{c ∈ s | f c ≤ f b} : 𝕜))⁻¹ := by
      refine inv_anti₀ (by exact_mod_cast card_pos.2 ⟨b, by simp [hb]⟩) ?_
      exact_mod_cast card_le_card (filter_subset_filter _ (subset_insert a s))
    rw [sum_insert ha, h_top, card_insert_of_notMem ha, harmonic_succ, Rat.cast_add, add_comm]
    push_cast
    gcongr
    exact (sum_le_sum h_rank).trans ih

end Finset
