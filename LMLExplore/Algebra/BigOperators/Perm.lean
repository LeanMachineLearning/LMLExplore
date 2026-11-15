/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Perm

/-!
# Sums over all permutations of the values of a function

For `w : ι → M` and `j : ι`, the sum `∑ σ : Perm ι, w (σ j)` over all permutations of a finite
type does not depend on `j`, and `K` times it is `(K!)` times `∑ i, w i`, for `K` the cardinality
of `ι`. In a semifield of characteristic zero: averaging the `w (σ j)` over the permutations `σ`
gives the average `(∑ i, w i) / K` of the `w i`, and likewise in `ℝ≥0∞`, which is not a
semifield. This is how a weighting is symmetrized.

## Main statements

* `Equiv.Perm.sum_apply_eq_sum_apply`: `∑ σ, w (σ j) = ∑ σ, w (σ k)`.
* `Equiv.Perm.card_nsmul_sum_apply`: `K • ∑ σ, w (σ j) = card (Perm ι) • ∑ i, w i`.
* `Equiv.Perm.sum_apply_div_card`: `(∑ σ, w (σ j)) / card (Perm ι) = (∑ i, w i) / K`.
* `Equiv.Perm.sum_comp_swap`: `∑ x ∈ s, w (swap a b x) = ∑ x ∈ s, w x` for `a, b ∈ s`.
* `ENNReal.sum_perm_apply_div_card`: the same identity in `ℝ≥0∞`.
-/

public section

open scoped ENNReal

namespace Equiv.Perm

variable {ι M : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of `w (σ j)` over all permutations `σ` does not depend on `j`. -/
theorem sum_apply_eq_sum_apply [AddCommMonoid M] (w : ι → M) (j k : ι) :
    ∑ σ : Perm ι, w (σ j) = ∑ σ : Perm ι, w (σ k) :=
  -- Composing with the swap of `j` and `k` permutes the permutations.
  Fintype.sum_equiv (Equiv.mulRight (Equiv.swap j k)) _ _ fun σ ↦ by simp

/-- `K` times the sum of `w (σ j)` over all permutations `σ` is the number of permutations times
`∑ i, w i`, for `K` the cardinality of `ι`. -/
theorem card_nsmul_sum_apply [AddCommMonoid M] (w : ι → M) (j : ι) :
    Fintype.card ι • ∑ σ : Perm ι, w (σ j) = Fintype.card (Perm ι) • ∑ i, w i := by
  have h : ∑ k, ∑ σ : Perm ι, w (σ k) = Fintype.card (Perm ι) • ∑ i, w i := by
    rw [Finset.sum_comm]
    simp_rw [fun σ : Perm ι ↦ Equiv.sum_comp σ w]
    rw [Finset.sum_const, Finset.card_univ]
  simpa [sum_apply_eq_sum_apply w _ j, Finset.sum_const, Finset.card_univ] using h

/-- **Averaging over all permutations**: the average of `w (σ j)` over the permutations `σ` is the
average `(∑ i, w i) / K` of the `w i`, for `K` the cardinality of `ι`. -/
theorem sum_apply_div_card [Semifield M] [CharZero M] (w : ι → M) (j : ι) :
    (∑ σ : Perm ι, w (σ j)) / Fintype.card (Perm ι) = (∑ i, w i) / Fintype.card ι := by
  have hN : (Fintype.card (Perm ι) : M) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hK : (Fintype.card ι : M) ≠ 0 := Nat.cast_ne_zero.2 (@Fintype.card_ne_zero ι _ ⟨j⟩)
  have h := card_nsmul_sum_apply w j
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  rw [div_eq_div_iff hN hK, mul_comm, h, mul_comm]

/-- Composing with the swap of two elements of a finset does not change the sum over it. -/
theorem sum_comp_swap [AddCommMonoid M] {α : Type*} [DecidableEq α] {s : Finset α} {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (w : α → M) : ∑ x ∈ s, w (Equiv.swap a b x) = ∑ x ∈ s, w x := by
  refine sum_comp (Equiv.swap a b) s w fun x hx ↦ ?_
  rcases eq_or_ne x a with rfl | hxa
  · exact ha
  rcases eq_or_ne x b with rfl | hxb
  · exact hb
  exact absurd (Equiv.swap_apply_of_ne_of_ne hxa hxb) hx

end Equiv.Perm

namespace ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Averaging over all permutations** in `ℝ≥0∞`: the average of `w (σ j)` over the
permutations `σ` is the average `(∑ i, w i) / K` of the `w i`, for `K` the cardinality of `ι`. -/
theorem sum_perm_apply_div_card (w : ι → ℝ≥0∞) (j : ι) :
    (∑ σ : Equiv.Perm ι, w (σ j)) / Fintype.card (Equiv.Perm ι) = (∑ i, w i) / Fintype.card ι := by
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (@Fintype.card_ne_zero ι _ ⟨j⟩)
  rw [ENNReal.div_eq_div_iff hK (by simp) (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by simp)]
  simpa [nsmul_eq_mul] using Equiv.Perm.card_nsmul_sum_apply w j

end ENNReal
