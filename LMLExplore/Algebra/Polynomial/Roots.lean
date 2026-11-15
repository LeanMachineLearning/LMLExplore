/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Polynomial.Roots

/-!
# A rational function with few zeros

A sum `s ↦ ∑ y, c y / (p₁ y + s * p₂ y)` over a finite type, with values in a field, is a
rational function of `s`: multiplied by `∏ y, (p₁ y + s * p₂ y)`, it is a polynomial of degree
less than the number of terms. If it vanishes at as many distinct points as there are terms, at
none of which a denominator vanishes, that polynomial vanishes, and so does the sum at `s = 0`
when no `p₁ y` vanishes.

## Main statements

* `LMLExplore.sum_div_eq_zero_of_injective`: a sum `∑ y, c y / (p₁ y + s * p₂ y)` that vanishes
  at `card α` distinct points `s` with nonzero denominators vanishes at `s = 0`.
-/

public section

namespace LMLExplore

variable {α K : Type*} [Fintype α] [Field K]

/-- **A rational function with few zeros.** If `s ↦ ∑ y, c y / (p₁ y + s * p₂ y)` vanishes at as
many distinct points `s j` as `α` has elements, at which no denominator `p₁ y + s j * p₂ y`
vanishes, it vanishes at `0` when no `p₁ y` vanishes: multiplied by `∏ y, (p₁ y + s * p₂ y)`, it
is a polynomial of degree less than the number of elements of `α`. -/
lemma sum_div_eq_zero_of_injective {p₁ p₂ c : α → K} (hp₁ : ∀ y, p₁ y ≠ 0) {ι : Type*}
    [Fintype ι] (hι : Fintype.card α ≤ Fintype.card ι) {s : ι → K} (hs : Function.Injective s)
    (hden : ∀ j y, p₁ y + s j * p₂ y ≠ 0) (h : ∀ j, ∑ y, c y / (p₁ y + s j * p₂ y) = 0) :
    ∑ y, c y / p₁ y = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with hα | hα
  · rw [Fintype.card_eq_zero_iff] at hα
    simp
  set N : Polynomial K := ∑ y, Polynomial.C (c y) *
    ∏ y' ∈ Finset.univ.erase y, (Polynomial.C (p₂ y') * Polynomial.X + Polynomial.C (p₁ y'))
  have heval : ∀ t : K, (∀ y, p₁ y + t * p₂ y ≠ 0) →
      (∑ y, c y / (p₁ y + t * p₂ y)) * ∏ y, (p₁ y + t * p₂ y) = N.eval t := by
    intro t ht
    simp only [N, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ y), ← mul_assoc, div_mul_cancel₀ _ (ht y)]
    exact congrArg _ (Finset.prod_congr rfl fun y' _ ↦ by ring)
  have hdeg : N.natDegree < Fintype.card ι := by
    have hle : N.natDegree ≤ Fintype.card α - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun y _ ↦ ?_
      refine (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_prod_le _ _).trans ?_)
      refine (Finset.sum_le_sum fun y' _ ↦ Polynomial.natDegree_linear_le).trans ?_
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ,
        smul_eq_mul, mul_one]
    omega
  have hN : N = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero N hs
    (fun j ↦ by rw [← heval _ (hden j), h j, zero_mul]) hdeg
  have h0 := heval 0 fun y ↦ by simpa using hp₁ y
  rw [hN, Polynomial.eval_zero] at h0
  simp only [zero_mul, add_zero] at h0
  exact (mul_eq_zero.1 h0).resolve_right (Finset.prod_ne_zero_iff.2 fun y _ ↦ hp₁ y)

end LMLExplore
