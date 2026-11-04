/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-!
# Products `∏ (1 + f i)` of factors with vanishing pairwise products

Expanding `∏ i ∈ s, (1 + f i)` gives the sum over the subsets `t ⊆ s` of `∏ i ∈ t, f i`
(`Finset.prod_one_add`). When `f i * f j = 0` for all distinct `i, j ∈ s`, the products over
subsets with at least two elements vanish and the expansion reduces to `1 + ∑ i ∈ s, f i`. For
real numbers, this is the case when at most one of the `f i` is nonzero. It is the algebraic step
behind the concentration of negatively correlated nonnegative variables, such as the indicators
`𝟙{A = i}` of the value of a random variable `A`.

## Main statements

* `Finset.prod_one_add_of_mul_eq_zero`: `∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i` when the products
  `f i * f j` of distinct `i, j ∈ s` vanish.
-/

public section

namespace Finset

variable {ι R : Type*} [CommSemiring R] {f : ι → R}

/-- If the products `f i * f j` of distinct `i, j ∈ s` vanish, then
`∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i`. -/
theorem prod_one_add_of_mul_eq_zero {s : Finset ι}
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    ∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj,
      ih fun i hi k hk hik ↦ hf i (mem_insert_of_mem hi) k (mem_insert_of_mem hk) hik]
    have hzero : f j * ∑ i ∈ s, f i = 0 := by
      rw [mul_sum]
      exact sum_eq_zero fun i hi ↦
        hf j (mem_insert_self j s) i (mem_insert_of_mem hi) fun h ↦ hj (h ▸ hi)
    calc (1 + f j) * (1 + ∑ i ∈ s, f i) = 1 + (f j + ∑ i ∈ s, f i) + f j * ∑ i ∈ s, f i := by ring
      _ = 1 + (f j + ∑ i ∈ s, f i) := by rw [hzero, add_zero]

end Finset
