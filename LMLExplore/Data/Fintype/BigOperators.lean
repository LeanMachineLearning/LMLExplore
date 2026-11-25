/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Counting functions with a coordinatewise condition, and products over a numbering

The functions `f : ∀ i, α i` with `Q i (f i)` for every `i` form the box
`Fintype.piFinset fun i ↦ {a | Q i a}`, so there are `∏ i, #{a | Q i a}` of them. The lower
bound for e-BH on running maxima
(`LMLExplore.EValues.Examples.MultipleTesting.RunningMaxima.LowerBound`) counts the height vectors
in a fiber of its information this way.

For a numbering `e : α ≃ Fin n` of a finite type, a product over `α` of a function of the numbers
is the product over `{0, …, n - 1}`. The bandits whose means are in arithmetic progression along a
numbering of the arms, as in the lower bounds of [D23, Theorem 8] and [CL16, Theorem 1], compute
their complexities this way.

## Main statements

* `Fintype.card_filter_forall`: the number of functions satisfying a coordinatewise condition is
  the product of the numbers of values satisfying it at each coordinate.
* `Equiv.prod_numbering_eq_prod_range`, `Equiv.sum_numbering_eq_sum_range`:
  `∏_b f (e b) = ∏_{i < n} f i` and `∑_b f (e b) = ∑_{i < n} f i` for a numbering `e : α ≃ Fin n`.

## Implementation notes

The statement of `Fintype.card_filter_forall` and its proof are adapted from the helper
`card_filter_forall` of `EValuesResearch/Results/RunningMaxima.lean` (commit `ffba78a`) in the paper
project `RemyDegenne/evalues_research`, stated there for functions `Fin (n + 1) → Fin (n + 1)`.

## References

* [D23] R. Degenne, *On the existence of a complexity in fixed budget bandit identification*,
  COLT 2023, arXiv:2303.09468v2.
* [CL16] A. Carpentier and A. Locatelli, *Tight (lower) bounds for the fixed budget best arm
  identification bandit problem*, COLT 2016.
-/

public section

namespace Fintype

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The number of functions `f : ∀ i, α i` with `Q i (f i)` for every `i` is the product over `i`
of the number of values `a : α i` with `Q i a`. -/
theorem card_filter_forall (Q : ∀ i, α i → Prop)
    [∀ i, DecidablePred (Q i)] [DecidablePred fun f : ∀ i, α i ↦ ∀ i, Q i (f i)] :
    (Finset.univ.filter fun f : ∀ i, α i ↦ ∀ i, Q i (f i)).card =
      ∏ i, (Finset.univ.filter (Q i)).card := by
  rw [← card_piFinset]
  congr 1
  ext f
  simp [mem_piFinset]

end Fintype

namespace Equiv

variable {α : Type*} [Fintype α] {n : ℕ}

/-- For a numbering `e` of `α`, the product over `α` of `f (e b)` is the product of `f i` over
`i < n`. -/
@[to_additive /-- For a numbering `e` of `α`, the sum over `α` of `f (e b)` is the sum of `f i`
over `i < n`. -/]
theorem prod_numbering_eq_prod_range {M : Type*} [CommMonoid M] (e : α ≃ Fin n)
    (f : ℕ → M) : ∏ b, f (e b) = ∏ i ∈ Finset.range n, f i :=
  (e.prod_comp fun i ↦ f i).trans (Fin.prod_univ_eq_prod_range f n)

end Equiv
