/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Counting functions with a coordinatewise condition

The functions `f : ∀ i, α i` with `Q i (f i)` for every `i` form the box
`Fintype.piFinset fun i ↦ {a | Q i a}`, so there are `∏ i, #{a | Q i a}` of them. The lower
bound for e-BH on running maxima (`LMLExplore.EValues.MultipleTesting.RunningMaxima.LowerBound`)
counts the height vectors in a fiber of its information this way.

## Main statements

* `Fintype.card_filter_forall`: the number of functions satisfying a coordinatewise condition is
  the product of the numbers of values satisfying it at each coordinate.

## Implementation notes

The statement and its proof are adapted from the helper `card_filter_forall` of
`EValuesResearch/Results/RunningMaxima.lean` (commit `ffba78a`) in the paper project
`RemyDegenne/evalues_research`, stated there for functions `Fin (n + 1) → Fin (n + 1)`.
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
