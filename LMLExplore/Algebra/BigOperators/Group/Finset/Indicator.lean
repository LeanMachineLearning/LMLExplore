/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Notation.Indicator

/-!
# Sums of indicators of the level sets of a natural-valued function

For a function `T : Ω → ℕ`, the events `{T = t}`, `t ≤ N`, partition the event `{T ≤ N}`, so the
sum of the indicators of a function `f` on these events is its indicator on `{T ≤ N}`.

## Main statements

* `Finset.sum_range_indicator_setOf_eq`: `∑ t ∈ range (N + 1), 𝟙{T = t} f = 𝟙{T ≤ N} f`.
-/

public section

namespace Finset

/-- Summing the indicators of the events `{T = t}`, `t ≤ N`, gives the indicator of `{T ≤ N}`. -/
lemma sum_range_indicator_setOf_eq {Ω M : Type*} [AddCommMonoid M] (T : Ω → ℕ) (f : Ω → M)
    (N : ℕ) (ω : Ω) :
    ∑ t ∈ range (N + 1), {ω | T ω = t}.indicator f ω = {ω | T ω ≤ N}.indicator f ω := by
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, sum_ite_eq, mem_range, Nat.lt_succ_iff]

end Finset
