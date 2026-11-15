/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# A superlevel set of positive measure

If a real function exceeds `a` on a set of positive measure, then it is at least some `c > a` on a
set of positive measure: the set `{a < f}` is the countable union of the sets
`{a + 1 / (n + 1) ≤ f}`.

## Main statements

* `MeasureTheory.exists_gt_measure_setOf_le_ne_zero`: if `μ {a < f} ≠ 0`, then
  `μ {c ≤ f} ≠ 0` for some `c > a`.
-/

public section

open Set

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If a real function exceeds `a` on a set of positive measure, then it is at least some `c > a`
on a set of positive measure. The function need not be measurable. -/
theorem exists_gt_measure_setOf_le_ne_zero {f : α → ℝ} {a : ℝ} (h : μ {x | a < f x} ≠ 0) :
    ∃ c, a < c ∧ μ {x | c ≤ f x} ≠ 0 := by
  by_contra! h'
  refine h ?_
  have : {x | a < f x} = ⋃ n : ℕ, {x | a + 1 / ((n : ℝ) + 1) ≤ f x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [this]
  exact measure_iUnion_null fun n ↦ h' _ (lt_add_of_pos_right a (by positivity))

end MeasureTheory
