/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.GetD

/-!
# Counting occurrences with `List.getD`

The number of occurrences of `a` in a list `l` is the number of indices `j < l.length` at which
`l.getD j d = a`, for any default value `d`. Phased elimination
(`LMLExplore.Identification.PhasedElimination`) plays the arm `l.getD j d` of its pull list `l`
at round `j` of a phase, and uses this to count the pulls of an arm in a phase.

## Main statements

* `List.count_eq_sum_range_getD`: `l.count a = ∑ j ∈ range l.length, if l.getD j d = a then 1
  else 0`.
-/

public section

namespace List

variable {α : Type*} [DecidableEq α]

/-- The number of occurrences of `a` in `l` is the number of indices `j < l.length` at which
`l.getD j d = a`. -/
lemma count_eq_sum_range_getD (l : List α) (a d : α) :
    l.count a = ∑ j ∈ Finset.range l.length, if l.getD j d = a then 1 else 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [length_cons, Finset.sum_range_succ', count_cons]
    simp only [getD_cons_succ, getD_cons_zero, ih, beq_iff_eq]

end List
