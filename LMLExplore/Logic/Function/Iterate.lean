/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Logic.Function.Iterate

/-!
# Iterates indexed backwards from a horizon

Backward induction over a horizon `m` uses the iterates `f^[m - n] x` at the rounds `n ≤ m`, which
are related from one round to the previous one by an application of `f`.

## Main statements

* `Function.iterate_sub_eq_apply`: for `n < m`, `f^[m - n] x = f (f^[m - (n + 1)] x)`.
-/

public section

namespace Function

/-- For `n < m`, the iterate of `f` at the backward index `m - n` is `f` applied to the iterate at
the backward index `m - (n + 1)` of the next round. -/
theorem iterate_sub_eq_apply {α : Type*} (f : α → α) (x : α) {m n : ℕ} (h : n < m) :
    f^[m - n] x = f (f^[m - (n + 1)] x) := by
  rw [show m - n = m - (n + 1) + 1 by omega, iterate_succ_apply']

end Function
