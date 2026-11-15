/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Inequalities up to `1 / (n + 1)` in Archimedean semifields

In an Archimedean linearly ordered semifield with `ExistsAddOfLE` (for instance, any Archimedean
linearly ordered field), an inequality that holds up to `1 / (n + 1)` for every natural number `n`
holds exactly. This is the sequential form of `le_of_forall_pos_le_add`, for
arguments that index the error by `ℕ`, such as a finite intersection over countably many closed
sets.

## Main statements

* `le_of_forall_nat_le_add_one_div`: if `a ≤ b + 1 / (n + 1)` for every `n : ℕ`, then `a ≤ b`.
-/

public section

variable {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
  [ExistsAddOfLE K] {a b : K}

/-- If `a ≤ b + 1 / (n + 1)` for every natural number `n`, then `a ≤ b`. -/
theorem le_of_forall_nat_le_add_one_div (h : ∀ n : ℕ, a ≤ b + 1 / ((n : K) + 1)) : a ≤ b :=
  le_of_forall_pos_le_add fun _ hε ↦
    let ⟨n, hn⟩ := exists_nat_one_div_lt hε
    (h n).trans ((add_le_add_iff_left b).2 hn.le)
