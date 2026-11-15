/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Hitting times of processes indexed by `ℕ`

For a process indexed by `ℕ`, Mathlib's `MeasureTheory.hittingAfter u s n` takes values in
`WithTop ℕ`, and `MeasureTheory.le_hittingAfter` bounds it below by the coercion
`WithTop.some n`. Stopping-time statements about `ℕ`-indexed processes use the cast
`(n : WithTop ℕ)` instead; this file restates the lower bound at that cast.

## Main statements

* `MeasureTheory.natCast_le_hittingAfter`: a hitting time after `n` is at least
  `(n : WithTop ℕ)`.
-/

public section

namespace MeasureTheory

variable {Ω β : Type*} {u : ℕ → Ω → β} {s : Set β} {n : ℕ}

/-- A hitting time after `n` of a process indexed by `ℕ` is at least the cast `(n : WithTop ℕ)`:
Mathlib's `MeasureTheory.le_hittingAfter` at the cast of a natural number. -/
theorem natCast_le_hittingAfter (ω : Ω) : (n : WithTop ℕ) ≤ hittingAfter u s n ω := by
  simpa using le_hittingAfter (u := u) (s := s) (n := n) ω

end MeasureTheory
