/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Indicator

/-!
# Indicators of the level sets of a natural-valued function and products

On the event `{T = t}` of a function `T : Ω → ℕ`, a family `G t` indexed by the value `t` agrees
with the function `ω ↦ G (T ω) ω`, so it can be moved inside the indicator of that event.

## Main statements

* `Set.indicator_setOf_eq_mul_apply`: `𝟙{T = t} f * G t = 𝟙{T = t} (f * G T)`.
-/

public section

namespace Set

/-- On the event `{T = t}`, a function `G t` of the time `t` is the function `G (T ·)` of the
random time: `𝟙{T = t} f * G t = 𝟙{T = t} (f * G T)`. -/
lemma indicator_setOf_eq_mul_apply {Ω M : Type*} [MulZeroClass M] (T : Ω → ℕ) (t : ℕ)
    (f : Ω → M) (G : ℕ → Ω → M) (ω : Ω) :
    {ω | T ω = t}.indicator f ω * G t ω =
      {ω | T ω = t}.indicator (fun ω' ↦ f ω' * G (T ω') ω') ω := by
  by_cases h : T ω = t
  · rw [indicator_of_mem (s := {x | T x = t}) h, indicator_of_mem (s := {x | T x = t}) h, h]
  · rw [indicator_of_notMem (s := {x | T x = t}) h, indicator_of_notMem (s := {x | T x = t}) h,
      zero_mul]

end Set
