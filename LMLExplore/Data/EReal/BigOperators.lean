/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.EReal.BigOperators
import Mathlib.Algebra.BigOperators.WithTop

/-!
# Finite sums in `EReal` that are not `⊥`

A finite sum in `EReal` is `⊥` exactly when one of its terms is, since `⊥ + x = ⊥` for every `x`
and a sum of terms above `⊥` stays above `⊥`. This is Mathlib's
`WithBot.sum_eq_bot_iff` and `WithBot.sum_lt_bot` for `EReal = WithBot (WithTop ℝ)`, recorded
with the `⊥` of `EReal` so that it applies to sums of extended integrals.

## Main statements

* `EReal.sum_ne_bot`: `∑ i ∈ s, f i ≠ ⊥ ↔ ∀ i ∈ s, f i ≠ ⊥`.
-/

public section

namespace EReal

variable {ι : Type*} {s : Finset ι} {f : ι → EReal}

/-- A finite sum in `EReal` is not `⊥` exactly when none of its terms is: `EReal` is
`WithBot (WithTop ℝ)`, and this is `WithBot.sum_eq_bot_iff` and `WithBot.sum_lt_bot`. -/
lemma sum_ne_bot : ∑ i ∈ s, f i ≠ ⊥ ↔ ∀ i ∈ s, f i ≠ ⊥ :=
  ⟨fun h i hi hb ↦ h (WithBot.sum_eq_bot_iff.2 ⟨i, hi, hb⟩), fun h ↦ (WithBot.sum_lt_bot h).ne'⟩

end EReal
