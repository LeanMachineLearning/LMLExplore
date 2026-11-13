/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Order.CompleteLattice.Basic

/-!
# Infima over the elements other than one

When the only elements of a type are `a ≠ b`, an infimum over the elements `c ≠ a` is the value at
`b`.

## Main statements

* `iInf_ne_eq_of_forall_eq_or_eq`: if the only elements are `a ≠ b`, then `⨅ c ≠ a, f c = f b`.
-/

public section

variable {ι β : Type*} [CompleteLattice β] {a b : ι}

/-- An infimum over the elements other than `a`, when the only other element is `b`. -/
theorem iInf_ne_eq_of_forall_eq_or_eq (hba : b ≠ a) (h : ∀ c, c = a ∨ c = b) (f : ι → β) :
    ⨅ (c) (_ : c ≠ a), f c = f b :=
  le_antisymm (iInf₂_le b hba) (le_iInf₂ fun c hc ↦ ((h c).resolve_left hc).symm ▸ le_rfl)
