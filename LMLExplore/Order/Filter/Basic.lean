/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Order.Filter.Basic

/-!
# The eventual order along the principal filter of a range

Along the principal filter of the range of a map `φ`, the eventual order of two functions is the
order of their compositions with `φ`, everywhere.

## Main statements

* `Filter.eventuallyLE_principal_range_iff`: `G ≤ᶠ[𝓟 (range φ)] H ↔ ∀ x, G (φ x) ≤ H (φ x)`.
-/

public section

open Set

namespace Filter

variable {α β γ : Type*} {φ : γ → α} {G H : α → β}

/-- Along the principal filter of the range of `φ`, the eventual order of two functions is the
order of their compositions with `φ`. -/
theorem eventuallyLE_principal_range_iff [LE β] :
    G ≤ᶠ[𝓟 (range φ)] H ↔ ∀ x, G (φ x) ≤ H (φ x) := by
  simp only [EventuallyLE, eventually_principal, forall_mem_range]

end Filter
