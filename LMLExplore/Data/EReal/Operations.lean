/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Data.EReal.Operations

/-!
# Adding a real constant to a supremum in `EReal`

Tau Ceti's `EReal.iSup_sub_coe` lets a real constant subtracted from every term of a family in
`EReal` be pulled out of the supremum. This file records the same statement for addition, which
conjugates of translated functions use.

## Main statements

* `EReal.iSup_add_coe`: `⨆ i, (g i + c) = (⨆ i, g i) + c` for a real `c`.
-/

public section

namespace EReal

/-- Adding a real constant commutes with a supremum in `EReal`; both sides are `⊥` when the index
type is empty. -/
theorem iSup_add_coe {ι : Sort*} (g : ι → EReal) (c : ℝ) :
    ⨆ i, (g i + (c : EReal)) = (⨆ i, g i) + (c : EReal) := by
  simpa [sub_eq_add_neg] using iSup_sub_coe g (-c)

end EReal
