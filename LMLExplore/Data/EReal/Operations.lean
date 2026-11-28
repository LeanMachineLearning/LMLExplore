/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Data.EReal.Operations

/-!
# Operations with real constants in `EReal`

Tau Ceti's `EReal.iSup_sub_coe` lets a real constant subtracted from every term of a family in
`EReal` be pulled out of the supremum. This file records the same statement for addition, which
conjugates of translated functions use, and the passage from a nonnegative extended real `d`
with `c d < x`, for a real `c > 0`, to the real number `d.toReal`.

## Main statements

* `EReal.iSup_add_coe`: `⨆ i, (g i + c) = (⨆ i, g i) + c` for a real `c`.
* `EReal.coe_toReal_eq_and_mul_toReal_lt_of_coe_mul_lt`: if `0 ≤ d` and `c d < x` with a real
  `c > 0` and a real `x`, then `d` is the real `d.toReal ≥ 0`, and `c d.toReal < x`.
-/

public section

namespace EReal

/-- Adding a real constant commutes with a supremum in `EReal`; both sides are `⊥` when the index
type is empty. -/
theorem iSup_add_coe {ι : Sort*} (g : ι → EReal) (c : ℝ) :
    ⨆ i, (g i + (c : EReal)) = (⨆ i, g i) + (c : EReal) := by
  simpa [sub_eq_add_neg] using iSup_sub_coe g (-c)

/-- An extended real `d ≥ 0` with `c d < x`, for reals `c > 0` and `x`, is the real
`d.toReal ≥ 0`, and `c d.toReal < x`. -/
theorem coe_toReal_eq_and_mul_toReal_lt_of_coe_mul_lt {c x : ℝ} {d : EReal} (hc : 0 < c)
    (hd : 0 ≤ d) (h : (c : EReal) * d < x) :
    (d.toReal : EReal) = d ∧ 0 ≤ d.toReal ∧ c * d.toReal < x := by
  have hdr : (d.toReal : EReal) = d :=
    coe_toReal (ne_top_of_coe_mul_ne_top hc (ne_top_of_lt h)) (ne_bot_of_le_ne_bot zero_ne_bot hd)
  refine ⟨hdr, toReal_nonneg hd, ?_⟩
  rw [← hdr, ← coe_mul] at h
  exact_mod_cast h

end EReal
