/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Semicontinuity.Defs

/-!
# Semicontinuity of one-sided limits of antitone functions

The left limit `Function.leftLim f` of an antitone function `f` is upper semicontinuous, and
it agrees with `f` wherever `f` is continuous. Replacing a p-to-e calibrator by its left limit is
how one shows that admissible calibrators are upper semicontinuous.

## Main statements

* `Antitone.upperSemicontinuous_leftLim`: the left limit of an antitone function is upper
  semicontinuous.
-/

public section

open Filter Function Set
open scoped Topology

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}

/-- The left limit `leftLim f` of an antitone function `f` is upper semicontinuous. -/
theorem Antitone.upperSemicontinuous_leftLim (hf : Antitone f) :
    UpperSemicontinuous (leftLim f) := by
  intro x c hc
  rcases eq_or_neBot (𝓝[<] x) with h | h
  · -- no point to the left of `x` is close to `x`, and to its right `leftLim f ≤ f x`
    filter_upwards [inf_principal_eq_bot.1 h] with z hz
    rcases (not_lt.1 hz).eq_or_lt with rfl | hxz
    · exact hc
    · exact (hf.leftLim_le hxz).trans_lt (leftLim_eq_of_eq_bot f h ▸ hc)
  · -- some `y < x` has `f y < c`, and `leftLim f ≤ f y` to the right of `y`
    obtain ⟨y, hyc, hyx⟩ :=
      ((hf.tendsto_leftLim x).eventually (gt_mem_nhds hc)).and self_mem_nhdsWithin |>.exists
    filter_upwards [Ioi_mem_nhds hyx] with z hz
    exact (hf.leftLim_le hz).trans_lt hyc
