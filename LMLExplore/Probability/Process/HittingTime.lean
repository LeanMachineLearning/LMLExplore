/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Process.HittingTime

/-!
# Hitting times of a sequence of events

The first time after `n` at which a sequence of events `E i` occurs is the hitting time of `{1}` by
the indicators of the events. It is finite exactly when some event `E i` with `n ≤ i` occurs.

## Main statements

* `MeasureTheory.hittingAfter_indicator_lt_top_iff`: the hitting time of the indicators of a
  sequence of events is finite exactly on the union of the events after the starting time.
-/

public section

namespace MeasureTheory

variable {Ω ι : Type*} [ConditionallyCompleteLinearOrder ι]

/-- The hitting time after `n` of `{1}` by the indicators of a sequence of events `E i` is finite
exactly when some event `E i` with `n ≤ i` occurs. -/
theorem hittingAfter_indicator_lt_top_iff (E : ι → Set Ω) (n : ι) (ω : Ω) :
    hittingAfter (fun i ↦ (E i).indicator fun _ ↦ (1 : ℝ)) {1} n ω < ⊤ ↔
      ∃ i, n ≤ i ∧ ω ∈ E i := by
  rw [lt_top_iff_ne_top, Ne, hittingAfter_eq_top_iff]
  push Not
  refine exists_congr fun i ↦ and_congr_right fun _ ↦ ?_
  by_cases h : ω ∈ E i <;> simp [h]

end MeasureTheory
