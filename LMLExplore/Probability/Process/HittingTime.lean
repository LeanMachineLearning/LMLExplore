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

More generally, the hitting time after `n` at `ω` of a set `s` by a process `u` depends only on the
sequence of events `u i ω ∈ s`, `i ≥ n`.

## Main statements

* `MeasureTheory.hittingAfter_indicator_lt_top_iff`: the hitting time of the indicators of a
  sequence of events is finite exactly on the union of the events after the starting time.
* `MeasureTheory.hittingAfter_apply_congr`: two hitting times agree at `ω` when the two processes
  lie in their sets at the same times.
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

/-- The hitting time after `n` at `ω` depends only on the times `i ≥ n` at which the process lies
in the set: if `u i ω ∈ s ↔ u' i ω ∈ s'` for all `i ≥ n`, the hitting times are equal. -/
theorem hittingAfter_apply_congr [WellFoundedLT ι] {β β' : Type*} {u : ι → Ω → β}
    {u' : ι → Ω → β'} {s : Set β} {s' : Set β'} {n : ι} {ω : Ω}
    (h : ∀ i, n ≤ i → (u i ω ∈ s ↔ u' i ω ∈ s')) :
    hittingAfter u s n ω = hittingAfter u' s' n ω := by
  -- a hitting time is determined by the times `k` it is at most, through `hittingAfter_le_iff`
  refine eq_of_forall_ge_iff fun k ↦ ?_
  induction k using WithTop.recTopCoe with
  | top => simp
  | coe k =>
    rw [hittingAfter_le_iff, hittingAfter_le_iff]
    exact exists_congr fun i ↦ and_congr_right fun hi ↦ h i hi.1

end MeasureTheory
