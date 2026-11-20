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
sequence of events `u i ω ∈ s`, `i ≥ n`: it is finite exactly when one of these events occurs, and
it is `t` when they occur exactly at the times `i ≥ t`. Every random time `τ` is thus the first
time at which the events `{τ ≤ i}` occur.

Stopping at the first of the events `A 0, …, A N` that occurs shows that the probability that
some event of an adapted sequence occurs is the supremum, over the stopping times `τ`, of the
probability of the event `A τ` read at `τ` [RRLK, Lemma 2]. A bound on the probability of the
event read at every stopping time is therefore a bound uniform in time. Since that probability
does not depend on the filtration, a bound on the events of a sequence adapted to a filtration `𝒢`,
read at the stopping times of `𝒢`, holds at the stopping times of every finer filtration: the
lifting lemma of [CR26, Lemma 1].

## Main statements

* `MeasureTheory.hittingAfter_lt_top_iff`: a hitting time is finite exactly when the process
  lies in the set at some time after the starting time.
* `MeasureTheory.hittingAfter_indicator_lt_top_iff`: the hitting time of the indicators of a
  sequence of events is finite exactly on the union of the events after the starting time.
* `MeasureTheory.hittingAfter_apply_eq_of_forall_mem_iff`: a process that lies in the set exactly
  from a time `t` on hits it at `t`.
* `MeasureTheory.hittingAfter_indicator_setOf_le_apply`: a random time `τ` is the first time at
  which the indicators of the events `{τ ≤ i}` equal `1`.
* `MeasureTheory.hittingAfter_apply_congr`: two hitting times agree at `ω` when the two processes
  lie in their sets at the same times.
* `MeasureTheory.measure_iUnion_eq_iSup_isStoppingTime`: the measure of the union of an adapted
  sequence of events is the supremum of the measures of the events read at the stopping times with
  values in `ℕ` [RRLK, Lemma 2].
* `MeasureTheory.forall_isStoppingTime_measure_le_iff_of_le`: the lifting lemma [CR26, Lemma 1].

## References

* [CR26] Y. J. Choe and A. Ramdas, *Combining evidence across filtrations*, arXiv:2402.09698v5,
  Lemma 1.

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, Lemma 2.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} [ConditionallyCompleteLinearOrder ι]

/-- The hitting time after `n` of a set `s` by a process `u` is finite exactly when the process
lies in `s` at some time `i ≥ n`. -/
theorem hittingAfter_lt_top_iff {β : Type*} {u : ι → Ω → β} {s : Set β} {n : ι} {ω : Ω} :
    hittingAfter u s n ω < ⊤ ↔ ∃ i, n ≤ i ∧ u i ω ∈ s := by
  simp [lt_top_iff_ne_top, hittingAfter_eq_top_iff]

/-- The hitting time after `n` of `{1}` by the indicators of a sequence of events `E i` is finite
exactly when some event `E i` with `n ≤ i` occurs. -/
theorem hittingAfter_indicator_lt_top_iff (E : ι → Set Ω) (n : ι) (ω : Ω) :
    hittingAfter (fun i ↦ (E i).indicator fun _ ↦ (1 : ℝ)) {1} n ω < ⊤ ↔
      ∃ i, n ≤ i ∧ ω ∈ E i := by
  rw [hittingAfter_lt_top_iff]
  refine exists_congr fun i ↦ and_congr_right fun _ ↦ ?_
  by_cases h : ω ∈ E i <;> simp [h]

/-- If, from time `n` on, a process lies in `s` at `ω` exactly at the times `i ≥ t`, for some
`t ≥ n` in `WithTop ι`, then its hitting time of `s` after `n` at `ω` is `t`. With `t = ⊤`, the
process never lies in `s` after `n`. -/
theorem hittingAfter_apply_eq_of_forall_mem_iff [WellFoundedLT ι] {β : Type*} {u : ι → Ω → β}
    {s : Set β} {n : ι} {ω : Ω} {t : WithTop ι} (hnt : (n : WithTop ι) ≤ t)
    (h : ∀ i, n ≤ i → (u i ω ∈ s ↔ t ≤ i)) :
    hittingAfter u s n ω = t := by
  -- both sides are determined by the times `k` they are at most
  refine eq_of_forall_ge_iff fun k ↦ ?_
  induction k using WithTop.recTopCoe with
  | top => simp
  | coe k =>
    rw [hittingAfter_le_iff]
    refine ⟨fun ⟨j, hj, hjs⟩ ↦ ((h j hj.1).1 hjs).trans (mod_cast hj.2), fun htk ↦ ?_⟩
    have hnk : n ≤ k := WithTop.coe_le_coe.1 (hnt.trans htk)
    exact ⟨k, ⟨hnk, le_rfl⟩, (h k hnk).2 htk⟩

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

/-- **A random time is the first time it has passed.** For `τ : Ω → WithTop ι` with `n ≤ τ ω`, the
first time after `n` at which the indicator of the event `{τ ≤ i}` equals `1` is `τ ω`. -/
theorem hittingAfter_indicator_setOf_le_apply [WellFoundedLT ι] {β : Type*} [Zero β] [One β]
    [NeZero (1 : β)] {τ : Ω → WithTop ι} {n : ι} {ω : Ω} (hτ : (n : WithTop ι) ≤ τ ω) :
    hittingAfter (fun i : ι ↦ {ω | τ ω ≤ i}.indicator (1 : Ω → β)) {1} n ω = τ ω := by
  refine hittingAfter_apply_eq_of_forall_mem_iff hτ fun i _ ↦ ?_
  by_cases h : τ ω ≤ i <;> simp [h]

/-- **The events of an adapted sequence read at stopping times**, the form of [RRLK, Lemma 2] for
one measure and the stopping times with values in `ℕ`. For a sequence of events `A n` adapted to a
filtration indexed by `ℕ`, the measure of the event that some `A n` occurs is the supremum, over
the stopping times `τ` with values in `ℕ`, of the measure of the event `A (τ ω)` read at `τ`. The
measure need not be finite and the events need not be nested. -/
theorem measure_iUnion_eq_iSup_isStoppingTime {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ mΩ} {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet[ℱ n] (A n)) :
    μ (⋃ n, A n) = ⨆ (τ : Ω → ℕ) (_ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ))),
      μ {ω | ω ∈ A (τ ω)} := by
  refine le_antisymm ?_ (iSup₂_le fun τ _ ↦ measure_mono fun ω hω ↦ Set.mem_iUnion.2 ⟨τ ω, hω⟩)
  -- by continuity from below, it suffices to bound the probability that one of `A 0, …, A N`
  -- occurs, and the first of them that occurs, or `N`, is a stopping time
  rw [measure_iUnion_eq_iSup_accumulate]
  refine iSup_le fun N ↦ ?_
  set u : ℕ → Ω → ℝ := fun n ↦ (A n).indicator fun _ ↦ 1
  have hu : Adapted ℱ u := fun n ↦ measurable_const.indicator (hA n)
  refine le_iSup₂_of_le (fun ω ↦ hittingBtwn u {1} 0 N ω)
    (hu.isStoppingTime_hittingBtwn (measurableSet_singleton 1)) (measure_mono fun ω hω ↦ ?_)
  obtain ⟨k, hk, hωk⟩ := Set.mem_accumulate.1 hω
  have h := hittingBtwn_mem_set (u := u) (s := {1}) (n := 0) (m := N) (ω := ω)
    ⟨k, ⟨zero_le, hk⟩, by simp [u, hωk]⟩
  simpa [u] using h

/-- **The lifting lemma** [CR26, Lemma 1]. For filtrations `𝒢 ≤ ℱ` and a sequence of events `A n`
adapted to the coarser filtration `𝒢`, a bound on the measure of the event `A (τ ω)` read at every
stopping time `τ` of `𝒢` with values in `ℕ` holds at every stopping time of `ℱ`: both say that the
measure of the union of the events is at most the bound. -/
theorem forall_isStoppingTime_measure_le_iff_of_le {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 ℱ : Filtration ℕ mΩ} (h𝒢ℱ : 𝒢 ≤ ℱ) {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet[𝒢 n] (A n))
    (c : ℝ≥0∞) :
    (∀ τ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω ↦ (τ ω : WithTop ℕ)) → μ {ω | ω ∈ A (τ ω)} ≤ c) ↔
      ∀ τ : Ω → ℕ, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) → μ {ω | ω ∈ A (τ ω)} ≤ c := by
  simp_rw [← iSup₂_le_iff, ← measure_iUnion_eq_iSup_isStoppingTime hA,
    ← measure_iUnion_eq_iSup_isStoppingTime fun n ↦ h𝒢ℱ n _ (hA n)]

end MeasureTheory
