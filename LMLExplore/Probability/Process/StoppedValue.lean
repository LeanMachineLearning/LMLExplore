/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Probability.Process.Stopping
public import TauCeti.Probability.Process.StoppedValue
import LMLExplore.Data.ENat.Basic

/-!
# The value of a process, and an event, at a possibly infinite time

A random time of a filtration indexed by `ℕ` takes values in `WithTop ℕ`. Mathlib's
`MeasureTheory.stoppedValue u τ` reads the process at `τ ω` where it is finite and takes an
arbitrary value where `τ ω = ⊤`. Anytime-valid inference needs a canonical value at infinity: the
value of a process at a possibly infinite stopping time is `u (τ ω) ω` where `τ ω` is finite and
`limsup (u · ω)` where it is infinite [RRLK; RLKR23, (1.2)]. For nonnegative supermartingales with
finite initial expectation, which converge almost surely, this is the almost sure limit, and
optional stopping holds at every stopping time with this convention.

Over all random times, not necessarily stopping times, the largest expectation of an
`ℝ≥0∞`-valued process read at that time is the expectation of its supremum over time
[RRLK, Lemma 3].

In the same way, a sequence of events `A n` is read at a random time `τ` as the event `A (τ ω)`
where `τ ω` is finite, and as the event `limsup A atTop`, that infinitely many of the events
occur, where it is infinite [RRLK, Lemma 2]. This event is contained in the union of the events.

## Main definitions

* `MeasureTheory.stoppedValueLimsup u τ`: the value of `u` at the random time `τ`, with
  `limsup (u · ω)` where `τ ω = ⊤`.
* `MeasureTheory.stoppedEvent A τ`: the events `A n` read at the random time `τ`, with
  `limsup A atTop` where `τ ω = ⊤`.

## Main statements

* `MeasureTheory.stoppedValueLimsup_of_eq_natCast`, `MeasureTheory.stoppedValueLimsup_of_eq_top`:
  its values at finite and infinite times.
* `MeasureTheory.stoppedValue_of_eq_natCast`, `MeasureTheory.stoppedValue_natCast`,
  `MeasureTheory.stoppedValue_add_one`: Mathlib's `stoppedValue` where the random time is finite,
  at the cast of a random time with values in `ℕ`, and the value of a shifted process at a random
  time that is finite everywhere.
* `MeasureTheory.stoppedValue_congr`: the value of a process at a random time at `ω` depends only
  on the time at `ω`.
* `MeasureTheory.stoppedValueLimsup_of_forall_ne_top`: at a random time that is finite
  everywhere it is Mathlib's `stoppedValue`.
* `MeasureTheory.stoppedValueLimsup_eq_stoppedValue`: where `τ` is finite it agrees with Mathlib's
  `stoppedValue`.
* `MeasureTheory.stoppedValueLimsup_mono`: it is monotone in the process.
* `MeasureTheory.stoppedValueLimsup_le_iSup`: it is at most the supremum of the process over time.
* `MeasureTheory.tendsto_stoppedValueLimsup_min`: for a convergent process, the values at the
  truncated times `min τ N` converge to the value at `τ`.
* `MeasureTheory.liminf_stoppedValue_min`: the `liminf` of the values at the truncated times
  `min τ N` is the value at `τ`, with the `liminf` of the process where `τ` is infinite.
* `MeasureTheory.measurable_stoppedValueLimsup`: it is measurable for measurable `u n` and `τ`.
* `MeasureTheory.lintegral_stoppedValueLimsup_le_sum`: at a random time bounded by `N`, the
  integral of an `ℝ≥0∞`-valued process is at most the sum of its integrals at the times up to `N`.
* `MeasureTheory.tendsto_lintegral_stoppedValueLimsup_min`: for an almost everywhere nondecreasing
  `ℝ≥0∞`-valued process, the integrals at the truncated times `min τ N` converge to the integral
  at `τ`.
* `MeasureTheory.tendsto_setLIntegral_inter_le_natCast`: the integrals of a function over
  `s ∩ {τ ≤ N}` increase to its integral over `s ∩ {τ ≠ ⊤}`.
* `MeasureTheory.measurable_apply_of_countable`: the value `fun ω ↦ u (σ ω) ω` of a process of
  measurable functions, indexed by a countable type, at a measurable random time is measurable.
* `MeasureTheory.iSup_lintegral_apply_eq_lintegral_iSup`,
  `MeasureTheory.iSup_lintegral_stoppedValueLimsup_eq_lintegral_iSup`: the supremum, over the
  random times with values in `ℕ`, and in `WithTop ℕ`, of the integral of an `ℝ≥0∞`-valued process
  read at that time is the integral of its supremum over time [RRLK, Lemma 3].
* `MeasureTheory.mem_stoppedEvent_of_eq_natCast`, `MeasureTheory.mem_stoppedEvent_of_eq_top`:
  the event read at a finite and at an infinite time, and
  `MeasureTheory.stoppedEvent_of_forall_ne_top`: at a random time that is finite everywhere.
* `MeasureTheory.stoppedEvent_mono`, `MeasureTheory.stoppedEvent_subset_iUnion`: the event read at
  a random time is monotone in the events, and contained in their union.
* `MeasureTheory.measurableSet_stoppedEvent`: it is measurable for measurable events and a
  measurable random time.

## References

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, Lemmas 2 and 3.
* [RLKR23] J. Ruf, M. Larsson, W. M. Koolen and A. Ramdas, *A composite generalization of Ville's
  martingale theorem using e-processes*, Electron. J. Probab. 28 (2023), arXiv:2203.04485.
-/

public section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {Ω β : Type*} {τ : Ω → WithTop ℕ} {ω : Ω}

/-- Where the random time is finite, Mathlib's `stoppedValue` reads the process at that time.
This is Tau Ceti's `stoppedValue_of_eq` with the cast `(n : WithTop ℕ)`, the simp normal form of a
finite time in `WithTop ℕ`, in place of the coercion `WithTop.some n`. -/
theorem stoppedValue_of_eq_natCast {u : ℕ → Ω → β} {n : ℕ} (h : τ ω = n) :
    stoppedValue u τ ω = u n ω :=
  stoppedValue_of_eq h

/-- The value of a process at a random time at `ω` depends only on the time at `ω`. -/
theorem stoppedValue_congr {ι : Type*} [Nonempty ι] {u : ι → Ω → β} {σ σ' : Ω → WithTop ι}
    (h : σ ω = σ' ω) : stoppedValue u σ ω = stoppedValue u σ' ω := by
  rw [stoppedValue, stoppedValue, h]

/-- At the cast of a random time with values in `ℕ`, `stoppedValue` reads the process at that
time. -/
@[simp]
theorem stoppedValue_natCast (u : ℕ → Ω → β) (τ : Ω → ℕ) :
    stoppedValue u (fun ω ↦ (τ ω : WithTop ℕ)) = fun ω ↦ u (τ ω) ω :=
  funext fun _ ↦ stoppedValue_of_eq_natCast rfl

/-- At a random time that is finite everywhere, the shift `fun n ↦ u (n + 1)` read at `τ` is `u`
read at `τ + 1`. -/
theorem stoppedValue_add_one (u : ℕ → Ω → β) (h : ∀ ω, τ ω ≠ ⊤) :
    stoppedValue (fun n ↦ u (n + 1)) τ = stoppedValue u (fun ω ↦ τ ω + 1) := by
  obtain ⟨τ, rfl⟩ := WithTop.exists_eq_natCast_of_forall_ne_top h
  simp only [← Nat.cast_add_one, stoppedValue_natCast]

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β] {u : ℕ → Ω → β}

/-- The value of the process `u` at the random time `τ : Ω → WithTop ℕ`: `u n ω` where
`τ ω = n`, and `limsup (u · ω)` where `τ ω = ⊤` [RRLK; RLKR23, (1.2)]. Unlike Mathlib's
`stoppedValue`, its value at infinity is meaningful: for an almost surely convergent process it is
the limit. -/
noncomputable def stoppedValueLimsup (u : ℕ → Ω → β) (τ : Ω → WithTop ℕ) (ω : Ω) : β :=
  if τ ω = ⊤ then limsup (fun n ↦ u n ω) atTop else u (τ ω).untopA ω

/-- Where the random time is finite, `stoppedValueLimsup` reads the process at that time. -/
theorem stoppedValueLimsup_of_eq_natCast {n : ℕ} (h : τ ω = n) :
    stoppedValueLimsup u τ ω = u n ω := by
  simp only [stoppedValueLimsup, h, WithTop.natCast_ne_top, ↓reduceIte, WithTop.untopA_natCast]

/-- Where the random time is infinite, `stoppedValueLimsup` is the `limsup` of the process. -/
theorem stoppedValueLimsup_of_eq_top (h : τ ω = ⊤) :
    stoppedValueLimsup u τ ω = limsup (fun n ↦ u n ω) atTop := by
  simp [stoppedValueLimsup, h]

/-- The value of a process at a random time at `ω` depends only on the time at `ω`. -/
theorem stoppedValueLimsup_congr {τ' : Ω → WithTop ℕ} (h : τ ω = τ' ω) :
    stoppedValueLimsup u τ ω = stoppedValueLimsup u τ' ω := by
  simp only [stoppedValueLimsup, h]

/-- At a random time that is finite everywhere, `stoppedValueLimsup` is Mathlib's
`stoppedValue`. -/
theorem stoppedValueLimsup_of_forall_ne_top (u : ℕ → Ω → β) (h : ∀ ω, τ ω ≠ ⊤) :
    stoppedValueLimsup u τ = stoppedValue u τ := by
  funext ω
  simp [stoppedValueLimsup, stoppedValue, h ω]

/-- At a constant finite time, `stoppedValueLimsup` is the process at that time. -/
theorem stoppedValueLimsup_const (u : ℕ → Ω → β) (n : ℕ) :
    stoppedValueLimsup u (fun _ ↦ (n : WithTop ℕ)) = u n :=
  funext fun _ ↦ stoppedValueLimsup_of_eq_natCast rfl

/-- At the constant time `⊤`, `stoppedValueLimsup` is the `limsup` of the process. -/
@[simp]
theorem stoppedValueLimsup_top (u : ℕ → Ω → β) :
    stoppedValueLimsup u (fun _ ↦ ⊤) = fun ω ↦ limsup (fun n ↦ u n ω) atTop :=
  funext fun _ ↦ stoppedValueLimsup_of_eq_top rfl

/-- Where the random time is finite, `stoppedValueLimsup` agrees with Mathlib's `stoppedValue`. -/
theorem stoppedValueLimsup_eq_stoppedValue (h : τ ω ≠ ⊤) :
    stoppedValueLimsup u τ ω = stoppedValue u τ ω := by
  simp [stoppedValueLimsup, stoppedValue, h]

/-- For a process that converges at `ω` (to its `limsup`), the values at the truncated times
`min τ N` converge to the value at `τ`. -/
theorem tendsto_stoppedValueLimsup_min [TopologicalSpace β]
    (h : Tendsto (fun n ↦ u n ω) atTop (𝓝 (limsup (fun n ↦ u n ω) atTop))) :
    Tendsto (fun N : ℕ ↦ stoppedValueLimsup u (fun ω ↦ min (τ ω) N) ω) atTop
      (𝓝 (stoppedValueLimsup u τ ω)) := by
  induction hτω : τ ω using WithTop.recTopCoe with
  | top =>
    rw [stoppedValueLimsup_of_eq_top hτω]
    exact h.congr fun N ↦ (stoppedValueLimsup_of_eq_natCast (by simp [hτω])).symm
  | coe b =>
    rw [← Nat.cast_withTop] at hτω
    rw [stoppedValueLimsup_of_eq_natCast hτω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    refine (stoppedValueLimsup_of_eq_natCast ?_).symm
    rw [hτω, min_eq_left (by exact_mod_cast hN)]

/-- **The `liminf` convention at infinity.** The `liminf` of the values of a process at the
truncated times `min τ N` is its value at `τ` where `τ` is finite, and the `liminf` of the process
where `τ` is infinite. -/
theorem liminf_stoppedValue_min (u : ℕ → Ω → β) (τ : Ω → WithTop ℕ) (ω : Ω) :
    liminf (fun N : ℕ ↦ stoppedValue u (fun ω ↦ min (τ ω) N) ω) atTop =
      if τ ω = ⊤ then liminf (fun n ↦ u n ω) atTop else stoppedValue u τ ω := by
  induction hτω : τ ω using WithTop.recTopCoe with
  | top => simp [stoppedValue, hτω, WithTop.untopA_natCast]
  | coe b =>
    rw [ite_eq_right (WithTop.coe_ne_top (a := b)),
      ← liminf_const (f := (atTop : Filter ℕ)) (stoppedValue u τ ω)]
    refine liminf_congr ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    rw [← Nat.cast_withTop] at hτω
    rw [stoppedValue_of_eq_natCast hτω,
      stoppedValue_of_eq_natCast (by rw [hτω, min_eq_left (by exact_mod_cast hN)])]

end ConditionallyCompleteLattice

/-- The value at a random time is monotone in the process: if `u n ω ≤ v n ω` at every time `n`,
then the value of `u` at `ω` at every random time is at most that of `v`. -/
theorem stoppedValueLimsup_mono [CompleteLattice β] {u v : ℕ → Ω → β}
    (h : ∀ n, u n ω ≤ v n ω) : stoppedValueLimsup u τ ω ≤ stoppedValueLimsup v τ ω := by
  unfold stoppedValueLimsup
  split_ifs
  · exact limsup_le_limsup (Eventually.of_forall h)
  · exact h _

/-- The value of a process at a random time is at most its supremum over time. -/
theorem stoppedValueLimsup_le_iSup [CompleteLattice β] {u : ℕ → Ω → β} :
    stoppedValueLimsup u τ ω ≤ ⨆ n, u n ω := by
  by_cases hτ : τ ω = ⊤
  · rw [stoppedValueLimsup_of_eq_top hτ]
    exact limsup_le_iSup
  · rw [stoppedValueLimsup_eq_stoppedValue hτ]
    exact le_iSup (u · ω) _

/-- The value of a process of measurable functions at a measurable random time is measurable. -/
theorem measurable_stoppedValueLimsup [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
    [OrderTopology β] [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β]
    {mΩ : MeasurableSpace Ω} {u : ℕ → Ω → β} (hu : ∀ n, Measurable (u n)) (hτ : Measurable τ) :
    Measurable (stoppedValueLimsup u τ) := by
  have h : Measurable fun p : Ω × WithTop ℕ ↦ stoppedValueLimsup u (fun _ ↦ p.2) p.1 := by
    refine measurable_from_prod_countable_left fun k ↦ ?_
    cases k with
    | top => simpa using Measurable.limsup hu
    | coe n => simpa [← Nat.cast_withTop, stoppedValueLimsup_const] using hu n
  exact h.comp (measurable_id.prodMk hτ)

/-- The integral of the value of an `ℝ≥0∞`-valued process at a random time bounded by `N` is at
most the sum of the integrals of the process at the times up to `N`. -/
theorem lintegral_stoppedValueLimsup_le_sum {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {u : ℕ → Ω → ℝ≥0∞} (hu : ∀ n, AEMeasurable (u n) μ) {N : ℕ} (hτN : ∀ ω, τ ω ≤ N) :
    ∫⁻ ω, stoppedValueLimsup u τ ω ∂μ ≤ ∑ k ∈ Finset.range (N + 1), ∫⁻ ω, u k ω ∂μ := by
  rw [← lintegral_finsetSum' (Finset.range (N + 1)) fun k _ ↦ hu k]
  refine lintegral_mono fun ω ↦ ?_
  have h := hτN ω
  induction hτω : τ ω using WithTop.recTopCoe with
  | top => simp [hτω] at h
  | coe k =>
    rw [← Nat.cast_withTop] at hτω
    rw [hτω, Nat.cast_le] at h
    rw [stoppedValueLimsup_of_eq_natCast hτω]
    exact Finset.single_le_sum (f := fun k ↦ u k ω) (fun _ _ ↦ zero_le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le h))

/-- **Monotone convergence at truncated times.** For an almost everywhere nondecreasing process
of measurable `ℝ≥0∞`-valued functions and a measurable random time `τ`, the integrals of its
values at the truncated times `min τ N` increase to the integral of its value at `τ`. -/
theorem tendsto_lintegral_stoppedValueLimsup_min {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {u : ℕ → Ω → ℝ≥0∞} (hu : ∀ n, Measurable (u n)) (hmono : ∀ᵐ ω ∂μ, Monotone (u · ω))
    (hτ : Measurable τ) :
    Tendsto (fun N : ℕ ↦ ∫⁻ ω, stoppedValueLimsup u (fun ω ↦ min (τ ω) N) ω ∂μ) atTop
      (𝓝 (∫⁻ ω, stoppedValueLimsup u τ ω ∂μ)) := by
  have hmin_top (ω : Ω) (N : ℕ) : min (τ ω) N ≠ ⊤ :=
    WithTop.ne_top_of_le_natCast (min_le_right _ _)
  refine lintegral_tendsto_of_tendsto_of_monotone (fun N ↦ (measurable_stoppedValueLimsup hu
    ((measurable_of_countable fun t : WithTop ℕ ↦ min t N).comp hτ)).aemeasurable) ?_ ?_
  · filter_upwards [hmono] with ω hω N N' h
    dsimp only
    rw [stoppedValueLimsup_eq_stoppedValue (τ := fun ω ↦ min (τ ω) N) (hmin_top ω N),
      stoppedValueLimsup_eq_stoppedValue (τ := fun ω ↦ min (τ ω) N') (hmin_top ω N')]
    exact hω (WithTop.untopA_mono (hmin_top ω N') (min_le_min_left _ (by exact_mod_cast h)))
  · filter_upwards [hmono] with ω hω
    refine tendsto_stoppedValueLimsup_min ?_
    rw [(tendsto_atTop_iSup hω).limsup_eq]
    exact tendsto_atTop_iSup hω

/-- The integrals of `f` over `s ∩ {τ ≤ N}` increase to its integral over `s ∩ {τ ≠ ⊤}`. -/
theorem tendsto_setLIntegral_inter_le_natCast {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {s : Set Ω} (f : Ω → ℝ≥0∞) (hs : MeasurableSet s) (hτ : Measurable τ) :
    Tendsto (fun N : ℕ ↦ ∫⁻ ω in s ∩ {ω | τ ω ≤ N}, f ω ∂μ) atTop
      (𝓝 (∫⁻ ω in s ∩ {ω | τ ω ≠ ⊤}, f ω ∂μ)) := by
  have hmeas (N : ℕ) : MeasurableSet (s ∩ {ω | τ ω ≤ N}) := hs.inter (hτ measurableSet_Iic)
  have hU : ⋃ N : ℕ, s ∩ {ω | τ ω ≤ N} = s ∩ {ω | τ ω ≠ ⊤} := by
    rw [← Set.inter_iUnion]
    congr 1
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨fun ⟨N, hN⟩ ↦ WithTop.ne_top_of_le_natCast hN, fun h ↦ ?_⟩
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 h
    exact ⟨t, by simp [← ht]⟩
  -- The set integrals of `f` are the measures of the sets under `μ.withDensity f`.
  simp_rw [← withDensity_apply _ (hmeas _)]
  rw [← withDensity_apply _ (hU ▸ MeasurableSet.iUnion hmeas), ← hU]
  exact tendsto_measure_iUnion_atTop fun N N' h ↦
    Set.inter_subset_inter_right _ fun ω (hω : τ ω ≤ N) ↦ hω.trans (by exact_mod_cast h)

/-- The value `fun ω ↦ u (σ ω) ω` of a process of measurable functions, indexed by a countable
type, at a measurable random time is measurable. -/
theorem measurable_apply_of_countable {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace β] {mΩ : MeasurableSpace Ω} {u : ι → Ω → β}
    {σ : Ω → ι} (hu : ∀ i, Measurable (u i)) (hσ : Measurable σ) :
    Measurable fun ω ↦ u (σ ω) ω :=
  (measurable_from_prod_countable_left (f := fun p : Ω × ι ↦ u p.2 p.1) hu).comp
    (measurable_id.prodMk hσ)

/-- **The largest expectation at a random time** [RRLK, Lemma 3]. The supremum, over the random
times `τ` with values in `ℕ`, not necessarily stopping times, of the integral of an `ℝ≥0∞`-valued
process read at `τ` is the integral of its supremum over time. -/
theorem iSup_lintegral_apply_eq_lintegral_iSup {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {u : ℕ → Ω → ℝ≥0∞} (hu : ∀ n, AEMeasurable (u n) μ) :
    ⨆ τ : Ω → ℕ, ∫⁻ ω, u (τ ω) ω ∂μ = ∫⁻ ω, ⨆ n, u n ω ∂μ := by
  refine le_antisymm (iSup_le fun τ ↦ lintegral_mono fun ω ↦ le_iSup (u · ω) (τ ω)) ?_
  -- the supremum is the increasing limit of the running maxima `partialSups` up to `N`
  simp_rw [← iSup_partialSups_eq (u · _)]
  rw [lintegral_iSup' (fun N ↦ by
      simp_rw [partialSups_eq_biSup]
      exact AEMeasurable.iSup fun k ↦ AEMeasurable.iSup fun _ ↦ hu k)
    (ae_of_all _ fun ω ↦ (partialSups (u · ω)).monotone)]
  refine iSup_le fun N ↦ ?_
  -- up to each horizon `N`, the running maximum is attained at some time `k ≤ N`, which depends
  -- on `ω`
  have h_max (ω : Ω) : ∃ k, ∀ j ≤ N, u j ω ≤ u k ω := by
    obtain ⟨k, -, hk⟩ := (Finset.range (N + 1)).exists_max_image (u · ω) ⟨0, by simp⟩
    exact ⟨k, fun j hj ↦ hk j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))⟩
  choose τ hτ using h_max
  exact le_iSup_of_le τ (lintegral_mono fun ω ↦ partialSups_le _ _ _ fun j hj ↦ hτ ω j hj)

/-- **The largest expectation at a possibly infinite random time** [RRLK, Lemma 3]. The supremum,
over the random times `τ` with values in `WithTop ℕ`, of the integral of an `ℝ≥0∞`-valued process
read at `τ`, with its `limsup` where `τ` is infinite, is the integral of its supremum over time. -/
theorem iSup_lintegral_stoppedValueLimsup_eq_lintegral_iSup {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {u : ℕ → Ω → ℝ≥0∞} (hu : ∀ n, AEMeasurable (u n) μ) :
    ⨆ τ : Ω → WithTop ℕ, ∫⁻ ω, stoppedValueLimsup u τ ω ∂μ = ∫⁻ ω, ⨆ n, u n ω ∂μ := by
  refine le_antisymm (iSup_le fun τ ↦ lintegral_mono fun ω ↦ stoppedValueLimsup_le_iSup) ?_
  rw [← iSup_lintegral_apply_eq_lintegral_iSup hu]
  exact iSup_le fun τ ↦ le_iSup_of_le (fun ω ↦ (τ ω : WithTop ℕ))
    (lintegral_congr fun ω ↦ (stoppedValueLimsup_of_eq_natCast (τ := fun ω ↦ (τ ω : WithTop ℕ))
      (ω := ω) rfl).symm).le

/-! ### Events at a random time -/

section StoppedEvent

variable {A B : ℕ → Set Ω}

/-- The event of a sequence of events `A : ℕ → Set Ω` read at the random time `τ : Ω → WithTop ℕ`:
the points `ω ∈ A n` where `τ ω = n`, and the points of `limsup A atTop`, at which infinitely many
of the events occur, where `τ ω = ⊤` [RRLK, Lemma 2]. -/
def stoppedEvent (A : ℕ → Set Ω) (τ : Ω → WithTop ℕ) : Set Ω :=
  {ω | if τ ω = ⊤ then ω ∈ limsup A atTop else ω ∈ A (τ ω).untopA}

/-- Where the random time is finite, the event read at it is the event at that time. -/
theorem mem_stoppedEvent_of_eq_natCast {n : ℕ} (h : τ ω = n) :
    ω ∈ stoppedEvent A τ ↔ ω ∈ A n := by
  simp [stoppedEvent, h]

/-- Where the random time is finite, the event read at it is the event at its value, as Mathlib's
`stoppedValue` reads a process. -/
theorem mem_stoppedEvent_of_ne_top (h : τ ω ≠ ⊤) :
    ω ∈ stoppedEvent A τ ↔ ω ∈ A (τ ω).untopA := by
  simp [stoppedEvent, h]

/-- Where the random time is infinite, the event read at it is the event that infinitely many of
the events occur. -/
theorem mem_stoppedEvent_of_eq_top (h : τ ω = ⊤) :
    ω ∈ stoppedEvent A τ ↔ ∃ᶠ n in atTop, ω ∈ A n := by
  simp [stoppedEvent, h, mem_limsup_iff_frequently_mem]

/-- The event read at a random time that is finite everywhere is the event at its value. -/
theorem stoppedEvent_of_forall_ne_top (A : ℕ → Set Ω) (h : ∀ ω, τ ω ≠ ⊤) :
    stoppedEvent A τ = {ω | ω ∈ A (τ ω).untopA} :=
  Set.ext fun ω ↦ mem_stoppedEvent_of_ne_top (h ω)

/-- The event read at a constant finite time is the event at that time. -/
theorem stoppedEvent_const (A : ℕ → Set Ω) (n : ℕ) :
    stoppedEvent A (fun _ ↦ (n : WithTop ℕ)) = A n :=
  Set.ext fun _ ↦ mem_stoppedEvent_of_eq_natCast rfl

/-- The event read at the constant time `⊤` is the `limsup` of the events. -/
@[simp]
theorem stoppedEvent_top (A : ℕ → Set Ω) : stoppedEvent A (fun _ ↦ ⊤) = limsup A atTop := by
  ext
  simp [stoppedEvent]

/-- The event read at a random time is monotone in the events. -/
theorem stoppedEvent_mono (h : ∀ n, A n ⊆ B n) : stoppedEvent A τ ⊆ stoppedEvent B τ := by
  intro ω hω
  by_cases hτ : τ ω = ⊤
  · rw [mem_stoppedEvent_of_eq_top hτ] at hω ⊢
    exact hω.mono fun n hn ↦ h n hn
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hτ
    rw [mem_stoppedEvent_of_eq_natCast hn.symm] at hω ⊢
    exact h n hω

/-- The event read at a random time is contained in the union of the events. -/
theorem stoppedEvent_subset_iUnion : stoppedEvent A τ ⊆ ⋃ n, A n := by
  intro ω hω
  by_cases hτ : τ ω = ⊤
  · exact Set.mem_iUnion.2 ((mem_stoppedEvent_of_eq_top hτ).1 hω).exists
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hτ
    exact Set.mem_iUnion.2 ⟨n, (mem_stoppedEvent_of_eq_natCast hn.symm).1 hω⟩

/-- The event of a sequence of measurable events read at a measurable random time is
measurable. -/
theorem measurableSet_stoppedEvent {mΩ : MeasurableSpace Ω} (hA : ∀ n, MeasurableSet (A n))
    (hτ : Measurable τ) : MeasurableSet (stoppedEvent A τ) := by
  -- split along the values of `τ`
  have h_eq : stoppedEvent A τ = ⋃ k : WithTop ℕ, τ ⁻¹' {k} ∩ stoppedEvent A (fun _ ↦ k) := by
    ext ω
    simp [stoppedEvent]
  rw [h_eq]
  refine .iUnion fun k ↦ (hτ (measurableSet_singleton k)).inter ?_
  cases k with
  | top => simpa using MeasurableSet.measurableSet_limsup hA
  | coe n => simpa [stoppedEvent_const] using hA n

end StoppedEvent

end MeasureTheory
