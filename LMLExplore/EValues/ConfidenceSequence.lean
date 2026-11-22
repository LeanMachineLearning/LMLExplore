/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.SequentialTest

/-!
# Confidence sequences

For a type `Θ` of parameters and a family of nulls `S : Θ → Set (Measure Ω)`, with `P ∈ S θ`
meaning that `θ` is a true parameter of `P`, a confidence sequence at level `α` is a sequence of
random sets `C n ω ⊆ Θ`, adapted to a filtration `ℱ` indexed by `ℕ`, that contain every true
parameter at all times simultaneously, except with probability at most `α`:
`P {ω | ∃ n, θ ∉ C n ω} ≤ α` for every `θ` and every `P ∈ S θ` [DR67; HRMS21; RW, Definition 13.3].
A statistician who monitors the data, stops at a data-dependent time, or reports the set at any
time chosen after seeing the data, keeps coverage `1 - α`. The parameter may be of any type and
partially identified: a functional `φ` on a model `M` is the case `S θ = {P ∈ M | φ P = θ}`.

The uniform guarantee is the same as coverage at every random time, with the value
`liminf (C · ω)` where the random time is infinite, and as coverage at every stopping time
[RRLK, §4.3 and Lemma 2]; running intersections of confidence sequences are confidence sequences.

Confidence sequences are dual to families of sequential tests [RRLK, §4.3, Proposition 13]: the
parameters `θ` that the tests of the nulls `S θ` have not rejected at time `n` form a confidence
sequence, and conversely every confidence sequence `C` is the set of parameters not rejected by
the level-`α` sequential tests `𝟙{θ ∉ C n}`. Through the reductions between sequential tests,
p-processes and e-processes, this gives confidence sequences `{θ | α < p θ n ω}` from p-processes
and `{θ | E θ n ω < α⁻¹}` from e-processes [WSR24, Theorem 1; RW, §13.1], and shows that every
confidence sequence at a level `α ≠ ∞` is of the latter form for the e-processes
`α⁻¹ * 𝟙{θ ∉ C n}`.

## Main definitions

* `ProbabilityTheory.IsConfSeq C ℱ S α`: `C` is a confidence sequence at level `α` for the
  parameters of the nulls `S` and the filtration `ℱ`.

## Main statements

* `ProbabilityTheory.isConfSeq_tfae`: coverage uniformly in time, at every random time and at
  every stopping time, possibly infinite or bounded, are equivalent [RRLK, §4.3 and Lemma 2].
* `ProbabilityTheory.isConfSeq_iff_forall_isTimeUniform`: confidence sequences are an instance of
  time-uniform validity (`ProbabilityTheory.IsTimeUniform`), for the events that the set misses a
  parameter [RRLK, §4.3 and Lemma 2].
* `ProbabilityTheory.isConfSeq_biInter_iff`, `ProbabilityTheory.IsConfSeq.biInter`: the running
  intersection of a confidence sequence is a confidence sequence.
* `ProbabilityTheory.isConfSeq_iff_exists_isSequentialTest`: the confidence sequences at level `α`
  are exactly the sets of parameters not rejected by families of level-`α` sequential tests
  [RRLK, Proposition 13].
* `ProbabilityTheory.isConfSeq_of_isPProcess`, `ProbabilityTheory.isConfSeq_of_isEProcess`:
  confidence sequences from families of p-processes and of e-processes [WSR24, Theorem 1].
* `ProbabilityTheory.isConfSeq_iff_exists_isEProcess`: for a level `α ≠ ∞`, every confidence
  sequence is `{θ | E θ n ω < α⁻¹}` for a family of e-processes `E θ` for `S θ` [RRLK, §4.3; RW,
  §13.1].

## References

* [DR67] D. A. Darling and H. Robbins, *Confidence sequences for mean, variance, and median*,
  PNAS 58 (1967).
* [HRMS21] S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform, nonparametric,
  nonasymptotic confidence sequences*, Ann. Statist. 49 (2021).
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, §4.3, Lemma 2 and
  Proposition 13.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Definition 13.3 and §13.1.
* [WSR24] I. Waudby-Smith and A. Ramdas, *Estimating means of bounded random variables by
  betting*, J. R. Stat. Soc. Ser. B 86 (2024), arXiv:2010.09686v7, Theorem 1.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Θ : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
  {S T : Θ → Set (Measure Ω)} {P : Measure Ω} {C D : ℕ → Ω → Set Θ} {α β : ℝ≥0∞} {θ : Θ}

/-- `C : ℕ → Ω → Set Θ` is a **confidence sequence** at level `α` for the parameters of the nulls
`S : Θ → Set (Measure Ω)` and the filtration `ℱ`: the event `{ω | θ ∈ C n ω}` is
`ℱ n`-measurable for every `θ` and `n`, and for every parameter `θ` and every `P ∈ S θ` the
probability that `C n` misses `θ` at some time `n` is at most `α`
[RW, Definition 13.3; RRLK, §4.3]. -/
structure IsConfSeq (C : ℕ → Ω → Set Θ) (ℱ : Filtration ℕ mΩ) (S : Θ → Set (Measure Ω))
    (α : ℝ≥0∞) : Prop where
  measurableSet_mem : ∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ C n ω}
  measure_exists_notMem_le : ∀ θ, ∀ P ∈ S θ, P {ω | ∃ n, θ ∉ C n ω} ≤ α

namespace IsConfSeq

/-- The event that a confidence sequence misses `θ` at time `n` is `ℱ n`-measurable. -/
theorem measurableSet_notMem (hC : IsConfSeq C ℱ S α) (θ : Θ) (n : ℕ) :
    MeasurableSet[ℱ n] {ω | θ ∉ C n ω} :=
  (hC.measurableSet_mem θ n).compl

/-- **Coverage at random times** [RRLK, Lemma 2]. Under every `P ∈ S θ`, a confidence sequence
read at a random time `τ`, not necessarily a stopping time, misses `θ` with probability at most
`α`. Where `τ` is infinite, Mathlib's `stoppedValue` reads the sequence at an arbitrary time. -/
theorem measure_notMem_le (hC : IsConfSeq C ℱ S α) (τ : Ω → WithTop ℕ) (hP : P ∈ S θ) :
    P {ω | θ ∉ stoppedValue C τ ω} ≤ α :=
  (hC.measure_exists_notMem_le θ P hP).trans' (measure_mono fun _ hω ↦ ⟨_, hω⟩)

/-- **Coverage at possibly infinite random times** [RRLK, §4.3 and Lemma 2]. Under every
`P ∈ S θ`, a confidence sequence read at a random time `τ` with values in `WithTop ℕ`, not
necessarily a stopping time, misses `θ` with probability at most `α`, with the set
`liminf (C · ω)` of the parameters that `C n ω` eventually contains where `τ` is infinite. -/
theorem measure_notMem_liminf_le (hC : IsConfSeq C ℱ S α) (τ : Ω → WithTop ℕ) (hP : P ∈ S θ) :
    P {ω | θ ∉ if τ ω = ⊤ then liminf (fun n ↦ C n ω) atTop else stoppedValue C τ ω} ≤ α := by
  refine (hC.measure_exists_notMem_le θ P hP).trans' (measure_mono fun ω hω ↦ ?_)
  by_cases hτ : τ ω = ⊤
  · -- a parameter outside the `liminf` is missed infinitely often, so at least once
    simp only [mem_ofPred_eq, hτ, ↓reduceIte, mem_liminf_iff_eventually_mem, not_eventually] at hω
    exact hω.exists
  · simp only [mem_ofPred_eq, hτ, ↓reduceIte] at hω
    exact ⟨_, hω⟩

/-- A confidence sequence for the nulls `T` is one for all smaller nulls `S θ ⊆ T θ`. -/
theorem anti_set (hST : ∀ θ, S θ ⊆ T θ) (hC : IsConfSeq C ℱ T α) : IsConfSeq C ℱ S α :=
  ⟨hC.measurableSet_mem, fun θ P hP ↦ hC.measure_exists_notMem_le θ P (hST θ hP)⟩

/-- A confidence sequence at level `α` is one at every level `β ≥ α`. -/
theorem mono_level (hC : IsConfSeq C ℱ S α) (hαβ : α ≤ β) : IsConfSeq C ℱ S β :=
  ⟨hC.measurableSet_mem, fun θ P hP ↦ (hC.measure_exists_notMem_le θ P hP).trans hαβ⟩

/-- **Domination.** Adapted random sets that contain a confidence sequence at every time,
quasi-surely for the null `S θ` of the parameter `θ`, form a confidence sequence. -/
theorem mono_ae (hC : IsConfSeq C ℱ S α) (hD : ∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ D n ω})
    (hCD : ∀ θ n, ∀ᶠ ω in quasiSure (S θ), θ ∈ C n ω → θ ∈ D n ω) : IsConfSeq D ℱ S α := by
  refine ⟨hD, fun θ P hP ↦ (hC.measure_exists_notMem_le θ P hP).trans' (measure_mono_ae ?_)⟩
  filter_upwards [ae_all_iff.2 fun n ↦ ae_of_eventually_quasiSure (hCD θ n) hP] with ω hω ⟨n, hn⟩
    using ⟨n, mt (hω n) hn⟩

/-- Adapted random sets that contain a confidence sequence at every time form a confidence
sequence. -/
theorem mono (hC : IsConfSeq C ℱ S α) (hD : ∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ D n ω})
    (hCD : ∀ n ω, C n ω ⊆ D n ω) : IsConfSeq D ℱ S α :=
  hC.mono_ae hD fun _ n ↦ .of_forall fun ω ↦ @hCD n ω _

/-- Adapted random sets that agree with a confidence sequence at every time, quasi-surely for the
null `S θ` of the parameter `θ`, form a confidence sequence. -/
theorem congr (hC : IsConfSeq C ℱ S α) (hD : ∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ D n ω})
    (hCD : ∀ θ n, ∀ᶠ ω in quasiSure (S θ), θ ∈ C n ω ↔ θ ∈ D n ω) : IsConfSeq D ℱ S α :=
  hC.mono_ae hD fun θ n ↦ (hCD θ n).mono fun _ h ↦ h.1

end IsConfSeq

/-- **Confidence sequences are time-uniformly valid** [RRLK, §4.3 and Lemma 2]. Random sets form a
confidence sequence at level `α` exactly when, for every parameter `θ`, the events `{θ ∉ C n}`
that they miss `θ` are time-uniformly valid at level `α` for the null `S θ`. -/
theorem isConfSeq_iff_forall_isTimeUniform :
    IsConfSeq C ℱ S α ↔ ∀ θ, IsTimeUniform (fun n ↦ {ω | θ ∉ C n ω}) ℱ (S θ) α :=
  ⟨fun h θ ↦ ⟨h.measurableSet_notMem θ, fun P hP ↦ by
      simpa [ofPred_exists] using h.measure_exists_notMem_le θ P hP⟩,
    fun h ↦ ⟨fun θ n ↦ by simpa [compl_ofPred] using ((h θ).measurableSet n).compl, fun θ P hP ↦ by
      simpa [ofPred_exists] using (h θ).measure_iUnion_le P hP⟩⟩

/-- For every parameter `θ`, the events `{θ ∉ C n}` that a confidence sequence misses `θ` are
time-uniformly valid at level `α` for the null `S θ`. -/
theorem IsConfSeq.isTimeUniform (hC : IsConfSeq C ℱ S α) (θ : Θ) :
    IsTimeUniform (fun n ↦ {ω | θ ∉ C n ω}) ℱ (S θ) α :=
  isConfSeq_iff_forall_isTimeUniform.1 hC θ

/-- The constant confidence sequence `univ`, which contains every parameter, has level `0`. -/
theorem isConfSeq_univ (ℱ : Filtration ℕ mΩ) (S : Θ → Set (Measure Ω)) :
    IsConfSeq (fun _ _ ↦ (univ : Set Θ)) ℱ S 0 :=
  ⟨fun _ _ ↦ by simp, fun _ _ _ ↦ by simp⟩

/-- **Coverage at random and stopping times** [RRLK, §4.3 and Lemma 2]. For adapted random sets
`C n ω ⊆ Θ`, the following are equivalent:
1. `C` is a confidence sequence at level `α`: it misses a true parameter at some time with
  probability at most `α`;
2. read at every random time `τ` with values in `WithTop ℕ`, with the set `liminf (C · ω)` where
  `τ` is infinite, it misses a true parameter with probability at most `α`;
3. the same at every stopping time with values in `WithTop ℕ`;
4. read at every random time `τ` with Mathlib's `stoppedValue`, which reads it at an arbitrary
  time where `τ` is infinite, it misses a true parameter with probability at most `α`;
5. the same at every bounded stopping time.

The random time may depend on the parameter. For each parameter `θ`, this is the equivalence lemma
for time-uniform validity (`ProbabilityTheory.isTimeUniform_tfae`) for the events `{θ ∉ C n}`. -/
theorem isConfSeq_tfae (hC : ∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ C n ω}) :
    List.TFAE [IsConfSeq C ℱ S α,
      ∀ θ, ∀ P ∈ S θ, ∀ τ : Ω → WithTop ℕ,
        P {ω | θ ∉ if τ ω = ⊤ then liminf (fun n ↦ C n ω) atTop else stoppedValue C τ ω} ≤ α,
      ∀ θ, ∀ P ∈ S θ, ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ →
        P {ω | θ ∉ if τ ω = ⊤ then liminf (fun n ↦ C n ω) atTop else stoppedValue C τ ω} ≤ α,
      ∀ θ, ∀ P ∈ S θ, ∀ τ : Ω → WithTop ℕ, P {ω | θ ∉ stoppedValue C τ ω} ≤ α,
      ∀ θ, ∀ P ∈ S θ, ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
        P {ω | θ ∉ stoppedValue C τ ω} ≤ α] := by
  -- read at a random time, the set misses `θ` on the event `{θ ∉ C n}` read at that time
  have h_event (θ : Θ) (τ : Ω → WithTop ℕ) :
      {ω | θ ∉ if τ ω = ⊤ then liminf (fun n ↦ C n ω) atTop else stoppedValue C τ ω} =
        stoppedEvent (fun n ↦ {ω | θ ∉ C n ω}) τ := by
    ext ω
    by_cases hτ : τ ω = ⊤
    · simp [hτ, mem_stoppedEvent_of_eq_top, mem_liminf_iff_eventually_mem, frequently_atTop]
    · simp [hτ, mem_stoppedEvent_of_ne_top, stoppedValue]
  -- the equivalence lemma for the events `{θ ∉ C n}`, for each parameter `θ`
  have h_tu (θ : Θ) := isTimeUniform_tfae (A := fun n ↦ {ω | θ ∉ C n ω}) (S := S θ) (α := α)
    fun n ↦ (hC θ n).compl
  tfae_have 1 ↔ 2 := by
    simp only [isConfSeq_iff_forall_isTimeUniform, h_event]
    exact forall_congr' fun θ ↦ (h_tu θ).out 1 2
  tfae_have 1 ↔ 3 := by
    simp only [isConfSeq_iff_forall_isTimeUniform, h_event]
    exact forall_congr' fun θ ↦ (h_tu θ).out 1 3
  tfae_have 1 → 4 := fun h θ _ hP τ ↦ h.measure_notMem_le τ hP
  tfae_have 4 → 5 := fun h θ P hP τ _ _ _ ↦ h θ P hP τ
  tfae_have 5 → 1 := fun h ↦ isConfSeq_iff_forall_isTimeUniform.2 fun θ ↦
    ((h_tu θ).out 1 5).2 fun P hP τ hτ N hτN ↦ by
      -- a bounded time is finite, where the event is read through `stoppedValue`
      rw [stoppedEvent_of_forall_ne_top _
        fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)]
      exact h θ P hP τ hτ N hτN
  tfae_finish

/-- **Confidence sequences are valid at stopping times** [RRLK, §4.3]. Adapted random sets form a
confidence sequence at level `α` exactly when, read at every bounded stopping time, they miss
every true parameter with probability at most `α`. -/
theorem isConfSeq_iff_forall_isStoppingTime :
    IsConfSeq C ℱ S α ↔ (∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ C n ω}) ∧
      ∀ θ, ∀ P ∈ S θ, ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
        P {ω | θ ∉ stoppedValue C τ ω} ≤ α :=
  ⟨fun h ↦ ⟨h.measurableSet_mem, (isConfSeq_tfae h.measurableSet_mem).out 1 5 |>.1 h⟩,
    fun ⟨hC, h⟩ ↦ (isConfSeq_tfae hC).out 1 5 |>.2 h⟩

/-! ### Running intersections -/

/-- The events of membership in the running intersection of adapted random sets are adapted. -/
theorem measurableSet_mem_biInter (hC : ∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ C n ω}) (θ : Θ)
    (n : ℕ) : MeasurableSet[ℱ n] {ω | θ ∈ ⋂ k ≤ n, C k ω} := by
  simp only [mem_iInter, ofPred_forall]
  exact .iInter fun k ↦ .iInter fun hk ↦ ℱ.mono hk _ (hC θ k)

/-- **Running intersections** [RRLK, §4.3]. For adapted random sets `C`, the running intersection
`fun n ω ↦ ⋂ k ≤ n, C k ω` is a confidence sequence exactly when `C` is one: a confidence sequence
may be taken nonincreasing. -/
theorem isConfSeq_biInter_iff (hC : ∀ θ n, MeasurableSet[ℱ n] {ω | θ ∈ C n ω}) :
    IsConfSeq (fun n ω ↦ ⋂ k ≤ n, C k ω) ℱ S α ↔ IsConfSeq C ℱ S α := by
  -- the running intersection misses `θ` at some time exactly when `C` does
  have h (θ : Θ) : {ω | ∃ n, θ ∉ ⋂ k ≤ n, C k ω} = {ω | ∃ n, θ ∉ C n ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, not_forall, exists_prop]
    exact ⟨fun ⟨_, k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, k, le_rfl, hk⟩⟩
  exact ⟨fun h' ↦ ⟨hC, fun θ ↦ h θ ▸ h'.measure_exists_notMem_le θ⟩,
    fun h' ↦ ⟨measurableSet_mem_biInter hC, fun θ ↦ (h θ).symm ▸ h'.measure_exists_notMem_le θ⟩⟩

/-- The running intersection `fun n ω ↦ ⋂ k ≤ n, C k ω` of a confidence sequence is a confidence
sequence. -/
theorem IsConfSeq.biInter (hC : IsConfSeq C ℱ S α) :
    IsConfSeq (fun n ω ↦ ⋂ k ≤ n, C k ω) ℱ S α :=
  (isConfSeq_biInter_iff hC.measurableSet_mem).2 hC

/-! ### Duality with sequential tests, p-processes and e-processes -/

section Duality

variable {φ p E : Θ → ℕ → Ω → ℝ≥0∞}

/-- **Confidence sequences from sequential tests** [RRLK, Proposition 13]. For a family of
level-`α` sequential tests `φ θ` of the nulls `S θ`, the parameters that have not been rejected at
time `n` form a confidence sequence at level `α`. -/
theorem isConfSeq_of_isSequentialTest (hφ : ∀ θ, IsSequentialTest (φ θ) ℱ (S θ) α) :
    IsConfSeq (fun n ω ↦ {θ | φ θ n ω = 0}) ℱ S α := by
  refine ⟨fun θ n ↦ (hφ θ).adapted n (measurableSet_singleton 0), fun θ P hP ↦ ?_⟩
  -- a `{0, 1}`-valued test that is not `0` is `1`
  refine ((hφ θ).measure_exists_eq_one_le P hP).trans' (measure_mono fun ω ⟨n, hn⟩ ↦ ⟨n, ?_⟩)
  exact ((hφ θ).eq_zero_or_eq_one n ω).resolve_left hn

/-- **Sequential tests from a confidence sequence** [RRLK, Proposition 13]. Rejecting `θ` at the
times at which a confidence sequence at level `α` misses it is a level-`α` sequential test of the
null `S θ`. -/
theorem IsConfSeq.isSequentialTest (hC : IsConfSeq C ℱ S α) (θ : Θ) :
    IsSequentialTest (fun n ↦ {ω | θ ∉ C n ω}.indicator 1) ℱ (S θ) α where
  adapted n := measurable_const.indicator (hC.measurableSet_notMem θ n)
  eq_zero_or_eq_one n ω := by by_cases h : θ ∈ C n ω <;> simp [h]
  measure_exists_eq_one_le P hP := by
    -- the test is `1` exactly where `C n` misses `θ`
    have h_event :
        {ω | ∃ n, {ω | θ ∉ C n ω}.indicator (1 : Ω → ℝ≥0∞) ω = 1} = {ω | ∃ n, θ ∉ C n ω} := by
      ext ω
      refine exists_congr fun n ↦ ?_
      by_cases h : θ ∈ C n ω <;> simp [h]
    exact (measure_mono h_event.le).trans (hC.measure_exists_notMem_le θ P hP)

/-- **The duality between confidence sequences and sequential tests** [RRLK, Proposition 13].
Random sets form a confidence sequence at level `α` exactly when they are the sets of parameters
not rejected by a family of level-`α` sequential tests `φ θ` of the nulls `S θ`. -/
theorem isConfSeq_iff_exists_isSequentialTest :
    IsConfSeq C ℱ S α ↔
      ∃ φ : Θ → ℕ → Ω → ℝ≥0∞, (∀ θ, IsSequentialTest (φ θ) ℱ (S θ) α) ∧
        C = fun n ω ↦ {θ | φ θ n ω = 0} := by
  refine ⟨fun hC ↦ ⟨_, hC.isSequentialTest, ?_⟩, fun ⟨φ, hφ, hCφ⟩ ↦
    hCφ ▸ isConfSeq_of_isSequentialTest hφ⟩
  ext n ω θ
  by_cases h : θ ∈ C n ω <;> simp [h]

/-- **Confidence sequences from p-processes.** For a family of p-processes `p θ` for the nulls
`S θ`, the parameters whose p-value exceeds `α` form a confidence sequence at level `α`. -/
theorem isConfSeq_of_isPProcess (hp : ∀ θ, IsPProcess (p θ) ℱ (S θ)) (α : ℝ≥0∞) :
    IsConfSeq (fun n ω ↦ {θ | α < p θ n ω}) ℱ S α := by
  simpa [indicator_apply_eq_zero] using
    isConfSeq_of_isSequentialTest fun θ ↦ (hp θ).isSequentialTest α

/-- **Confidence sequences from e-processes** [WSR24, Theorem 1; RRLK, §4.3; RW, §13.1]. For a
family of e-processes `E θ` for the nulls `S θ`, the parameters whose e-value is below `α⁻¹` form
a confidence sequence at level `α`. -/
theorem isConfSeq_of_isEProcess (hE : ∀ θ, IsEProcess (E θ) ℱ (S θ)) (α : ℝ≥0∞) :
    IsConfSeq (fun n ω ↦ {θ | E θ n ω < α⁻¹}) ℱ S α := by
  simpa [indicator_apply_eq_zero] using
    isConfSeq_of_isSequentialTest fun θ ↦ (hE θ).isSequentialTest α

/-- **E-processes from a confidence sequence** [RRLK, §4.3]. `α⁻¹` times the indicator of the
times at which a confidence sequence at level `α` misses `θ` is an e-process for the null `S θ`. -/
theorem IsConfSeq.isEProcess (hC : IsConfSeq C ℱ S α) (θ : Θ) :
    IsEProcess (fun n ω ↦ α⁻¹ * {ω | θ ∉ C n ω}.indicator 1 ω) ℱ (S θ) :=
  (hC.isSequentialTest θ).isEProcess_inv_mul

/-- **The duality between confidence sequences and e-processes** [RRLK, §4.3; RW, §13.1]. For a
level `α ≠ ∞`, random sets form a confidence sequence at level `α` exactly when they are the sets
`{θ | E θ n ω < α⁻¹}` for a family of e-processes `E θ` for the nulls `S θ`. -/
theorem isConfSeq_iff_exists_isEProcess (hα : α ≠ ∞) :
    IsConfSeq C ℱ S α ↔
      ∃ E : Θ → ℕ → Ω → ℝ≥0∞, (∀ θ, IsEProcess (E θ) ℱ (S θ)) ∧
        C = fun n ω ↦ {θ | E θ n ω < α⁻¹} := by
  refine ⟨fun hC ↦ ⟨_, hC.isEProcess, ?_⟩, fun ⟨E, hE, hCE⟩ ↦
    hCE ▸ isConfSeq_of_isEProcess hE α⟩
  -- `α⁻¹ * 𝟙{θ ∉ C n}` is `0 < α⁻¹` on `C n` and `α⁻¹` off it, since `α⁻¹ ≠ 0`
  ext n ω θ
  by_cases h : θ ∈ C n ω <;> simp [h, hα]

end Duality

end ProbabilityTheory
