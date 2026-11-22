/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.Probability.Process.HittingTime

/-!
# Time-uniform validity

A sequence of events `A n`, adapted to a filtration `ℱ` indexed by `ℕ`, is **time-uniformly valid**
at level `α` for a null hypothesis `S : Set (Measure Ω)` when, under every member of the null, the
probability that some `A n` occurs is at most `α`. When `A n` is the event of an erroneous claim
at time `n`, this is the error control of anytime-valid inference: p-processes (the events
`{p n ≤ α}`), sequential tests (the events of rejection) and confidence sequences (the events that
the set misses the parameter) are its instances.

**The equivalence lemma** [RRLK, Lemmas 1 and 2]. Read the events at a random time `τ` with values
in `WithTop ℕ`, with the event `limsup A` that infinitely many of them occur where `τ` is infinite
(`MeasureTheory.stoppedEvent`). Time-uniform validity is equivalent to validity at every random
time, possibly infinite and not necessarily a stopping time, and to validity at every stopping
time: the event at a random time is contained in the union, and the union is the event read at the
first time that one of the events occurs, which is a stopping time. The same holds for the random
times that are finite everywhere and for the bounded stopping times. The equivalence holds with
equality: the largest probability of the union over the null is the largest probability of the
event read at a stopping time.
Validity uniformly in time does not mention the filtration, so it passes to every finer filtration,
and back to a coarser one to which the events are adapted [CR26, Lemma 1].

**Expectations** [RRLK, Lemma 3]. For an adapted `ℝ≥0∞`-valued process `E`, the corresponding
statements about expectations are not equivalent. The largest expectation of `E` read at a random
time is the expectation of `⨆ n, E n`
(`MeasureTheory.iSup_lintegral_stoppedValueLimsup_eq_lintegral_iSup`), so `∫⁻ ⨆ n, E n ∂P ≤ 1`
under every member of the null makes `E` an e-process. The converse fails: on two points, the
martingale that starts at `1` and then doubles or vanishes has expectation `1` at every stopping
time, but its supremum has expectation `3 / 2`. The same martingale shows that the running maximum
of an e-process need not be an e-process [RRLK, Remark 16]. Adjusting the supremum restores the
bound: for an adjuster `A`, `⨆ n, A (max 1 (E n))` has expectation at most `1`
(`ProbabilityTheory.IsEProcess.lintegral_iSup_comp_max_le_one`, in `EValues/EProcess/Adjuster`).

## Main definitions

* `ProbabilityTheory.IsTimeUniform A ℱ S α`: the events `A n` are adapted to `ℱ`, and under every
  member of the null the probability that one of them occurs is at most `α`.

## Main statements

* `ProbabilityTheory.isTimeUniform_tfae`: time-uniform validity is validity at every random time
  and at every stopping time, possibly infinite or bounded [RRLK, Lemma 2].
* `ProbabilityTheory.iSup_measure_iUnion_eq_iSup_isStoppingTime`,
  `ProbabilityTheory.iSup_measure_iUnion_eq_iSup_stoppedEvent`: the largest probability of the
  union over the null is the largest probability of the event read at a stopping time, and at a
  random time [RRLK, Lemma 2].
* `ProbabilityTheory.IsTimeUniform.mono_filtration`, `ProbabilityTheory.isTimeUniform_iff_of_le`:
  monotonicity in the filtration [CR26, Lemma 1].
* `ProbabilityTheory.IsEProcess.of_lintegral_iSup_le_one`: an adapted process whose supremum has
  expectation at most `1` under every member of the null is an e-process [RRLK, Lemma 3].
* `ProbabilityTheory.exists_isEProcess_one_lt_lintegral_iSup`: some e-process has a supremum of
  expectation larger than `1` [RRLK, Lemma 3].
* `ProbabilityTheory.exists_isEProcess_not_isEProcess_partialSups`: the running maximum of an
  e-process need not be an e-process [RRLK, Remark 16].

## Implementation notes

The name and the union bound of `ProbabilityTheory.IsTimeUniform` follow the prototype
`IsTimeUniform` in `notes/book/Suggested.lean` (commit `1411a5b`) of the paper project
`RemyDegenne/evalues_research`. That prototype has no filtration argument; this version adds the
filtration and the adaptedness of the events, which the equivalence lemma and the monotonicity in
the filtration need.

## References

* [CR26] Y. J. Choe and A. Ramdas, *Combining evidence across filtrations*, arXiv:2402.09698v5,
  to appear in J. R. Stat. Soc. Ser. B: Lemma 1.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, Lemmas 1–3 and Remark 16.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝒢 ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {A B : ℕ → Set Ω} {α β : ℝ≥0∞} {E : ℕ → Ω → ℝ≥0∞}

/-- The events `A : ℕ → Set Ω` are **time-uniformly valid** at level `α` for the null `S` and the
filtration `ℱ`: they are adapted to `ℱ`, and under every member of the null the probability that
one of them occurs is at most `α` [RRLK, Lemma 2]. -/
structure IsTimeUniform (A : ℕ → Set Ω) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω))
    (α : ℝ≥0∞) : Prop where
  measurableSet : ∀ n, MeasurableSet[ℱ n] (A n)
  measure_iUnion_le : ∀ P ∈ S, P (⋃ n, A n) ≤ α

namespace IsTimeUniform

/-- **Validity at random times** [RRLK, Lemma 2]. Under every member of the null, time-uniformly
valid events read at a random time with values in `WithTop ℕ`, not necessarily a stopping time,
occur with probability at most `α`. -/
theorem measure_stoppedEvent_le (h : IsTimeUniform A ℱ S α) (τ : Ω → WithTop ℕ) (hP : P ∈ S) :
    P (stoppedEvent A τ) ≤ α :=
  (measure_mono stoppedEvent_subset_iUnion).trans (h.measure_iUnion_le P hP)

/-- Time-uniformly valid events for `T` are time-uniformly valid for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (h : IsTimeUniform A ℱ T α) : IsTimeUniform A ℱ S α :=
  ⟨h.measurableSet, fun P hP ↦ h.measure_iUnion_le P (hST hP)⟩

/-- Time-uniformly valid events at level `α` are time-uniformly valid at every level `β ≥ α`. -/
theorem mono_level (h : IsTimeUniform A ℱ S α) (hαβ : α ≤ β) : IsTimeUniform A ℱ S β :=
  ⟨h.measurableSet, fun P hP ↦ (h.measure_iUnion_le P hP).trans hαβ⟩

/-- Adapted events contained in time-uniformly valid events are time-uniformly valid. -/
theorem mono (h : IsTimeUniform A ℱ S α) (hB : ∀ n, MeasurableSet[ℱ n] (B n))
    (hBA : ∀ n, B n ⊆ A n) : IsTimeUniform B ℱ S α :=
  ⟨hB, fun P hP ↦ (measure_mono (iUnion_mono hBA)).trans (h.measure_iUnion_le P hP)⟩

/-- **Lifting** [CR26, Lemma 1]. Time-uniformly valid events for a filtration `𝒢` are
time-uniformly valid for every finer filtration. -/
theorem mono_filtration (h : IsTimeUniform A 𝒢 S α) (h𝒢ℱ : 𝒢 ≤ ℱ) : IsTimeUniform A ℱ S α :=
  ⟨fun n ↦ h𝒢ℱ n _ (h.measurableSet n), h.measure_iUnion_le⟩

end IsTimeUniform

/-- **Lifting** [CR26, Lemma 1]. For filtrations `𝒢 ≤ ℱ` and events adapted to the coarser
filtration `𝒢`, time-uniform validity for `𝒢` and for `ℱ` are the same. -/
theorem isTimeUniform_iff_of_le (h𝒢ℱ : 𝒢 ≤ ℱ) (hA : ∀ n, MeasurableSet[𝒢 n] (A n)) :
    IsTimeUniform A 𝒢 S α ↔ IsTimeUniform A ℱ S α :=
  ⟨fun h ↦ h.mono_filtration h𝒢ℱ, fun h ↦ ⟨hA, h.measure_iUnion_le⟩⟩

/-- **The equivalence lemma** [RRLK, Lemmas 1 and 2]. For events `A n` adapted to `ℱ`, the
following are equivalent:
1. they are time-uniformly valid at level `α`: under every member of the null, the probability that
  one of them occurs is at most `α`;
2. read at every random time with values in `WithTop ℕ`, with `limsup A` where the time is
  infinite, they occur with probability at most `α`;
3. the same at every stopping time with values in `WithTop ℕ`;
4. the same at every random time that is finite everywhere;
5. the same at every bounded stopping time. -/
theorem isTimeUniform_tfae (hA : ∀ n, MeasurableSet[ℱ n] (A n)) :
    List.TFAE [IsTimeUniform A ℱ S α,
      ∀ P ∈ S, ∀ τ : Ω → WithTop ℕ, P (stoppedEvent A τ) ≤ α,
      ∀ P ∈ S, ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → P (stoppedEvent A τ) ≤ α,
      ∀ P ∈ S, ∀ τ : Ω → WithTop ℕ, (∀ ω, τ ω ≠ ⊤) → P (stoppedEvent A τ) ≤ α,
      ∀ P ∈ S, ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
        P (stoppedEvent A τ) ≤ α] := by
  tfae_have 1 → 2 := fun h P hP τ ↦ h.measure_stoppedEvent_le τ hP
  tfae_have 2 → 3 := fun h P hP τ _ ↦ h P hP τ
  tfae_have 3 → 1 := fun h ↦ ⟨hA, fun P hP ↦ by
    -- the union is the event read at the first time that one of the events occurs
    obtain ⟨τ, hτ, h_eq⟩ := exists_isStoppingTime_stoppedEvent_eq_iUnion hA
    exact h_eq ▸ h P hP τ hτ⟩
  tfae_have 2 → 4 := fun h P hP τ _ ↦ h P hP τ
  tfae_have 4 → 5 := fun h P hP τ _ N hτN ↦
    h P hP τ fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)
  tfae_have 5 → 1 := fun h ↦ ⟨hA, fun P hP ↦ by
    rw [measure_iUnion_eq_iSup_isStoppingTime hA]
    exact iSup₂_le fun τ hτ ↦ iSup₂_le fun N hτN ↦ h P hP τ hτ N hτN⟩
  tfae_finish

/-- **Time-uniform validity at stopping times** [RRLK, Lemma 2]. Events adapted to `ℱ` are
time-uniformly valid at level `α` exactly when, under every member of the null, they occur with
probability at most `α` when read at every bounded stopping time. -/
theorem isTimeUniform_iff_forall_isStoppingTime :
    IsTimeUniform A ℱ S α ↔ (∀ n, MeasurableSet[ℱ n] (A n)) ∧
      ∀ P ∈ S, ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
        P (stoppedEvent A τ) ≤ α :=
  ⟨fun h ↦ ⟨h.measurableSet, (isTimeUniform_tfae h.measurableSet).out 1 5 |>.1 h⟩,
    fun ⟨hA, h⟩ ↦ (isTimeUniform_tfae hA).out 1 5 |>.2 h⟩

/-- **The equality case of the equivalence lemma** [RRLK, Lemma 2]. For events adapted to `ℱ`, the
largest probability, over the members of the null, that one of the events occurs is the largest
probability of the events read at a stopping time with values in `WithTop ℕ`. One stopping time,
the first time that one of the events occurs, attains it under every member. -/
theorem iSup_measure_iUnion_eq_iSup_isStoppingTime (hA : ∀ n, MeasurableSet[ℱ n] (A n))
    (S : Set (Measure Ω)) :
    ⨆ P ∈ S, P (⋃ n, A n) =
      ⨆ (τ : Ω → WithTop ℕ) (_ : IsStoppingTime ℱ τ), ⨆ P ∈ S, P (stoppedEvent A τ) := by
  refine le_antisymm ?_ (iSup₂_le fun τ _ ↦ iSup₂_mono fun P _ ↦
    measure_mono stoppedEvent_subset_iUnion)
  obtain ⟨τ, hτ, h_eq⟩ := exists_isStoppingTime_stoppedEvent_eq_iUnion hA
  exact le_iSup₂_of_le τ hτ (by rw [h_eq])

/-- **The equality case of the equivalence lemma at random times** [RRLK, Lemma 2]. The largest
probability, over the members of the null, that one of the events `A n` occurs is the largest
probability of the events read at a random time with values in `WithTop ℕ`. No measurability is
needed. -/
theorem iSup_measure_iUnion_eq_iSup_stoppedEvent (A : ℕ → Set Ω) (S : Set (Measure Ω)) :
    ⨆ P ∈ S, P (⋃ n, A n) = ⨆ τ : Ω → WithTop ℕ, ⨆ P ∈ S, P (stoppedEvent A τ) := by
  refine le_antisymm ?_ (iSup_le fun τ ↦ iSup₂_mono fun P _ ↦
    measure_mono stoppedEvent_subset_iUnion)
  exact le_iSup_of_le _ (by rw [stoppedEvent_hittingAfter_indicator])

/-! ### Expectations -/

/-- **A bound on the supremum gives an e-process** [RRLK, Lemma 3]. An adapted `ℝ≥0∞`-valued
process whose supremum over time has expectation at most `1` under every member of the null is an
e-process: its value at every random time is below its supremum. The converse fails
(`ProbabilityTheory.exists_isEProcess_one_lt_lintegral_iSup`). -/
theorem IsEProcess.of_lintegral_iSup_le_one (hE : Adapted ℱ E)
    (h : ∀ P ∈ S, ∫⁻ ω, ⨆ n, E n ω ∂P ≤ 1) : IsEProcess E ℱ S :=
  .of_lintegral_le_one hE fun _ _ _ _ P hP ↦
    (lintegral_mono fun ω ↦ le_iSup (E · ω) _).trans (h P hP)

/-! ### A martingale that doubles or vanishes -/

/-- The filtration on `Bool` that knows nothing at time `0` and everything afterwards. -/
private def revealFiltration : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq n := if n = 0 then ⊥ else ⊤
  mono' m n hmn := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [Nat.pos_iff_ne_zero.1 hm, Nat.pos_iff_ne_zero.1 (hm.trans_le hmn)]
  le' _ := le_top

/-- The uniform law on `Bool`. -/
private noncomputable def coinLaw : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

private instance : IsProbabilityMeasure coinLaw :=
  ⟨by simp [coinLaw, ENNReal.inv_two_add_inv_two]⟩

/-- The martingale that starts at `1` and, at time `1`, doubles on `true` and vanishes on
`false`. -/
private def doubleOrNothing (n : ℕ) (ω : Bool) : ℝ≥0∞ :=
  if n = 0 then 1 else if ω then 2 else 0

private lemma revealFiltration_zero : revealFiltration 0 = ⊥ := rfl

private lemma revealFiltration_of_ne_zero {n : ℕ} (hn : n ≠ 0) : revealFiltration n = ⊤ :=
  ite_eq_right_iff.2 fun h ↦ absurd h hn

private lemma lintegral_coinLaw (f : Bool → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂coinLaw = 2⁻¹ * (f true + f false) := by
  simp [coinLaw, lintegral_add_measure, mul_add]

private lemma isEProcess_doubleOrNothing :
    IsEProcess doubleOrNothing revealFiltration {coinLaw} := by
  refine .of_lintegral_le_one (fun n ↦ ?_) fun τ hτ N hτN P hP ↦ ?_
  · rcases eq_or_ne n 0 with rfl | hn
    · have h_const : doubleOrNothing 0 = fun _ ↦ 1 := by ext; simp [doubleOrNothing]
      rw [h_const]
      exact measurable_const
    · rw [revealFiltration_of_ne_zero hn]
      exact measurable_from_top
  rw [mem_singleton_iff.1 hP, lintegral_coinLaw]
  -- the event `{τ = 0}` is known at time `0`, hence empty or everything
  have h0 := hτ 0
  rw [revealFiltration_zero, MeasurableSpace.measurableSet_bot_iff] at h0
  rcases h0 with h0 | h0
  · -- `τ ≥ 1` everywhere: the martingale is read at time `1` or later
    have hτ1 (ω : Bool) : (τ ω).untopA ≠ 0 := fun h ↦ eq_empty_iff_forall_notMem.1 h0 ω (by
      rw [mem_ofPred_eq, ← WithTop.natCast_untopA
        (WithTop.ne_top_of_le_natCast (hτN ω)), h]
      simp)
    simp [stoppedValue, doubleOrNothing, hτ1]
  · -- `τ = 0` everywhere: the martingale is read at time `0`
    have hτ0 (ω : Bool) : τ ω = 0 := by simpa using h0.ge (mem_univ ω)
    have h0 : (0 : WithTop ℕ).untopA = 0 := by simp
    simp [stoppedValue, doubleOrNothing, hτ0, h0, ← two_mul]

/-- The running maximum of the martingale at time `1`. -/
private lemma partialSups_one_doubleOrNothing (ω : Bool) :
    partialSups doubleOrNothing 1 ω = if ω then 2 else 1 := by
  simp only [partialSups_eq_biSup, iSup_apply]
  refine le_antisymm (iSup₂_le fun k hk ↦ ?_) ?_
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl <;> cases ω <;>
      simp [doubleOrNothing]
  · cases ω
    · exact le_iSup₂_of_le 0 zero_le_one (by simp [doubleOrNothing])
    · exact le_iSup₂_of_le 1 le_rfl (by simp [doubleOrNothing])

private lemma one_lt_lintegral_partialSups_one_doubleOrNothing :
    1 < ∫⁻ ω, partialSups doubleOrNothing 1 ω ∂coinLaw := by
  -- the expectation is `2⁻¹ * (2 + 1) = 1 + 2⁻¹`
  simp only [partialSups_one_doubleOrNothing, lintegral_coinLaw, ↓reduceIte, Bool.false_eq_true,
    mul_add, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  exact ENNReal.lt_add_right ENNReal.one_ne_top (by simp)

/-- **Expectations at stopping times do not bound the supremum** [RRLK, Lemma 3]. Some e-process
for a probability measure, the martingale on two points that starts at `1` and then doubles or
vanishes, has a supremum over time of expectation larger than `1`. -/
theorem exists_isEProcess_one_lt_lintegral_iSup :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (E : ℕ → Ω → ℝ≥0∞),
      IsEProcess E ℱ {P} ∧ 1 < ∫⁻ ω, ⨆ n, E n ω ∂P := by
  refine ⟨Bool, ⊤, revealFiltration, coinLaw, inferInstance, doubleOrNothing,
    isEProcess_doubleOrNothing, one_lt_lintegral_partialSups_one_doubleOrNothing.trans_le ?_⟩
  refine lintegral_mono fun ω ↦ ?_
  simp only [partialSups_eq_biSup, iSup_apply]
  exact iSup₂_le fun k _ ↦ le_iSup (doubleOrNothing · ω) k

/-- **The running maximum of an e-process need not be an e-process** [RRLK, Remark 16]. For the
martingale on two points that starts at `1` and then doubles or vanishes, the running maximum has
expectation `3 / 2` at time `1`. -/
theorem exists_isEProcess_not_isEProcess_partialSups :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (ℱ : Filtration ℕ mΩ) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (E : ℕ → Ω → ℝ≥0∞),
      IsEProcess E ℱ {P} ∧ ¬ IsEProcess (partialSups E) ℱ {P} :=
  ⟨Bool, ⊤, revealFiltration, coinLaw, inferInstance, doubleOrNothing,
    isEProcess_doubleOrNothing, fun h ↦ (h.isEVar 1).lintegral_le_one (mem_singleton _) |>.not_gt
      one_lt_lintegral_partialSups_one_doubleOrNothing⟩

end ProbabilityTheory
