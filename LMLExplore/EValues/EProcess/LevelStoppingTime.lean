/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.SequentialTest

/-!
# Sequential tests as stopping times

A level-`α` sequential test for a null hypothesis `S : Set (Measure Ω)` and a filtration `ℱ`
indexed by `ℕ` can be presented as a stopping time `τ : Ω → WithTop ℕ`, the time at which the
null is rejected, with `τ = ⊤` when it never is: its level is the bound `P {τ < ⊤} ≤ α` for every
member `P` of the null. Its power against a measure `Q` is `Q {τ < ⊤}`, it has power one against
`Q` when `τ < ⊤` holds `Q`-almost surely, and its expected number of observations under `Q` is
`∫⁻ ω, ENat.toENNReal (τ ω) ∂Q`. This is the form in which the lower bounds on the expected number
of observations of sequential tests, and the characterizations of the nulls and alternatives
against which tests of power one exist, are stated.

This file relates it to the other instruments of anytime-valid inference
(`ProbabilityTheory.IsSequentialTest`, `ProbabilityTheory.IsPProcess`,
`ProbabilityTheory.IsEProcess`). A stopping time `τ` is a level-`α` sequential test exactly when
the adapted `{0, 1}`-valued process `𝟙{τ ≤ n}`, which rejects from time `τ` on, is a level-`α`
sequential test in the sense of `IsSequentialTest`; conversely the rejection events of a
`{0, 1}`-valued sequential test `φ` are those of the first time `hittingAfter φ {1} 0` at which it
rejects, and the first rejection time of `𝟙{τ ≤ n}` is `τ`
(`MeasureTheory.hittingAfter_indicator_setOf_le_apply`). For every null, the first time an
e-process reaches `α⁻¹` is a level-`α` sequential test, at every level `α`, `0` included, by
Ville's inequality for e-processes; for `α ≠ ∞` every level-`α` sequential test is of this
form, with the e-process `α⁻¹ * 𝟙{τ ≤ n}` [RW, Proposition 7.8]. The
first time a p-process is at most `α` is a level-`α` sequential test [RRLK, Proposition 11]. The
minimum of two sequential tests for one null is a sequential test at the sum of their levels, and
their maximum is a sequential test for the union of their nulls at the common level.

The filtration is arbitrary, and the null has no dominating measure. The null is an arbitrary set
of measures in the definition, its order properties, its correspondence with `IsSequentialTest`
and the thresholding of p-processes; the results on e-processes assume that every member of the
null is a probability measure.

## Main definitions

* `ProbabilityTheory.IsLevelStoppingTime τ ℱ S α`: `τ` is a level-`α` sequential test, as a
  stopping time, for the null `S` and the filtration `ℱ`.

## Main statements

* `ProbabilityTheory.isLevelStoppingTime_iff_isSequentialTest`: `τ` is a level-`α` sequential
  test exactly when the process `𝟙{τ ≤ n}` is one in the sense of `IsSequentialTest`.
* `ProbabilityTheory.isSequentialTest_iff_isLevelStoppingTime_hittingAfter`: a `{0, 1}`-valued
  adapted process is a level-`α` sequential test exactly when its first rejection time is one.
* `ProbabilityTheory.IsEProcess.isLevelStoppingTime_hittingAfter`: the first time an e-process
  reaches `α⁻¹` is a level-`α` sequential test [RW, Fact 7.6].
* `ProbabilityTheory.isLevelStoppingTime_iff_exists_isEProcess`: for `α ≠ ∞`, the level-`α`
  sequential tests are the first times at which e-processes reach `α⁻¹` [RW, Proposition 7.8].
* `ProbabilityTheory.IsEProcess.exists_isLevelStoppingTime_ae_lt_top`: an e-process that is
  unbounded almost surely under every alternative gives, at every level `α ≠ 0`, a sequential
  test with power one against them.
* `ProbabilityTheory.IsPProcess.isLevelStoppingTime_hittingAfter`: the first time a p-process is
  at most `α` is a level-`α` sequential test [RRLK, Proposition 11 (1)].

## Implementation notes

The definition and `ProbabilityTheory.IsEProcess.isLevelStoppingTime_hittingAfter` are adapted
from `notes/book/Suggested.lean` (commit `88fb487`) in the paper project
`RemyDegenne/evalues_research`.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, §7.3, Fact 7.6 and Proposition 7.8.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, §4.1 and Proposition 11.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝒢 ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {τ σ : Ω → WithTop ℕ} {p E φ : ℕ → Ω → ℝ≥0∞} {α β : ℝ≥0∞}

/-- `τ : Ω → WithTop ℕ` is a **level-`α` sequential test**, as a stopping time, for the null `S`
and the filtration `ℱ`: it is a stopping time, the time at which the null is rejected (never when
`τ = ⊤`), and under every member of the null it is finite with probability at most `α`. -/
structure IsLevelStoppingTime (τ : Ω → WithTop ℕ) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω))
    (α : ℝ≥0∞) : Prop where
  isStoppingTime : IsStoppingTime ℱ τ
  measure_lt_top_le : ∀ P ∈ S, P {ω | τ ω < ⊤} ≤ α

namespace IsLevelStoppingTime

/-- A level-`α` sequential test for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hτ : IsLevelStoppingTime τ ℱ T α) :
    IsLevelStoppingTime τ ℱ S α :=
  ⟨hτ.isStoppingTime, fun P hP ↦ hτ.measure_lt_top_le P (hST hP)⟩

/-- A level-`α` sequential test is a level-`β` sequential test for every `β ≥ α`. -/
theorem mono (hτ : IsLevelStoppingTime τ ℱ S α) (hαβ : α ≤ β) : IsLevelStoppingTime τ ℱ S β :=
  ⟨hτ.isStoppingTime, fun P hP ↦ (hτ.measure_lt_top_le P hP).trans hαβ⟩

/-- A level-`α` sequential test for a filtration `𝒢` is one for every finer filtration `ℱ`. -/
theorem mono_filtration (hτ : IsLevelStoppingTime τ 𝒢 S α) (h𝒢ℱ : 𝒢 ≤ ℱ) :
    IsLevelStoppingTime τ ℱ S α :=
  ⟨fun n ↦ h𝒢ℱ n _ (hτ.isStoppingTime n), hτ.measure_lt_top_le⟩

/-- **Bonferroni's correction for sequential tests.** Rejecting as soon as one of two sequential
tests of levels `α` and `β` rejects is a sequential test of level `α + β`. -/
protected theorem min (hτ : IsLevelStoppingTime τ ℱ S α) (hσ : IsLevelStoppingTime σ ℱ S β) :
    IsLevelStoppingTime (fun ω ↦ min (τ ω) (σ ω)) ℱ S (α + β) where
  isStoppingTime := hτ.isStoppingTime.min hσ.isStoppingTime
  measure_lt_top_le P hP := by
    have h_union : {ω | min (τ ω) (σ ω) < ⊤} = {ω | τ ω < ⊤} ∪ {ω | σ ω < ⊤} := by
      ext ω
      simp [min_lt_iff]
    rw [h_union]
    exact (measure_union_le _ _).trans
      (add_le_add (hτ.measure_lt_top_le P hP) (hσ.measure_lt_top_le P hP))

/-- **The intersection-union principle for sequential tests.** Rejecting once two level-`α`
sequential tests, for the nulls `S` and `T`, have both rejected is a level-`α` sequential test for
the null `S ∪ T`. -/
protected theorem max (hτ : IsLevelStoppingTime τ ℱ S α) (hσ : IsLevelStoppingTime σ ℱ T α) :
    IsLevelStoppingTime (fun ω ↦ max (τ ω) (σ ω)) ℱ (S ∪ T) α where
  isStoppingTime := hτ.isStoppingTime.max hσ.isStoppingTime
  measure_lt_top_le P hP := by
    -- both tests reject where their maximum does
    have h_sub : {ω | max (τ ω) (σ ω) < ⊤} ⊆ {ω | τ ω < ⊤} ∩ {ω | σ ω < ⊤} :=
      fun ω hω ↦ by simpa using hω
    rcases hP with hP | hP
    · exact (measure_mono (h_sub.trans inter_subset_left)).trans (hτ.measure_lt_top_le P hP)
    · exact (measure_mono (h_sub.trans inter_subset_right)).trans (hσ.measure_lt_top_le P hP)

end IsLevelStoppingTime

/-! ### Stopping times and adapted sequential tests -/

/-- **A stopping time as an adapted sequential test.** A random time `τ : Ω → WithTop ℕ` is a
level-`α` sequential test exactly when the process `𝟙{τ ≤ n}`, which rejects from time `τ` on, is
a level-`α` sequential test in the sense of `ProbabilityTheory.IsSequentialTest`. -/
theorem isLevelStoppingTime_iff_isSequentialTest :
    IsLevelStoppingTime τ ℱ S α ↔
      IsSequentialTest (fun n ↦ {ω | τ ω ≤ n}.indicator 1) ℱ S α := by
  -- the process `𝟙{τ ≤ n}` rejects at some time exactly where `τ` is finite
  have h_rej : {ω | ∃ n : ℕ, {ω | τ ω ≤ n}.indicator (1 : Ω → ℝ≥0∞) ω = 1} = {ω | τ ω < ⊤} := by
    ext ω
    simp only [mem_ofPred_eq]
    cases h : τ ω
    · simp [indicator, h]
    · simpa [indicator, h] using ⟨_, le_rfl⟩
  refine ⟨fun hτ ↦ ⟨fun n ↦
    measurable_const.indicator (hτ.isStoppingTime.measurableSet_le_natCast n), fun n ω ↦ ?_,
    fun P hP ↦ h_rej ▸ hτ.measure_lt_top_le P hP⟩,
    fun hφ ↦ ⟨fun n ↦ ?_, fun P hP ↦ h_rej ▸ hφ.measure_exists_eq_one_le P hP⟩⟩
  · by_cases h : τ ω ≤ n <;> simp [h]
  · -- `{τ ≤ n}` is the event where the `ℱ n`-measurable indicator equals `1`
    have h_eq : {ω | τ ω ≤ n} = {ω | τ ω ≤ n}.indicator (1 : Ω → ℝ≥0∞) ⁻¹' {1} := by
      ext ω
      by_cases h : τ ω ≤ n <;> simp [h]
    rw [← Nat.cast_withTop, h_eq]
    exact hφ.adapted n (measurableSet_singleton 1)

/-- A level-`α` sequential test `τ` gives the adapted level-`α` sequential test `𝟙{τ ≤ n}`. -/
theorem IsLevelStoppingTime.isSequentialTest (hτ : IsLevelStoppingTime τ ℱ S α) :
    IsSequentialTest (fun n ↦ {ω | τ ω ≤ n}.indicator 1) ℱ S α :=
  isLevelStoppingTime_iff_isSequentialTest.1 hτ

/-- **The first rejection time of a sequential test.** A `{0, 1}`-valued adapted process `φ` is a
level-`α` sequential test exactly when the first time `hittingAfter φ {1} 0` at which it rejects is
a level-`α` sequential test, as a stopping time: both reject on the same event. -/
theorem isSequentialTest_iff_isLevelStoppingTime_hittingAfter (hφ : Adapted ℱ φ)
    (h01 : ∀ n ω, φ n ω = 0 ∨ φ n ω = 1) :
    IsSequentialTest φ ℱ S α ↔ IsLevelStoppingTime (hittingAfter φ {1} 0) ℱ S α := by
  have h_lt_top : {ω | hittingAfter φ {1} 0 ω < ⊤} = {ω | ∃ n, φ n ω = 1} := by
    ext ω
    simp [hittingAfter_lt_top_iff]
  refine ⟨fun h ↦ ⟨hφ.isStoppingTime_hittingAfter (measurableSet_singleton 1), ?_⟩,
    fun h ↦ ⟨hφ, h01, ?_⟩⟩
  · simpa only [h_lt_top] using h.measure_exists_eq_one_le
  · simpa only [h_lt_top] using h.measure_lt_top_le

/-- The first time at which a level-`α` sequential test `φ` rejects is a level-`α` sequential
test, as a stopping time. -/
theorem IsSequentialTest.isLevelStoppingTime_hittingAfter (hφ : IsSequentialTest φ ℱ S α) :
    IsLevelStoppingTime (hittingAfter φ {1} 0) ℱ S α :=
  (isSequentialTest_iff_isLevelStoppingTime_hittingAfter hφ.adapted hφ.eq_zero_or_eq_one).1 hφ

/-! ### Sequential tests from e-processes and p-processes -/

/-- **Thresholding an e-process** [RW, Fact 7.6]. The first time an e-process reaches `α⁻¹` is a
level-`α` sequential test, at every level `α`, `0` included: this is Ville's inequality for
e-processes, through the p-process `E⁻¹`. -/
theorem IsEProcess.isLevelStoppingTime_hittingAfter (hE : IsEProcess E ℱ S) (α : ℝ≥0∞) :
    IsLevelStoppingTime (hittingAfter E (Ici α⁻¹) 0) ℱ S α where
  isStoppingTime := hE.adapted.isStoppingTime_hittingAfter measurableSet_Ici
  measure_lt_top_le P hP := by
    simpa [hittingAfter_lt_top_iff, ENNReal.inv_le_iff_inv_le] using
      hE.isPProcess_inv.measure_exists_le_le hP α

/-- **The e-process of a sequential test** [RW, Proposition 7.8]. A level-`α` sequential test `τ`
gives the e-process `α⁻¹ * 𝟙{τ ≤ n}`. -/
theorem IsLevelStoppingTime.isEProcess_inv_mul_indicator (hτ : IsLevelStoppingTime τ ℱ S α) :
    IsEProcess (fun n ω ↦ α⁻¹ * {ω | τ ω ≤ n}.indicator 1 ω) ℱ S :=
  hτ.isSequentialTest.isEProcess_inv_mul

/-- **Sequential tests are thresholded e-processes** [RW, Proposition 7.8 and Fact 7.6]. For a
level `α ≠ ∞`, a random time is a level-`α` sequential test exactly when it is the first time some
e-process reaches `α⁻¹`. -/
theorem isLevelStoppingTime_iff_exists_isEProcess (hα : α ≠ ∞) :
    IsLevelStoppingTime τ ℱ S α ↔ ∃ E, IsEProcess E ℱ S ∧ τ = hittingAfter E (Ici α⁻¹) 0 := by
  refine ⟨fun hτ ↦ ⟨_, hτ.isEProcess_inv_mul_indicator, ?_⟩, fun ⟨E, hE, hτE⟩ ↦
    hτE ▸ hE.isLevelStoppingTime_hittingAfter α⟩
  -- `α⁻¹ * 𝟙{τ ≤ n}` reaches `α⁻¹` exactly from time `τ` on, since `α⁻¹ ≠ 0`
  ext1 ω
  refine (hittingAfter_apply_eq_of_forall_mem_iff (by simp) fun n _ ↦ ?_).symm
  by_cases h : τ ω ≤ n <;> simp [h, hα]

/-- **Power one from an unbounded e-process.** For a level `α ≠ 0`, the first time an e-process
reaches `α⁻¹` is a level-`α` sequential test that is finite almost surely under every measure under
which the e-process is almost surely unbounded. -/
theorem IsEProcess.exists_isLevelStoppingTime_ae_lt_top (hE : IsEProcess E ℱ S) (hα : α ≠ 0) :
    ∃ τ, IsLevelStoppingTime τ ℱ S α ∧
      ∀ Q : Measure Ω, (∀ᵐ ω ∂Q, ⨆ n, E n ω = ∞) → ∀ᵐ ω ∂Q, τ ω < ⊤ := by
  refine ⟨_, hE.isLevelStoppingTime_hittingAfter α, fun Q hQ ↦ ?_⟩
  filter_upwards [hQ] with ω hω
  -- the threshold `α⁻¹` is finite, so it is exceeded by some value of the unbounded process
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 (hω ▸ ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hα))
  exact hittingAfter_lt_top_iff.2 ⟨n, Nat.zero_le n, mem_Ici.2 hn.le⟩

/-- **Thresholding a p-process** [RRLK, Proposition 11 (1)]. The first time a p-process is at
most `α` is a level-`α` sequential test. -/
theorem IsPProcess.isLevelStoppingTime_hittingAfter (hp : IsPProcess p ℱ S) (α : ℝ≥0∞) :
    IsLevelStoppingTime (hittingAfter p (Iic α) 0) ℱ S α where
  isStoppingTime := hp.adapted.isStoppingTime_hittingAfter measurableSet_Iic
  measure_lt_top_le P hP := by
    simpa [hittingAfter_lt_top_iff] using hp.measure_exists_le_le hP α

end ProbabilityTheory
