/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import LMLExplore.Probability.Martingale.ExactVille
public import LMLExplore.Probability.Martingale.SnellEnvelope

/-!
# E-processes

An e-process for a null hypothesis `S : Set (Measure Ω)` and a filtration `ℱ` indexed by `ℕ` is an
adapted `ℝ≥0∞`-valued process `E` whose value `fun ω ↦ E (τ ω) ω` at every stopping time `τ` with
values in `ℕ` is an e-variable for `S` (Statlib's `ProbabilityTheory.IsEVar`)
[RW, Definition 7.3 (ii)]. A statistician who monitors `E` and stops at a data-dependent time
still holds an e-value: e-processes are the sequential, anytime-valid form of e-variables. The
null is an arbitrary set of measures, with no dominating measure, and the filtration is
arbitrary. [RW] also allows stopping times that never stop; validity at the stopping times with
values in `ℕ` is the form used here.

Every test supermartingale for a null of measures of mass at most one is an e-process, by optional
stopping (`ProbabilityTheory.IsTestSupermartingale.isEVar_stoppedValueLimsup`), but not
conversely. This file also proves the closure properties of e-processes that follow from those of
e-variables at each stopping time: restricting the null, passing to an adapted process that is
almost surely equal or almost surely smaller, and convex combinations.

The converse holds one member of the null at a time [RRLK, Lemma 6]: an adapted process is an
e-process exactly when, under every member `P` of the null, it is `P`-almost surely dominated by a
test supermartingale for `P`, or equivalently by a test martingale for `P`. The test
supermartingale is the Snell envelope of the process under `P`
(`ProbabilityTheory.snellEnvelope`), and the test martingale is its martingale part
(`ProbabilityTheory.IsTestSupermartingale.exists_isTestMartingale_ge`). Validity at the stopping
times with values in `ℕ` is then equivalent to validity at the bounded ones, and to validity at
the stopping times with values in `WithTop ℕ`, with the `limsup` or the `liminf` of the process
where the stopping time is infinite: the definition does not depend on the convention at infinity.
Through the domination, Ville's inequality for test supermartingales gives Ville's inequality for
e-processes, so that thresholding an e-process at `α⁻¹` is a level-`α` sequential test.

## Main definitions

* `ProbabilityTheory.IsEProcess E ℱ S`: `E` is an e-process for the null `S` and the filtration
  `ℱ`.

## Main statements

* `ProbabilityTheory.IsEProcess.isEVar`: the value of an e-process at every fixed time is an
  e-variable.
* `ProbabilityTheory.IsEProcess.lintegral_le_one`: under every member of the null, an e-process has
  expectation at most `1` at every stopping time with values in `ℕ`.
* `ProbabilityTheory.isEProcess_iff_lintegral_le_one`,
  `ProbabilityTheory.IsEProcess.of_lintegral_le_one`: an adapted process is an e-process exactly
  when it has expectation at most `1` at every stopping time with values in `ℕ`, under every
  member of the null.
* `ProbabilityTheory.IsEProcess.anti_set`, `ProbabilityTheory.isEProcess_iff_forall_singleton`: an
  e-process for `S` is one for every subset of `S`, and an adapted process is an e-process for `S`
  exactly when it is one for each simple null `{P}` with `P ∈ S`.
* `ProbabilityTheory.IsEProcess.mono_ae`, `ProbabilityTheory.IsEProcess.mono`: an adapted process
  dominated by an e-process, almost surely under every member of the null or pointwise, is an
  e-process.
* `ProbabilityTheory.isEProcess_one`, `ProbabilityTheory.convex_isEProcess`: the constant process
  `1` is an e-process for a null of measures of mass at most `1`, and the e-processes for a null
  form a convex set.
* `ProbabilityTheory.IsTestSupermartingale.isEProcess`: a test supermartingale for a null of
  measures of mass at most one is an e-process [RW, Fact 7.5].
* `ProbabilityTheory.IsEProcess.shift`, `ProbabilityTheory.isEProcess_shift_iff`: for filtrations
  with `𝒢 0 = ⊥` and `𝒢 (n + 1) = ℱ n`, such as `Filtration.piLT` and `Filtration.piLE`, and a
  null of measures of mass at most `1`, a process `E` with `E 0 = 1` is an e-process for `𝒢`
  exactly when its shift `fun n ↦ E (n + 1)` is one for `ℱ`.
* `ProbabilityTheory.isEProcess_tfae`: the characterization of e-processes [RRLK, Lemma 6].
* `ProbabilityTheory.isEProcess_iff_forall_exists_isTestSupermartingale`,
  `ProbabilityTheory.isEProcess_iff_forall_exists_isTestMartingale`: for a null of probability
  measures, an adapted process is an e-process exactly when it is dominated by a test
  supermartingale, or by a test martingale, under each member of the null.
* `ProbabilityTheory.IsEProcess.exists_isTestSupermartingale_ae_le`,
  `ProbabilityTheory.IsEProcess.exists_isTestMartingale_ae_le`: an e-process is dominated by a
  test supermartingale and by a test martingale under each member of the null.
* `ProbabilityTheory.IsEProcess.isEVar_stoppedValueLimsup`: the value of an e-process at every
  stopping time with values in `WithTop ℕ` is an e-variable.
* `ProbabilityTheory.IsEProcess.measure_exists_le_le`,
  `ProbabilityTheory.IsEProcess.measure_exists_inv_le_le`,
  `ProbabilityTheory.IsEProcess.measure_inv_le_stoppedValueLimsup_le`: Ville's inequality for
  e-processes, uniformly over time and at a stopping time.

## Implementation notes

The definition and its closure properties are adapted from
`EValuesResearch/ForLMLExplore/EValues/EProcess.lean` (commit `d2da7b7`) in the paper project
`RemyDegenne/evalues_research` (same author), which also fixes the field name
`isEVar_stoppedValue`.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, Lemma 6 and Appendix A.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {E F : ℕ → Ω → ℝ≥0∞} {τ : Ω → ℕ}

/-- `E : ℕ → Ω → ℝ≥0∞` is an **e-process** for the null `S` and the filtration `ℱ`: it is adapted
and, for every stopping time `τ` with values in `ℕ`, its value `fun ω ↦ E (τ ω) ω` at `τ` is an
e-variable for `S` [RW, Definition 7.3 (ii)]. -/
structure IsEProcess (E : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) : Prop where
  adapted : Adapted ℱ E
  isEVar_stoppedValue : ∀ τ : Ω → ℕ, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) →
    IsEVar (fun ω ↦ E (τ ω) ω) S

namespace IsEProcess

/-- Each value of an e-process is measurable. -/
theorem measurable (hE : IsEProcess E ℱ S) (n : ℕ) : Measurable (E n) :=
  hE.adapted.measurable

/-- The value of an e-process at every fixed time is an e-variable. -/
theorem isEVar (hE : IsEProcess E ℱ S) (n : ℕ) : IsEVar (E n) S :=
  hE.isEVar_stoppedValue (fun _ ↦ n) (isStoppingTime_natCast n)

/-- Under every member of the null, an e-process has expectation at most `1` at every stopping
time with values in `ℕ`. -/
theorem lintegral_le_one (hE : IsEProcess E ℱ S)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ))) (hP : P ∈ S) :
    ∫⁻ ω, E (τ ω) ω ∂P ≤ 1 :=
  (hE.isEVar_stoppedValue τ hτ).lintegral_le_one hP

/-- The value `fun ω ↦ E (τ ω) ω` of an e-process at a stopping time with values in `ℕ` is
measurable. -/
theorem measurable_stoppedValue (hE : IsEProcess E ℱ S)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ))) : Measurable fun ω ↦ E (τ ω) ω :=
  hE.adapted.measurable_apply_stoppingTime hτ

/-- An adapted process with expectation at most `1` at every stopping time with values in `ℕ`,
under every member of the null, is an e-process. -/
theorem of_lintegral_le_one (hE : Adapted ℱ E)
    (h : ∀ τ : Ω → ℕ, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) →
      ∀ P ∈ S, ∫⁻ ω, E (τ ω) ω ∂P ≤ 1) :
    IsEProcess E ℱ S :=
  ⟨hE, fun τ hτ ↦ ⟨hE.measurable_apply_stoppingTime hτ, h τ hτ⟩⟩

/-- An e-process for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hE : IsEProcess E ℱ T) : IsEProcess E ℱ S :=
  ⟨hE.adapted, fun τ hτ ↦ (hE.isEVar_stoppedValue τ hτ).anti_set hST⟩

/-- An adapted process equal to an e-process at every time, almost surely under every member of the
null, is an e-process. -/
theorem congr (hE : IsEProcess E ℱ S) (hF : Adapted ℱ F) (hEF : ∀ P ∈ S, ∀ n, E n =ᵐ[P] F n) :
    IsEProcess F ℱ S :=
  ⟨hF, fun τ hτ ↦ (hE.isEVar_stoppedValue τ hτ).congr (hF.measurable_apply_stoppingTime hτ)
    fun P hP ↦ by filter_upwards [ae_all_iff.2 (hEF P hP)] with ω hω using hω (τ ω)⟩

/-- **Domination.** An adapted process that is almost surely at most an e-process at every time,
under every member of the null, is an e-process. -/
theorem mono_ae (hE : IsEProcess E ℱ S) (hF : Adapted ℱ F) (hFE : ∀ P ∈ S, ∀ n, F n ≤ᵐ[P] E n) :
    IsEProcess F ℱ S := by
  refine ⟨hF, fun τ hτ ↦ ⟨hF.measurable_apply_stoppingTime hτ, fun P hP ↦ ?_⟩⟩
  refine (lintegral_mono_ae ?_).trans ((hE.isEVar_stoppedValue τ hτ).lintegral_le_one hP)
  filter_upwards [ae_all_iff.2 (hFE P hP)] with ω hω using hω (τ ω)

/-- **Domination.** An adapted process that is at most an e-process is an e-process. -/
theorem mono (hE : IsEProcess E ℱ S) (hF : Adapted ℱ F) (hFE : F ≤ E) : IsEProcess F ℱ S :=
  hE.mono_ae hF fun _ _ n ↦ ae_of_all _ (hFE n)

end IsEProcess

/-- A process is an e-process exactly when it is adapted and has expectation at most `1` at every
stopping time with values in `ℕ`, under every member of the null. -/
theorem isEProcess_iff_lintegral_le_one :
    IsEProcess E ℱ S ↔ Adapted ℱ E ∧ ∀ τ : Ω → ℕ, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) →
      ∀ P ∈ S, ∫⁻ ω, E (τ ω) ω ∂P ≤ 1 :=
  ⟨fun hE ↦ ⟨hE.adapted, fun _ hτ _ hP ↦ hE.lintegral_le_one hτ hP⟩,
    fun h ↦ .of_lintegral_le_one h.1 h.2⟩

/-- A process is an e-process for `S` exactly when it is adapted and an e-process for each simple
null `{P}` with `P ∈ S`. Adaptedness is needed only when `S` is empty. -/
theorem isEProcess_iff_forall_singleton :
    IsEProcess E ℱ S ↔ Adapted ℱ E ∧ ∀ P ∈ S, IsEProcess E ℱ {P} := by
  refine ⟨fun hE ↦ ⟨hE.adapted, fun P hP ↦ hE.anti_set (singleton_subset_iff.2 hP)⟩,
    fun ⟨hE, h⟩ ↦ ⟨hE, fun τ hτ ↦ ⟨hE.measurable_apply_stoppingTime hτ, fun P hP ↦
      ((h P hP).isEVar_stoppedValue τ hτ).lintegral_le_one (mem_singleton P)⟩⟩⟩

/-- The constant process `1` is an e-process for every null of measures of mass at most `1` and
every filtration. -/
theorem isEProcess_one (ℱ : Filtration ℕ mΩ) (hS : ∀ P ∈ S, P univ ≤ 1) : IsEProcess 1 ℱ S :=
  ⟨fun _ ↦ measurable_const, fun _ _ ↦ isEVar_one hS⟩

/-- The e-processes for a null form a convex set: a convex combination `a • E + b • F`, with
`a + b = 1`, of two e-processes is an e-process. -/
theorem convex_isEProcess (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Convex ℝ≥0∞ {E : ℕ → Ω → ℝ≥0∞ | IsEProcess E ℱ S} := by
  intro E hE F hF a b ha hb hab
  exact ⟨fun n ↦ ((hE.adapted n).const_smul a).add ((hF.adapted n).const_smul b), fun τ hτ ↦
    convex_isEVar S (hE.isEVar_stoppedValue τ hτ) (hF.isEVar_stoppedValue τ hτ) ha hb hab⟩

/-- **Test supermartingales are e-processes** [RW, Fact 7.5]. By optional stopping, a test
supermartingale for a null of measures of mass at most one has expectation at most `1` at every
stopping time, so it is an e-process. -/
theorem IsTestSupermartingale.isEProcess (hS : ∀ P ∈ S, P univ ≤ 1)
    {M : ℕ → Ω → ℝ≥0∞} (hM : IsTestSupermartingale M ℱ S) : IsEProcess M ℱ S :=
  ⟨hM.adapted, fun τ hτ ↦ by simpa using hM.isEVar_stoppedValueLimsup hS hτ⟩

/-! ### Shifting time by one

As for test supermartingales (`ProbabilityTheory.isTestSupermartingale_shift_iff`), e-processes
for two filtrations with `𝒢 (n + 1) = ℱ n`, such as `Filtration.piLT` and `Filtration.piLE`,
correspond through the shift `fun n ↦ E (n + 1)`. -/

section Shift

variable {𝒢 : Filtration ℕ mΩ}

/-- The shift `fun n ↦ E (n + 1)` of an e-process for `𝒢` is an e-process for any filtration `ℱ`
with `𝒢 (n + 1) = ℱ n`: a stopping time `τ` of `ℱ` gives the stopping time `τ + 1` of `𝒢`. -/
theorem IsEProcess.shift (hE : IsEProcess E 𝒢 S) (h : ∀ n, 𝒢 (n + 1) = ℱ n) :
    IsEProcess (fun n ↦ E (n + 1)) ℱ S where
  adapted := hE.adapted.shift h
  isEVar_stoppedValue τ hτ :=
    hE.isEVar_stoppedValue (fun ω ↦ τ ω + 1) ((isStoppingTime_natCast_add_one_iff h).2 hτ)

/-- For filtrations with `𝒢 0 = ⊥` and `𝒢 (n + 1) = ℱ n`, such as `Filtration.piLT` and
`Filtration.piLE`, and a null of measures of mass at most `1`, a process `E` that starts at `1` is
an e-process for `𝒢` exactly when its shift `fun n ↦ E (n + 1)` is one for `ℱ`. -/
theorem isEProcess_shift_iff (h₀ : 𝒢 0 = ⊥) (h : ∀ n, 𝒢 (n + 1) = ℱ n)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hE₀ : E 0 = 1) :
    IsEProcess (fun n ↦ E (n + 1)) ℱ S ↔ IsEProcess E 𝒢 S := by
  refine ⟨fun hE ↦ ⟨?_, fun τ hτ ↦ ?_⟩, fun hE ↦ hE.shift h⟩
  · exact (adapted_shift_iff h (hE₀ ▸ measurable_const)).1 hE.adapted
  -- the event `{τ = 0}` is known at time `0`, so `τ` is `0` everywhere or nowhere
  have h0 := hτ.measurableSet_le_natCast 0
  rw [h₀, MeasurableSpace.measurableSet_bot_iff] at h0
  rcases h0 with h0 | h0
  · -- `τ` is positive, and `τ - 1` is a stopping time of `ℱ`
    have hτ1 (ω : Ω) : τ ω - 1 + 1 = τ ω := by
      have hω : ω ∉ {ω | (τ ω : WithTop ℕ) ≤ (0 : ℕ)} := h0 ▸ notMem_empty ω
      simp only [mem_ofPred_eq, Nat.cast_le, nonpos_iff_eq_zero] at hω
      omega
    have hσ : IsStoppingTime ℱ fun ω ↦ ((τ ω - 1 : ℕ) : WithTop ℕ) :=
      (isStoppingTime_natCast_add_one_iff h).1 (by simpa only [hτ1] using hτ)
    simpa only [hτ1] using hE.isEVar_stoppedValue _ hσ
  · have hτ0 (ω : Ω) : τ ω = 0 := by
      have hω : ω ∈ {ω | (τ ω : WithTop ℕ) ≤ (0 : ℕ)} := h0 ▸ mem_univ ω
      simpa only [mem_ofPred_eq, Nat.cast_le, nonpos_iff_eq_zero] using hω
    simp only [hτ0, hE₀]
    exact isEVar_one hS

end Shift

/-! ### The characterization of e-processes -/

/-- Under a probability measure `P`, an adapted process with expectation at most `1` at every
bounded stopping time is `P`-almost surely dominated by a test supermartingale for `P`, its Snell
envelope. -/
private theorem exists_isTestSupermartingale_ae_le_of_lintegral_le_one [IsProbabilityMeasure P]
    (hE : Adapted ℱ E) (h : ∀ τ ∈ boundedStoppingTimesFrom ℱ 0, ∫⁻ ω, E (τ ω) ω ∂P ≤ 1) :
    ∃ M, IsTestSupermartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n :=
  ⟨snellEnvelope E ℱ P, isTestSupermartingale_snellEnvelope h, ae_le_snellEnvelope hE⟩

/-- Under a probability measure `P`, a process that is `P`-almost surely dominated by a test
supermartingale for `P` is `P`-almost surely dominated by a test martingale for `P`. -/
private theorem exists_isTestMartingale_ae_le_of_isTestSupermartingale [IsProbabilityMeasure P]
    (h : ∃ M, IsTestSupermartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n) :
    ∃ M, IsTestMartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n := by
  obtain ⟨M, hM, hEM⟩ := h
  obtain ⟨M', hM', -, hMM'⟩ := hM.exists_isTestMartingale_ge (mem_singleton P)
  exact ⟨M', hM', fun n ↦ (hEM n).trans (ae_of_all _ (hMM' n))⟩

/-- **E-processes are dominated by test supermartingales** [RRLK, Lemma 6]. Under every
probability measure `P` of the null, an e-process is `P`-almost surely dominated by a test
supermartingale for `P`: its Snell envelope. -/
theorem IsEProcess.exists_isTestSupermartingale_ae_le (hE : IsEProcess E ℱ S) (hP : P ∈ S)
    [IsProbabilityMeasure P] :
    ∃ M, IsTestSupermartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n :=
  exists_isTestSupermartingale_ae_le_of_lintegral_le_one hE.adapted fun _ hτ ↦
    hE.lintegral_le_one (mem_boundedStoppingTimesFrom_iff.1 hτ).1 hP

/-- **E-processes are dominated by test martingales** [RRLK, Lemma 6]. Under every probability
measure `P` of the null, an e-process is `P`-almost surely dominated by a test martingale for
`P`: the martingale part of its Snell envelope. -/
theorem IsEProcess.exists_isTestMartingale_ae_le (hE : IsEProcess E ℱ S) (hP : P ∈ S)
    [IsProbabilityMeasure P] :
    ∃ M, IsTestMartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n :=
  exists_isTestMartingale_ae_le_of_isTestSupermartingale
    (hE.exists_isTestSupermartingale_ae_le hP)

/-- Under a probability measure `P`, the value at every stopping time with values in `WithTop ℕ`
of a process almost surely dominated by a test supermartingale for `P` has expectation at most
`1`, with the value `limsup` where the stopping time is infinite. -/
private theorem lintegral_stoppedValueLimsup_le_one_of_ae_le [IsProbabilityMeasure P]
    {M : ℕ → Ω → ℝ≥0∞} (hM : IsTestSupermartingale M ℱ {P}) (hEM : ∀ n, E n ≤ᵐ[P] M n)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    ∫⁻ ω, stoppedValueLimsup E τ ω ∂P ≤ 1 := by
  refine (lintegral_mono_ae ?_).trans
    (hM.lintegral_stoppedValueLimsup_le_one (mem_singleton P) hτ)
  filter_upwards [ae_all_iff.2 hEM] with ω hω using stoppedValueLimsup_mono hω

/-- **The characterization of e-processes** [RRLK, Lemma 6]. For a null of probability measures
and an adapted process `E`, the following are equivalent:
1. `E` is an e-process: its value at every stopping time with values in `ℕ` is an e-variable;
2. `E` has expectation at most `1` at every bounded stopping time, under every member of the null;
3. the same at every stopping time with values in `WithTop ℕ`, with the value
  `stoppedValueLimsup E τ`, the `limsup` of `E` where the stopping time is infinite;
4. the same with the `liminf` of `E` where the stopping time is infinite;
5. under every member `P` of the null, `E` is `P`-almost surely dominated by a test
  supermartingale for `P`;
6. under every member `P` of the null, `E` is `P`-almost surely dominated by a test martingale
  for `P`.

The dominating test (super)martingale may depend on `P`. -/
theorem isEProcess_tfae (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hE : Adapted ℱ E) :
    List.TFAE [IsEProcess E ℱ S,
      ∀ τ ∈ boundedStoppingTimesFrom ℱ 0, ∀ P ∈ S, ∫⁻ ω, E (τ ω) ω ∂P ≤ 1,
      ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → ∀ P ∈ S,
        ∫⁻ ω, stoppedValueLimsup E τ ω ∂P ≤ 1,
      ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → ∀ P ∈ S,
        ∫⁻ ω, (if τ ω = ⊤ then liminf (fun n ↦ E n ω) atTop else stoppedValue E τ ω) ∂P ≤ 1,
      ∀ P ∈ S, ∃ M, IsTestSupermartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n,
      ∀ P ∈ S, ∃ M, IsTestMartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n] := by
  tfae_have 1 → 2 := fun h τ hτ P hP ↦
    h.lintegral_le_one (mem_boundedStoppingTimesFrom_iff.1 hτ).1 hP
  tfae_have 2 → 5 := fun h P hP ↦ have := hS P hP
    exists_isTestSupermartingale_ae_le_of_lintegral_le_one hE fun τ hτ ↦ h τ hτ P hP
  tfae_have 5 → 6 := fun h P hP ↦ have := hS P hP
    exists_isTestMartingale_ae_le_of_isTestSupermartingale (h P hP)
  tfae_have 6 → 5 := fun h P hP ↦ by
    obtain ⟨M, hM, hEM⟩ := h P hP
    exact ⟨M, hM.isTestSupermartingale, hEM⟩
  tfae_have 5 → 3 := fun h τ hτ P hP ↦ by
    obtain ⟨M, hM, hEM⟩ := h P hP
    have := hS P hP
    exact lintegral_stoppedValueLimsup_le_one_of_ae_le hM hEM hτ
  tfae_have 3 → 4 := fun h τ hτ P hP ↦ by
    refine (lintegral_mono fun ω ↦ ?_).trans (h τ hτ P hP)
    -- the `liminf` is below the `limsup` where `τ` is infinite; elsewhere both read `E` at `τ`
    by_cases hτω : τ ω = ⊤
    · rw [ite_eq_left hτω, stoppedValueLimsup_of_eq_top hτω]
      exact liminf_le_limsup
    · rw [ite_eq_right hτω, stoppedValueLimsup_eq_stoppedValue hτω]
  tfae_have 4 → 1 := fun h ↦ .of_lintegral_le_one hE fun τ hτ P hP ↦ by
    refine le_of_eq_of_le (lintegral_congr fun ω ↦ ?_) (h _ hτ P hP)
    -- `↑(τ ω) ≠ ⊤` selects the `stoppedValue` branch, and `stoppedValue E (↑τ) ω` is `E (τ ω) ω`
    -- by definition, since `WithTop.untopA ↑n` reduces to `n` (Mathlib has no simp lemma for it)
    exact (ite_eq_right (WithTop.natCast_ne_top _)).symm
  tfae_finish

/-- **The characterization of e-processes by test supermartingales** [RRLK, Lemma 6]. For a null
of probability measures, an adapted process is an e-process exactly when, under every member `P`
of the null, it is `P`-almost surely dominated by a test supermartingale for `P`. -/
theorem isEProcess_iff_forall_exists_isTestSupermartingale (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : Adapted ℱ E) :
    IsEProcess E ℱ S ↔ ∀ P ∈ S, ∃ M, IsTestSupermartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n :=
  (isEProcess_tfae hS hE).out 1 5

/-- **The characterization of e-processes by test martingales** [RRLK, Lemma 6]. For a null of
probability measures, an adapted process is an e-process exactly when, under every member `P` of
the null, it is `P`-almost surely dominated by a test martingale for `P`. -/
theorem isEProcess_iff_forall_exists_isTestMartingale (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : Adapted ℱ E) :
    IsEProcess E ℱ S ↔ ∀ P ∈ S, ∃ M, IsTestMartingale M ℱ {P} ∧ ∀ n, E n ≤ᵐ[P] M n :=
  (isEProcess_tfae hS hE).out 1 6

/-- The value at every stopping time with values in `WithTop ℕ` of an e-process for a null of
probability measures is an e-variable, with the value `stoppedValueLimsup E τ`, the `limsup` of
`E`, where the stopping time is infinite. -/
theorem IsEProcess.isEVar_stoppedValueLimsup (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : IsEProcess E ℱ S) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    IsEVar (stoppedValueLimsup E τ) S :=
  ⟨measurable_stoppedValueLimsup hE.measurable hτ.measurable',
    fun P hP ↦ by
      have h := ((isEProcess_tfae hS hE.adapted).out 1 3).1 hE
      exact h τ hτ P hP⟩

/-- **Ville's inequality for e-processes**, at level `α` [RW, Fact 7.6]. Under every probability
measure of the null, the sequential test that rejects as soon as an e-process reaches `α⁻¹` has
type I error at most `α`, uniformly over time. -/
theorem IsEProcess.measure_exists_inv_le_le (hE : IsEProcess E ℱ S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (α : ℝ≥0∞) : P {ω | ∃ n, α⁻¹ ≤ E n ω} ≤ α := by
  obtain ⟨M, hM, hEM⟩ := hE.exists_isTestSupermartingale_ae_le hP
  refine (measure_mono_ae ?_).trans (hM.measure_exists_inv_le_le (mem_singleton P) α)
  filter_upwards [ae_all_iff.2 hEM] with ω hω ⟨n, hn⟩ using ⟨n, hn.trans (hω n)⟩

/-- **Ville's inequality for e-processes** [RW, Fact 7.6]. Under every probability measure of the
null, the probability that an e-process ever reaches a level `c` is at most `c⁻¹`. -/
theorem IsEProcess.measure_exists_le_le (hE : IsEProcess E ℱ S) (hP : P ∈ S)
    [IsProbabilityMeasure P] (c : ℝ≥0∞) :
    P {ω | ∃ n, c ≤ E n ω} ≤ c⁻¹ := by
  simpa using hE.measure_exists_inv_le_le hP c⁻¹

/-- **Ville's inequality for e-processes at a stopping time.** Under every probability measure `P`
of the null, the probability that an e-process is at least `α⁻¹` at a stopping time with values in
`WithTop ℕ` is at most `α`, with the value `stoppedValueLimsup E τ`, the `limsup` of `E`, where
the stopping time is infinite. -/
theorem IsEProcess.measure_inv_le_stoppedValueLimsup_le (hE : IsEProcess E ℱ S) (hP : P ∈ S)
    [IsProbabilityMeasure P] {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (α : ℝ≥0∞) :
    P {ω | α⁻¹ ≤ stoppedValueLimsup E τ ω} ≤ α :=
  ((hE.anti_set (singleton_subset_iff.2 hP)).isEVar_stoppedValueLimsup
    (fun _ hQ ↦ (mem_singleton_iff.1 hQ) ▸ ‹_›) hτ).measure_inv_le_le (mem_singleton P) α

end ProbabilityTheory
