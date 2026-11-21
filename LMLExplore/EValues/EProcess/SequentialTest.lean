/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Calibrator
public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.EProcess.TimeUniform

/-!
# P-processes and sequential tests

A p-process for a null hypothesis `S : Set (Measure Ω)` and a filtration `ℱ` indexed by `ℕ` is an
adapted `ℝ≥0∞`-valued process `p` whose value `stoppedValue p τ` at every bounded stopping time `τ`
is a p-variable for `S` [RW, Definition 7.10]: an anytime-valid p-value. A level-`α`
sequential test is a `{0, 1}`-valued adapted process `φ`, which rejects the null at the times `n`
where `φ n = 1`, that ever rejects with probability at most `α` under every member of the null.
Together with e-processes, these are the instruments of anytime-valid sequential inference of
[RRLK, §4.1], and this file proves the reductions between them [RRLK, Propositions 11, 12 and 14;
RW, Proposition 7.8].

A p-process is the same as time-uniformly valid events `{p n ≤ α}` at every level `α`, and a
sequential test is a `{0, 1}`-valued process whose events of rejection are time-uniformly valid
(`ProbabilityTheory.IsTimeUniform`). The equivalence lemma for time-uniform validity
(`ProbabilityTheory.isTimeUniform_iff_forall_isStoppingTime`) then makes validity of a p-process
at every stopping time the same as validity uniformly in time, `P {ω | ∃ n, p n ω ≤ α} ≤ α`, and
a sequential test likewise rejects at every stopping time with probability at most `α`
[RRLK, §4.1 and Lemma 2]. The running infimum of a p-process is a p-process. The inverse `E⁻¹`
of an e-process is a p-process, by Markov's inequality at each stopping time, so its running
infimum `(⨆ k ≤ n, E k)⁻¹` is one as well; thresholding a p-process at `α`, or an e-process at
`α⁻¹`, is a level-`α` sequential test, which is Ville's inequality for e-processes; every
level-`α` sequential test `φ` is the e-process `α⁻¹ * φ` thresholded at `α⁻¹`; and a p-to-e
calibrator applied to a p-process gives an e-process.
Since time-uniform validity does not mention the filtration
(`ProbabilityTheory.IsTimeUniform.mono_filtration`), a p-process or a sequential test for a
filtration `𝒢` is one for every finer filtration [CR26, Theorem 1].

The null is an arbitrary set of measures, with no dominating measure, the filtration is
arbitrary, and p-processes are validated at the bounded stopping times, as e-processes are
(`ProbabilityTheory.IsEProcess`); validity at every random time follows
(`ProbabilityTheory.IsPProcess.measure_le_le`).

## Main definitions

* `ProbabilityTheory.IsPProcess p ℱ S`: `p` is a p-process for the null `S` and the filtration
  `ℱ`.
* `ProbabilityTheory.IsSequentialTest φ ℱ S α`: `φ` is a level-`α` sequential test for the null
  `S` and the filtration `ℱ`.

## Main statements

* `ProbabilityTheory.isPProcess_iff_measure_exists_le_le`: an adapted process is a p-process
  exactly when it is ever at most `α` with probability at most `α`, for every level `α` and every
  member of the null [RRLK, §4.1].
* `ProbabilityTheory.IsPProcess.measure_le_le`, `ProbabilityTheory.IsPProcess.isPVar_stoppedValue`:
  a p-process read at a random time is at most `α` with probability at most `α`, and its value at
  a stopping time is a p-variable.
* `ProbabilityTheory.isPProcess_iff_forall_isTimeUniform`,
  `ProbabilityTheory.isSequentialTest_iff_isTimeUniform`: p-processes and sequential tests are
  instances of time-uniform validity (`ProbabilityTheory.IsTimeUniform`), for the events
  `{p n ≤ α}` at every level `α` and for the events of rejection [RRLK, §4.1 and Lemma 2].
* `ProbabilityTheory.IsPProcess.mono_filtration`,
  `ProbabilityTheory.IsSequentialTest.mono_filtration`: p-processes and sequential tests for a
  filtration `𝒢` are ones for every finer filtration [CR26, Theorem 1 and §3.1].
* `ProbabilityTheory.isPProcess_iInf_iff`: an adapted process is a p-process exactly when its
  running infimum is one [RRLK, §4.1].
* `ProbabilityTheory.IsEProcess.isPProcess_inv`,
  `ProbabilityTheory.IsEProcess.isPProcess_inv_iSup`: for every null, the inverse of an e-process
  and the inverse of its running maximum are p-processes [RRLK, Proposition 12 (1); RW, §7.4].
* `ProbabilityTheory.isSequentialTest_iff_forall_isStoppingTime`: a `{0, 1}`-valued adapted
  process is a level-`α` sequential test exactly when it rejects with probability at most `α` at
  every stopping time [RRLK, §4.1].
* `ProbabilityTheory.IsPProcess.isSequentialTest`,
  `ProbabilityTheory.IsEProcess.isSequentialTest`: thresholding a p-process at `α`, or an e-process
  at `α⁻¹`, is a level-`α` sequential test [RRLK, Proposition 11 (1)–(2)].
* `ProbabilityTheory.IsSequentialTest.isEProcess_inv_mul`,
  `ProbabilityTheory.isSequentialTest_iff_exists_isEProcess`: a level-`α` sequential test `φ`
  gives the e-process `α⁻¹ * φ`, so the level-`α` sequential tests are exactly the e-processes
  thresholded at `α⁻¹` [RW, Proposition 7.8].
* `ProbabilityTheory.IsPProcess.isEProcess_comp`: a p-to-e calibrator applied to a p-process is an
  e-process [RRLK, Proposition 14].

## References

* [CR26] Y. J. Choe and A. Ramdas, *Combining evidence across filtrations*, arXiv:2402.09698v5,
  to appear in J. R. Stat. Soc. Ser. B: Theorem 1 and §3.1.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, §7.3–7.4, Proposition 7.8 and Definition 7.10.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, §4.1, §4.4 and Lemma 2.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝒢 ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {p q E : ℕ → Ω → ℝ≥0∞} {φ : ℕ → Ω → ℝ≥0∞} {α β : ℝ≥0∞}

/-! ### P-processes -/

/-- `p : ℕ → Ω → ℝ≥0∞` is a **p-process** for the null `S` and the filtration `ℱ`: it is adapted
and, for every bounded stopping time `τ`, its value `stoppedValue p τ` at `τ` is a p-variable for
`S` [RW, Definition 7.10]. Its value at every stopping time is then a p-variable
(`ProbabilityTheory.IsPProcess.isPVar_stoppedValue`). -/
structure IsPProcess (p : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) : Prop where
  adapted : Adapted ℱ p
  isPVar_stoppedValue_of_le ⦃τ : Ω → WithTop ℕ⦄ (hτ : IsStoppingTime ℱ τ) ⦃N : ℕ⦄
    (hτN : ∀ ω, τ ω ≤ N) : IsPVar (stoppedValue p τ) S

namespace IsPProcess

/-- Each value of a p-process is measurable. -/
theorem measurable (hp : IsPProcess p ℱ S) (n : ℕ) : Measurable (p n) :=
  hp.adapted.measurable

/-- The value of a p-process at every fixed time is a p-variable. -/
theorem isPVar (hp : IsPProcess p ℱ S) (n : ℕ) : IsPVar (p n) S := by
  simpa only [stoppedValue_const] using
    hp.isPVar_stoppedValue_of_le (isStoppingTime_const ℱ n) (N := n) fun _ ↦ le_rfl

/-- A p-process for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hp : IsPProcess p ℱ T) : IsPProcess p ℱ S :=
  ⟨hp.adapted, fun _ hτ _ hτN ↦ (hp.isPVar_stoppedValue_of_le hτ hτN).anti_set hST⟩

/-- **Domination.** An adapted process quasi-surely at least a p-process at every time is a
p-process. -/
theorem mono (hp : IsPProcess p ℱ S) (hq : Adapted ℱ q) (hpq : ∀ n, p n ≤ᶠ[quasiSure S] q n) :
    IsPProcess q ℱ S :=
  ⟨hq, fun _ hτ _ hτN ↦ (hp.isPVar_stoppedValue_of_le hτ hτN).mono
    (measurable_stoppedValue_of_countable (fun _ ↦ hq.measurable) hτ.measurable') <|
    eventuallyLE_quasiSure_iff.2 fun P hP ↦ by
      filter_upwards [ae_all_iff.2 fun n ↦ ae_of_eventually_quasiSure (hpq n) hP] with ω hω
        using hω _⟩

/-- An adapted process quasi-surely equal at every time to a p-process is a p-process. -/
theorem congr (hp : IsPProcess p ℱ S) (hq : Adapted ℱ q) (hpq : ∀ n, p n =ᶠ[quasiSure S] q n) :
    IsPProcess q ℱ S :=
  hp.mono hq fun n ↦ (hpq n).le

end IsPProcess

/-- A process is a p-process for `S` exactly when it is adapted and a p-process for each simple
null `{P}` with `P ∈ S`. Adaptedness is needed only when `S` is empty. -/
theorem isPProcess_iff_forall_singleton :
    IsPProcess p ℱ S ↔ Adapted ℱ p ∧ ∀ P ∈ S, IsPProcess p ℱ {P} := by
  refine ⟨fun hp ↦ ⟨hp.adapted, fun P hP ↦ hp.anti_set (singleton_subset_iff.2 hP)⟩,
    fun ⟨hp, h⟩ ↦ ⟨hp, fun _ hτ _ hτN ↦ ⟨measurable_stoppedValue_of_countable
      (fun _ ↦ hp.measurable) hτ.measurable', fun P hP α ↦ ?_⟩⟩⟩
  exact ((h P hP).isPVar_stoppedValue_of_le hτ hτN).measure_le_le P (mem_singleton P) α

/-- **P-processes are time-uniformly valid** [RRLK, §4.1 and Lemma 2]. A process is a p-process
exactly when, at every level `α`, the events `{p n ≤ α}` are time-uniformly valid at level `α`. -/
theorem isPProcess_iff_forall_isTimeUniform :
    IsPProcess p ℱ S ↔ ∀ α, IsTimeUniform (fun n ↦ {ω | p n ω ≤ α}) ℱ S α := by
  refine ⟨fun hp α ↦ isTimeUniform_iff_forall_isStoppingTime.2
    ⟨fun n ↦ hp.adapted n measurableSet_Iic, fun P hP τ hτ N hτN ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [stoppedEvent_of_forall_ne_top _
      fun ω ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hτN ω)]
    exact (hp.isPVar_stoppedValue_of_le hτ hτN).measure_le_le P hP α
  have hp : Adapted ℱ p := fun n ↦ measurable_of_Iic fun α ↦ (h α).measurableSet n
  refine ⟨hp, fun τ hτ N hτN ↦ ⟨measurable_stoppedValue_of_countable (fun _ ↦ hp.measurable)
    hτ.measurable', fun P hP α ↦ ?_⟩⟩
  have h_le := (h α).measure_stoppedEvent_le τ hP
  rwa [stoppedEvent_of_forall_ne_top _
    fun ω ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hτN ω)] at h_le

/-- At every level `α`, the events `{p n ≤ α}` of a p-process are time-uniformly valid at level
`α`. -/
theorem IsPProcess.isTimeUniform (hp : IsPProcess p ℱ S) (α : ℝ≥0∞) :
    IsTimeUniform (fun n ↦ {ω | p n ω ≤ α}) ℱ S α :=
  isPProcess_iff_forall_isTimeUniform.1 hp α

/-- **P-processes are valid uniformly in time** [RRLK, §4.1]. An adapted process is a p-process
exactly when, for every level `α` and every member `P` of the null, the probability that it is
ever at most `α` is at most `α`: the events `{p n ≤ α}` are time-uniformly valid. -/
theorem isPProcess_iff_measure_exists_le_le :
    IsPProcess p ℱ S ↔ Adapted ℱ p ∧ ∀ P ∈ S, ∀ α : ℝ≥0∞, P {ω | ∃ n, p n ω ≤ α} ≤ α := by
  have h_union (α : ℝ≥0∞) : {ω | ∃ n, p n ω ≤ α} = ⋃ n, {ω | p n ω ≤ α} := by ext; simp
  simp only [isPProcess_iff_forall_isTimeUniform, h_union]
  exact ⟨fun h ↦ ⟨fun n ↦ measurable_of_Iic fun α ↦ (h α).measurableSet n,
      fun P hP α ↦ (h α).measure_iUnion_le P hP⟩,
    fun ⟨hp, h⟩ α ↦ ⟨fun n ↦ hp n measurableSet_Iic, fun P hP ↦ h P hP α⟩⟩

/-- **Ville's inequality for p-processes** [RRLK, §4.1]. Under every member of the null, the
probability that a p-process is ever at most `α` is at most `α`. -/
theorem IsPProcess.measure_exists_le_le (hp : IsPProcess p ℱ S) (hP : P ∈ S) (α : ℝ≥0∞) :
    P {ω | ∃ n, p n ω ≤ α} ≤ α :=
  (isPProcess_iff_measure_exists_le_le.1 hp).2 P hP α

/-- **P-processes are valid at random times** [RRLK, Lemma 2]. Under every member of the null, a
p-process read at a random time `τ`, not necessarily a stopping time, is at most `α` with
probability at most `α`. Where `τ` is infinite, Mathlib's `stoppedValue` reads the process at an
arbitrary time. -/
theorem IsPProcess.measure_le_le (hp : IsPProcess p ℱ S) (τ : Ω → WithTop ℕ) (hP : P ∈ S)
    (α : ℝ≥0∞) : P {ω | stoppedValue p τ ω ≤ α} ≤ α :=
  (hp.measure_exists_le_le hP α).trans' (measure_mono fun _ hω ↦ ⟨_, hω⟩)

/-- The value `stoppedValue p τ` of a p-process at every stopping time is a p-variable. Where `τ`
is infinite, Mathlib's `stoppedValue` reads the process at an arbitrary time. -/
theorem IsPProcess.isPVar_stoppedValue (hp : IsPProcess p ℱ S) {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) : IsPVar (stoppedValue p τ) S :=
  ⟨measurable_stoppedValue_of_countable hp.measurable hτ.measurable',
    fun _ hP α ↦ hp.measure_le_le τ hP α⟩

/-- **p-lifting** [CR26, Theorem 1]. A p-process for a filtration `𝒢` is a p-process for every
finer filtration `ℱ`, with no calibration: time-uniform validity does not mention the
filtration. -/
theorem IsPProcess.mono_filtration (hp : IsPProcess p 𝒢 S) (h𝒢ℱ : 𝒢 ≤ ℱ) :
    IsPProcess p ℱ S :=
  isPProcess_iff_forall_isTimeUniform.2 fun α ↦ (hp.isTimeUniform α).mono_filtration h𝒢ℱ

/-- **The running infimum of a p-process** [RRLK, §4.1]. The running infimum
`fun n ω ↦ ⨅ k ≤ n, p k ω` of an adapted process is a p-process exactly when the process is one:
a p-process may be taken nonincreasing. -/
theorem isPProcess_iInf_iff (hp : Adapted ℱ p) :
    IsPProcess (fun n ω ↦ ⨅ k ≤ n, p k ω) ℱ S ↔ IsPProcess p ℱ S := by
  refine ⟨fun h ↦ h.mono hp fun n ↦ .of_forall fun ω ↦ iInf_le_of_le n (iInf_le _ le_rfl),
    fun h ↦ ?_⟩
  refine isPProcess_iff_measure_exists_le_le.2 ⟨fun _ ↦ Measurable.iInf fun k ↦
    Measurable.iInf fun hk ↦ (hp k).mono (ℱ.mono hk) le_rfl, fun P hP α ↦ ?_⟩
  -- where the running infimum is at most `α` at `n`, `p` is at most `α` at its minimizer `k ≤ n`
  refine (h.measure_exists_le_le hP α).trans' (measure_mono fun ω ⟨n, hn⟩ ↦ ?_)
  obtain ⟨k, -, hk⟩ := (Finset.Iic n).exists_min_image (p · ω) ⟨n, Finset.mem_Iic.2 le_rfl⟩
  exact ⟨k, (le_iInf₂ fun j hj ↦ hk j (Finset.mem_Iic.2 hj)).trans hn⟩

/-- The running infimum of a p-process is a p-process. -/
theorem IsPProcess.iInf (hp : IsPProcess p ℱ S) : IsPProcess (fun n ω ↦ ⨅ k ≤ n, p k ω) ℱ S :=
  (isPProcess_iInf_iff hp.adapted).2 hp

/-- **E-to-p calibration of e-processes.** The inverse `fun n ω ↦ (E n ω)⁻¹` of an e-process is a
p-process, by Markov's inequality at each stopping time. -/
theorem IsEProcess.isPProcess_inv (hE : IsEProcess E ℱ S) :
    IsPProcess (fun n ω ↦ (E n ω)⁻¹) ℱ S :=
  ⟨fun n ↦ (hE.adapted n).inv, fun _ hτ _ hτN ↦ (hE.isEVar_stoppedValue_of_le hτ hτN).isPVar_inv⟩

/-- **The p-process of the running maximum of an e-process** [RRLK, Proposition 12 (1); RW, §7.4].
The inverse `(⨆ k ≤ n, E k)⁻¹` of the running maximum of an e-process is a p-process: the running
infimum of the p-process `E⁻¹`. -/
theorem IsEProcess.isPProcess_inv_iSup (hE : IsEProcess E ℱ S) :
    IsPProcess (fun n ω ↦ (⨆ k ≤ n, E k ω)⁻¹) ℱ S := by
  simpa only [ENNReal.inv_iSup] using hE.isPProcess_inv.iInf

/-- **A p-to-e calibrator turns p-processes into e-processes** [RRLK, Proposition 14]. For a null
of measures of mass at most one, a p-to-e calibrator `f` applied to a p-process gives the
e-process `fun n ω ↦ f (p n ω)`. -/
theorem IsPProcess.isEProcess_comp {f : ℝ≥0∞ → ℝ≥0∞} (hf : IsPToECalibrator f)
    (hS : ∀ P ∈ S, P univ ≤ 1) (hp : IsPProcess p ℱ S) :
    IsEProcess (fun n ω ↦ f (p n ω)) ℱ S :=
  ⟨fun n ↦ hf.measurable.comp (hp.adapted n), fun _ hτ _ hτN ↦
    hf.isEVar_comp hS (hp.isPVar_stoppedValue_of_le hτ hτN)⟩

/-! ### Sequential tests -/

/-- `φ : ℕ → Ω → ℝ≥0∞` is a **level-`α` sequential test** for the null `S` and the filtration `ℱ`:
it is adapted and `{0, 1}`-valued, it rejects the null at the times `n` with `φ n ω = 1`, and under
every member of the null it ever rejects with probability at most `α` [RW, §7.3, (7.1)]. -/
structure IsSequentialTest (φ : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω))
    (α : ℝ≥0∞) : Prop where
  adapted : Adapted ℱ φ
  eq_zero_or_eq_one : ∀ n ω, φ n ω = 0 ∨ φ n ω = 1
  measure_exists_eq_one_le : ∀ P ∈ S, P {ω | ∃ n, φ n ω = 1} ≤ α

namespace IsSequentialTest

/-- Each value of a sequential test is measurable. -/
theorem measurable (hφ : IsSequentialTest φ ℱ S α) (n : ℕ) : Measurable (φ n) :=
  hφ.adapted.measurable

/-- Under every member of the null, a level-`α` sequential test read at a random time `τ`, not
necessarily a stopping time, rejects with probability at most `α`. Where `τ` is infinite, Mathlib's
`stoppedValue` reads the test at an arbitrary time. -/
theorem measure_eq_one_le (hφ : IsSequentialTest φ ℱ S α) (τ : Ω → WithTop ℕ) (hP : P ∈ S) :
    P {ω | stoppedValue φ τ ω = 1} ≤ α :=
  (hφ.measure_exists_eq_one_le P hP).trans' (measure_mono fun _ hω ↦ ⟨_, hω⟩)

/-- Under every member of the null, a level-`α` sequential test read at a random time `τ`, not
necessarily a stopping time, has expectation at most `α`: its expectation is at most the
probability that it rejects. -/
theorem lintegral_le (hφ : IsSequentialTest φ ℱ S α) (τ : Ω → WithTop ℕ) (hP : P ∈ S) :
    ∫⁻ ω, stoppedValue φ τ ω ∂P ≤ α := by
  have h_ind : stoppedValue φ τ = {ω | stoppedValue φ τ ω = 1}.indicator 1 := by
    ext ω
    rcases hφ.eq_zero_or_eq_one (τ ω).untopA ω with h | h <;> simp [stoppedValue, h]
  rw [h_ind]
  exact (lintegral_indicator_one_le _).trans (hφ.measure_eq_one_le τ hP)

/-- A level-`α` sequential test for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hφ : IsSequentialTest φ ℱ T α) : IsSequentialTest φ ℱ S α :=
  ⟨hφ.adapted, hφ.eq_zero_or_eq_one, fun P hP ↦ hφ.measure_exists_eq_one_le P (hST hP)⟩

/-- A level-`α` sequential test is a level-`β` sequential test for every `β ≥ α`. -/
theorem mono (hφ : IsSequentialTest φ ℱ S α) (hαβ : α ≤ β) : IsSequentialTest φ ℱ S β :=
  ⟨hφ.adapted, hφ.eq_zero_or_eq_one, fun P hP ↦ (hφ.measure_exists_eq_one_le P hP).trans hαβ⟩

end IsSequentialTest

/-- **Sequential tests are time-uniformly valid** [RRLK, §4.1 and Lemma 2]. A process is a
level-`α` sequential test exactly when it is adapted and `{0, 1}`-valued and its events of
rejection `{φ n = 1}` are time-uniformly valid at level `α`. -/
theorem isSequentialTest_iff_isTimeUniform :
    IsSequentialTest φ ℱ S α ↔ Adapted ℱ φ ∧ (∀ n ω, φ n ω = 0 ∨ φ n ω = 1) ∧
      IsTimeUniform (fun n ↦ {ω | φ n ω = 1}) ℱ S α :=
  ⟨fun hφ ↦ ⟨hφ.adapted, hφ.eq_zero_or_eq_one, fun n ↦ hφ.adapted n (measurableSet_singleton 1),
      fun P hP ↦ by simpa [ofPred_exists] using hφ.measure_exists_eq_one_le P hP⟩,
    fun ⟨hφ, h01, h⟩ ↦ ⟨hφ, h01, fun P hP ↦ by
      simpa [ofPred_exists] using h.measure_iUnion_le P hP⟩⟩

/-- The events of rejection `{φ n = 1}` of a level-`α` sequential test are time-uniformly valid at
level `α`. -/
theorem IsSequentialTest.isTimeUniform (hφ : IsSequentialTest φ ℱ S α) :
    IsTimeUniform (fun n ↦ {ω | φ n ω = 1}) ℱ S α :=
  (isSequentialTest_iff_isTimeUniform.1 hφ).2.2

/-- A level-`α` sequential test for a filtration `𝒢` is a level-`α` sequential test for every
finer filtration `ℱ` [CR26, §3.1]: time-uniform validity does not mention the filtration. -/
theorem IsSequentialTest.mono_filtration (hφ : IsSequentialTest φ 𝒢 S α) (h𝒢ℱ : 𝒢 ≤ ℱ) :
    IsSequentialTest φ ℱ S α :=
  isSequentialTest_iff_isTimeUniform.2 ⟨fun n ↦ (hφ.adapted n).mono (h𝒢ℱ n) le_rfl,
    hφ.eq_zero_or_eq_one, hφ.isTimeUniform.mono_filtration h𝒢ℱ⟩

/-- **Sequential tests are valid at stopping times** [RRLK, §4.1]. A `{0, 1}`-valued adapted
process is a level-`α` sequential test exactly when, under every member of the null, it rejects
at every bounded stopping time with probability at most `α`: the time-uniform validity of its
events of rejection, read at stopping times. -/
theorem isSequentialTest_iff_forall_isStoppingTime :
    IsSequentialTest φ ℱ S α ↔ Adapted ℱ φ ∧ (∀ n ω, φ n ω = 0 ∨ φ n ω = 1) ∧
      ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
        ∀ P ∈ S, P {ω | stoppedValue φ τ ω = 1} ≤ α := by
  rw [isSequentialTest_iff_isTimeUniform, isTimeUniform_iff_forall_isStoppingTime]
  have h_eq {τ : Ω → WithTop ℕ} {N : ℕ} (hτN : ∀ ω, τ ω ≤ N) :
      stoppedEvent (fun n ↦ {ω | φ n ω = 1}) τ = {ω | stoppedValue φ τ ω = 1} :=
    stoppedEvent_of_forall_ne_top _ fun ω ↦ ne_top_of_le_ne_top (WithTop.natCast_ne_top N) (hτN ω)
  exact ⟨fun ⟨hφ, h01, _, h⟩ ↦ ⟨hφ, h01, fun τ hτ N hτN P hP ↦ h_eq hτN ▸ h P hP τ hτ N hτN⟩,
    fun ⟨hφ, h01, h⟩ ↦ ⟨hφ, h01, fun n ↦ hφ n (measurableSet_singleton 1),
      fun P hP τ hτ N hτN ↦ (h_eq hτN).symm ▸ h τ hτ N hτN P hP⟩⟩

/-- **Thresholding a p-process** [RRLK, Proposition 11 (1)]. Rejecting the null at the times at
which a p-process is at most `α` is a level-`α` sequential test. -/
theorem IsPProcess.isSequentialTest (hp : IsPProcess p ℱ S) (α : ℝ≥0∞) :
    IsSequentialTest (fun n ↦ {ω | p n ω ≤ α}.indicator 1) ℱ S α where
  adapted n := measurable_const.indicator (hp.adapted n measurableSet_Iic)
  eq_zero_or_eq_one n ω := by by_cases h : p n ω ≤ α <;> simp [h]
  measure_exists_eq_one_le P hP := by
    simpa [indicator_apply] using hp.measure_exists_le_le hP α

/-- **Thresholding an e-process** [RRLK, Proposition 11 (2); RW, Fact 7.6]. Rejecting the null at
the times at which an e-process is at least `α⁻¹` is a level-`α` sequential test: this is Ville's
inequality for e-processes. -/
theorem IsEProcess.isSequentialTest (hE : IsEProcess E ℱ S) (α : ℝ≥0∞) :
    IsSequentialTest (fun n ↦ {ω | α⁻¹ ≤ E n ω}.indicator 1) ℱ S α := by
  simpa only [ENNReal.inv_le_iff_inv_le] using hE.isPProcess_inv.isSequentialTest α

/-- **Sequential tests are e-processes** [RW, Proposition 7.8]. A level-`α` sequential test `φ`
gives the e-process `α⁻¹ * φ`, whose expectation at every stopping time is `α⁻¹` times the
probability of rejection. -/
theorem IsSequentialTest.isEProcess_inv_mul (hφ : IsSequentialTest φ ℱ S α) :
    IsEProcess (fun n ω ↦ α⁻¹ * φ n ω) ℱ S :=
  .of_lintegral_le_one (fun n ↦ (hφ.adapted n).const_mul α⁻¹) fun τ hτ _ _ P hP ↦ by
    -- the stopped value of `α⁻¹ * φ` is `α⁻¹` times that of `φ`, by definition of `stoppedValue`
    have h_eq : stoppedValue (fun n ω ↦ α⁻¹ * φ n ω) τ = fun ω ↦ α⁻¹ * stoppedValue φ τ ω := rfl
    rw [h_eq, lintegral_const_mul _
      (measurable_stoppedValue_of_countable hφ.measurable hτ.measurable')]
    calc α⁻¹ * ∫⁻ ω, stoppedValue φ τ ω ∂P ≤ α⁻¹ * α := by gcongr; exact hφ.lintegral_le τ hP
      _ ≤ 1 := ENNReal.inv_mul_le_one α

/-- **Sequential tests are thresholded e-processes** [RW, Proposition 7.8 and Fact 7.6]. For a level
`α ≠ ∞`, a process is a level-`α` sequential test exactly when it is the indicator of the times at
which some e-process is at least `α⁻¹`. -/
theorem isSequentialTest_iff_exists_isEProcess (hα : α ≠ ∞) :
    IsSequentialTest φ ℱ S α ↔
      ∃ E, IsEProcess E ℱ S ∧ φ = fun n ↦ {ω | α⁻¹ ≤ E n ω}.indicator 1 := by
  refine ⟨fun hφ ↦ ⟨_, hφ.isEProcess_inv_mul, ?_⟩, fun ⟨E, hE, hφE⟩ ↦
    hφE ▸ hE.isSequentialTest α⟩
  -- `α⁻¹ * φ n ω` reaches `α⁻¹` exactly where `φ n ω = 1`, since `α⁻¹ ≠ 0`
  ext n ω
  rcases hφ.eq_zero_or_eq_one n ω with h | h <;> simp [h, hα]

end ProbabilityTheory
