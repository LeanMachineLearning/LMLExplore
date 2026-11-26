/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Calibrator
public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.EProcess.TimeUniform
public import LMLExplore.Order.Filter.CompleteClass

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
at every bounded stopping time the same as validity uniformly in time,
`P {ω | ∃ n, p n ω ≤ α} ≤ α`, and a sequential test likewise rejects at every bounded stopping
time with probability at most `α` [RRLK, §4.1 and Lemma 2]. The running infimum of a p-process
is a p-process. The inverse `E⁻¹` of an e-process is a p-process, by Markov's inequality at each
stopping time, so its running infimum `(partialSups E n)⁻¹` is one as well; thresholding a p-process
at `α`, or an e-process at `α⁻¹`, is a level-`α` sequential test, which is Ville's inequality for
e-processes; every level-`α` sequential test `φ` is the e-process `α⁻¹ * φ` thresholded at `α⁻¹`;
and a p-to-e calibrator applied to a p-process gives an e-process.
Since time-uniform validity does not mention the filtration
(`ProbabilityTheory.IsTimeUniform.mono_filtration`), a p-process or a sequential test for a
filtration `𝒢` is one for every finer filtration [CR26, Theorem 1].

A level-`α` sequential test is admissible when no level-`α` sequential test rejects quasi-surely
wherever it does and, with positive probability under some member of the null, at some time where
it does not [RRLK, §4.2]. A test is admissible as soon as, from every event on which it has not yet
rejected and that the null charges, it fails to reject ever with positive probability under a
member under which it rejects with probability exactly `α`. Every test supermartingale gives such
tests: rejecting from the first time it reaches `α⁻¹` on is admissible when Ville's inequality is
an equality, since by the extended Ville inequality a supermartingale below `α⁻¹` at time `n` stays
below `α⁻¹` forever with positive probability [RRLK, Theorem 18 (3) and Corollary 29 (3)].

The null is an arbitrary set of measures, with no dominating measure, the filtration is
arbitrary, and p-processes are validated at the bounded stopping times, as e-processes are
(`ProbabilityTheory.IsEProcess`); validity at every random time follows
(`ProbabilityTheory.IsPProcess.measure_le_le`).

## Main definitions

* `ProbabilityTheory.IsPProcess p ℱ S`: `p` is a p-process for the null `S` and the filtration
  `ℱ`.
* `ProbabilityTheory.IsSequentialTest φ ℱ S α`: `φ` is a level-`α` sequential test for the null
  `S` and the filtration `ℱ`.
* `ProbabilityTheory.IsAdmissibleSequentialTest φ ℱ S α`: `φ` is an admissible level-`α`
  sequential test for the null `S` and the filtration `ℱ`.

## Main statements

* `ProbabilityTheory.isPProcess_iff_measure_exists_le_le`: an adapted process is a p-process
  exactly when it is ever at most `α` with probability at most `α`, for every level `α` and every
  member of the null [RRLK, §4.1].
* `ProbabilityTheory.IsPProcess.measure_le_le`, `ProbabilityTheory.IsPProcess.isPVar_stoppedValue`:
  a p-process read at a random time is at most `α` with probability at most `α`, and its value at
  a stopping time is a p-variable.
* `ProbabilityTheory.IsPProcess.of_isPVar_stoppedValue`: an adapted process whose value at every
  stopping time that is finite everywhere is a p-variable is a p-process.
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
  `ProbabilityTheory.IsEProcess.isPProcess_inv_partialSups`: for every null, the inverse of an
  e-process and the inverse of its running maximum are p-processes [RRLK, Proposition 12 (1);
  RW, §7.4].
* `ProbabilityTheory.isSequentialTest_iff_forall_isStoppingTime`: a `{0, 1}`-valued adapted
  process is a level-`α` sequential test exactly when it rejects with probability at most `α` at
  every bounded stopping time [RRLK, §4.1].
* `ProbabilityTheory.IsPProcess.isSequentialTest`,
  `ProbabilityTheory.IsEProcess.isSequentialTest`: thresholding a p-process at `α`, or an e-process
  at `α⁻¹`, is a level-`α` sequential test [RRLK, Proposition 11 (1)–(2)].
* `ProbabilityTheory.IsSequentialTest.isEProcess_inv_mul`,
  `ProbabilityTheory.isSequentialTest_iff_exists_isEProcess`: a level-`α` sequential test `φ`
  gives the e-process `α⁻¹ * φ`, so the level-`α` sequential tests are exactly the e-processes
  thresholded at `α⁻¹` [RW, Proposition 7.8].
* `ProbabilityTheory.IsPProcess.isEProcess_comp`: a p-to-e calibrator applied to a p-process is an
  e-process [RRLK, Proposition 14].
* `ProbabilityTheory.isAdmissibleSequentialTest_iff`: a level-`α` sequential test is admissible
  exactly when every level-`α` sequential test that dominates it quasi-surely at every time is
  quasi-surely at most it at every time [RRLK, §4.2].
* `ProbabilityTheory.IsSequentialTest.isAdmissibleSequentialTest_of_forall_exists`: a sufficient
  condition for the admissibility of a sequential test.
* `ProbabilityTheory.IsTestSupermartingale.isSequentialTest`,
  `ProbabilityTheory.IsTestSupermartingale.isAdmissibleSequentialTest`: rejecting from the first
  time a test supermartingale reaches `α⁻¹` on is a level-`α` sequential test, which is admissible
  when Ville's inequality is an equality [RRLK, Theorem 18 (3) and Corollary 29 (3)].

## References

* [CR26] Y. J. Choe and A. Ramdas, *Combining evidence across filtrations*, arXiv:2402.09698v5,
  to appear in J. R. Stat. Soc. Ser. B: Theorem 1 and §3.1.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, §7.3–7.4, Proposition 7.8 and Definition 7.10.
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3, §4.1, §4.2, §4.4, Lemma 2,
  Theorem 18 and Corollary 29.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝒢 ℱ : Filtration ℕ mΩ} {S T : Set (Measure Ω)}
  {P : Measure Ω} {p q E M : ℕ → Ω → ℝ≥0∞} {φ ψ : ℕ → Ω → ℝ≥0∞} {α β : ℝ≥0∞}

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

/-- An adapted process whose value at every stopping time that is finite everywhere is a
p-variable is a p-process. -/
theorem of_isPVar_stoppedValue (hp : Adapted ℱ p)
    (h : ∀ τ : Ω → WithTop ℕ, IsStoppingTime ℱ τ → (∀ ω, τ ω ≠ ⊤) → IsPVar (stoppedValue p τ) S) :
    IsPProcess p ℱ S :=
  ⟨hp, fun τ hτ _ hτN ↦ h τ hτ fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)⟩

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
      fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)]
    exact (hp.isPVar_stoppedValue_of_le hτ hτN).measure_le_le P hP α
  have hp : Adapted ℱ p := fun n ↦ measurable_of_Iic fun α ↦ (h α).measurableSet n
  refine ⟨hp, fun τ hτ N hτN ↦ ⟨measurable_stoppedValue_of_countable (fun _ ↦ hp.measurable)
    hτ.measurable', fun P hP α ↦ ?_⟩⟩
  have h_le := (h α).measure_stoppedEvent_le τ hP
  rwa [stoppedEvent_of_forall_ne_top _
    fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)] at h_le

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
The inverse `(partialSups E n)⁻¹` of the running maximum of an e-process is a p-process: the
running infimum of the p-process `E⁻¹`. -/
theorem IsEProcess.isPProcess_inv_partialSups (hE : IsEProcess E ℱ S) :
    IsPProcess (fun n ω ↦ (partialSups E n ω)⁻¹) ℱ S := by
  simpa only [partialSups_eq_biSup, iSup_apply, ENNReal.inv_iSup] using hE.isPProcess_inv.iInf

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
    stoppedEvent_of_forall_ne_top _ fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)
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

/-! ### Admissible sequential tests -/

/-- A level-`α` sequential test `φ` for the null `S` and the filtration `ℱ` is **admissible**
when every level-`α` sequential test `ψ` that rejects quasi-surely wherever `φ` rejects, at every
time, rejects quasi-surely only where `φ` rejects: no level-`α` sequential test dominates `φ`
strictly [RRLK, §4.2] (`isAdmissibleSequentialTest_iff`). It is the admissibility
(`Filter.IsAdmissible`) of the paths `ω ↦ (n ↦ φ n ω)` among the paths of level-`α` sequential
tests, for the quasi-sure order of the null. -/
abbrev IsAdmissibleSequentialTest (φ : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ)
    (S : Set (Measure Ω)) (α : ℝ≥0∞) : Prop :=
  (quasiSure S).IsAdmissible {X | IsSequentialTest (Function.swap X) ℱ S α} (Function.swap φ)

/-- A level-`α` sequential test is admissible exactly when every level-`α` sequential test that
dominates it quasi-surely at every time is quasi-surely at most it at every time. -/
theorem isAdmissibleSequentialTest_iff :
    IsAdmissibleSequentialTest φ ℱ S α ↔ IsSequentialTest φ ℱ S α ∧ ∀ ψ, IsSequentialTest ψ ℱ S α →
      (∀ n, φ n ≤ᶠ[quasiSure S] ψ n) → ∀ n, ψ n ≤ᶠ[quasiSure S] φ n :=
  Filter.isAdmissible_swap_iff (p := (IsSequentialTest · ℱ S α))

/-- A level-`α` sequential test `ψ` that rejects quasi-surely wherever a process `φ` equals `1`,
at every time, rejects at some time almost surely wherever `φ` equals `1` at some time, under every
member of the null. -/
theorem IsSequentialTest.ae_exists_eq_one_le (hψ : IsSequentialTest ψ ℱ S α) (hP : P ∈ S)
    (h : ∀ k, φ k ≤ᶠ[quasiSure S] ψ k) :
    {ω | ∃ k, φ k ω = 1} ≤ᵐ[P] {ω | ∃ k, ψ k ω = 1} := by
  filter_upwards [ae_all_iff.2 fun k ↦ ae_of_eventually_quasiSure (h k) hP] with ω hω ⟨k, hk⟩
  refine ⟨k, (hψ.eq_zero_or_eq_one k ω).resolve_left fun h0 ↦ ?_⟩
  simpa [hk, h0] using hω k

/-- **A sufficient condition for admissible sequential tests** [RRLK, Theorem 18 (3) and
Corollary 29 (3)]. For a level `α ≠ ∞`, a level-`α` sequential test `φ` is admissible as soon as
every event `s` of time `n` on which `φ n` does not reject, charged by some member of the null, is
charged on the paths on which `φ` never rejects by a member under which `φ` rejects with
probability exactly `α`. -/
theorem IsSequentialTest.isAdmissibleSequentialTest_of_forall_exists
    (hφ : IsSequentialTest φ ℱ S α) (hα : α ≠ ∞)
    (h : ∀ n s, MeasurableSet[ℱ n] s → s ⊆ {ω | φ n ω = 0} → (∃ P ∈ S, P s ≠ 0) →
      ∃ P ∈ S, P {ω | ∃ k, φ k ω = 1} = α ∧ P (s ∩ {ω | ∀ k, φ k ω = 0}) ≠ 0) :
    IsAdmissibleSequentialTest φ ℱ S α := by
  refine isAdmissibleSequentialTest_iff.2 ⟨hφ, fun ψ hψ hφψ n ↦ ?_⟩
  -- `ψ n ≤ φ n` fails exactly on the event `s` where `ψ` rejects at time `n` and `φ` does not
  set s := {ω | ψ n ω = 1 ∧ φ n ω = 0}
  have hs : MeasurableSet[ℱ n] s :=
    (hψ.adapted n (measurableSet_singleton 1)).inter (hφ.adapted n (measurableSet_singleton 0))
  have hle (ω : Ω) (hω : ω ∉ s) : ψ n ω ≤ φ n ω := by
    rcases hψ.eq_zero_or_eq_one n ω with h0 | h1
    · simp [h0]
    rcases hφ.eq_zero_or_eq_one n ω with h0 | h1'
    · exact absurd ⟨h1, h0⟩ hω
    · rw [h1, h1']
  by_cases hnull : ∀ P ∈ S, P s = 0
  · exact eventually_quasiSure_iff.2 fun P hP ↦
      (measure_eq_zero_iff_ae_notMem.1 (hnull P hP)).mono hle
  push Not at hnull
  obtain ⟨P, hP, hPα, hPs⟩ := h n s hs (fun _ hω ↦ hω.2) hnull
  -- under `P`, `ψ` rejects wherever `φ` rejects, and on `s` where `φ` never rejects
  set A := {ω | ∃ k, φ k ω = 1}
  set B := s ∩ {ω | ∀ k, φ k ω = 0}
  have hAB : A ∪ B ≤ᵐ[P] {ω | ∃ k, ψ k ω = 1} := by
    filter_upwards [hψ.ae_exists_eq_one_le hP hφψ] with ω hω hmem
    rcases hmem with hA | ⟨⟨h1, -⟩, -⟩
    · exact hω hA
    · exact ⟨n, h1⟩
  have hdisj : Disjoint A B :=
    disjoint_left.2 fun ω ⟨k, hk⟩ ⟨_, h0⟩ ↦ by simp [h0 k] at hk
  have hB : MeasurableSet B := by
    refine (ℱ.le n _ hs).inter ?_
    simp only [ofPred_forall]
    exact .iInter fun k ↦ hφ.measurable k (measurableSet_singleton 0)
  -- so `ψ` rejects with probability more than `α` under `P`
  have hlt : α < P {ω | ∃ k, ψ k ω = 1} :=
    calc α < α + P B := ENNReal.lt_add_right hα hPs
      _ = P (A ∪ B) := by rw [measure_union hdisj hB, hPα]
      _ ≤ _ := measure_mono_ae hAB
  exact absurd (hψ.measure_exists_eq_one_le P hP) hlt.not_ge

/-- Rejecting the null from the first time a test supermartingale reaches `α⁻¹` on is a level-`α`
sequential test: this is Ville's inequality. -/
theorem IsTestSupermartingale.isSequentialTest (hM : IsTestSupermartingale M ℱ S)
    (α : ℝ≥0∞) :
    IsSequentialTest (fun n ↦ {ω | ∃ k ≤ n, α⁻¹ ≤ M k ω}.indicator 1) ℱ S α where
  adapted n := by
    refine measurable_const.indicator ?_
    have h_eq : {ω | ∃ k ≤ n, α⁻¹ ≤ M k ω} = ⋃ k ∈ Iic n, {ω | α⁻¹ ≤ M k ω} := by
      ext ω
      simp
    rw [h_eq]
    exact .biUnion (to_countable _) fun k hk ↦ ℱ.mono hk _ (hM.adapted k measurableSet_Ici)
  eq_zero_or_eq_one n ω := by by_cases h : ∃ k ≤ n, α⁻¹ ≤ M k ω <;> simp [h]
  measure_exists_eq_one_le P hP := by
    refine (hM.measure_exists_inv_le_le hP α).trans' (measure_mono fun ω ⟨n, hn⟩ ↦ ?_)
    by_cases h : ∃ k ≤ n, α⁻¹ ≤ M k ω
    · obtain ⟨k, -, hk⟩ := h
      exact ⟨k, hk⟩
    · simp [h] at hn

/-- **Admissible sequential tests from test supermartingales** [RRLK, Theorem 18 (3) and
Corollary 29 (3)]. For a test supermartingale `M` for the null `S` and a level `α ≠ ∞`, rejecting
the null from the first time `M` reaches `α⁻¹` on is an admissible level-`α` sequential test as soon
as every event of time `n` on which `M` has stayed below `α⁻¹`, charged by a member of the null, is
charged by a member under which `M` reaches `α⁻¹` with probability exactly `α`, that is, under
which Ville's inequality is an equality. [RRLK, Corollary 29 (3)] states the case of test
martingales that do not overshoot `α⁻¹`. -/
theorem IsTestSupermartingale.isAdmissibleSequentialTest (hM : IsTestSupermartingale M ℱ S)
    (hα : α ≠ ∞) (hMα : ∀ n s, MeasurableSet[ℱ n] s → s ⊆ {ω | ∀ k ≤ n, M k ω < α⁻¹} →
      (∃ P ∈ S, P s ≠ 0) → ∃ P ∈ S, P s ≠ 0 ∧ P {ω | ∃ n, α⁻¹ ≤ M n ω} = α) :
    IsAdmissibleSequentialTest (fun n ↦ {ω | ∃ k ≤ n, α⁻¹ ≤ M k ω}.indicator 1) ℱ S α := by
  have h1 (n : ℕ) (ω : Ω) :
      {ω | ∃ k ≤ n, α⁻¹ ≤ M k ω}.indicator (1 : Ω → ℝ≥0∞) ω = 1 ↔ ∃ k ≤ n, α⁻¹ ≤ M k ω := by
    by_cases h : ∃ k ≤ n, α⁻¹ ≤ M k ω <;> simp [h]
  have h0 (n : ℕ) (ω : Ω) :
      {ω | ∃ k ≤ n, α⁻¹ ≤ M k ω}.indicator (1 : Ω → ℝ≥0∞) ω = 0 ↔ ∀ k ≤ n, M k ω < α⁻¹ := by
    simp [indicator_apply_eq_zero]
  refine (hM.isSequentialTest α).isAdmissibleSequentialTest_of_forall_exists hα
    fun n s hs hs0 hP₀ ↦ ?_
  obtain ⟨P, hP, hPs, hPα⟩ := hMα n s hs (fun ω hω ↦ (h0 n ω).1 (hs0 hω)) hP₀
  refine ⟨P, hP, ?_, ?_⟩
  · -- the test rejects at some time exactly where `M` reaches `α⁻¹`
    have h_eq : {ω | ∃ k, {ω | ∃ j ≤ k, α⁻¹ ≤ M j ω}.indicator (1 : Ω → ℝ≥0∞) ω = 1} =
        {ω | ∃ n, α⁻¹ ≤ M n ω} := by
      ext ω
      simp only [mem_ofPred_eq, h1]
      exact ⟨fun ⟨_, k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, k, le_rfl, hk⟩⟩
    rw [h_eq, hPα]
  -- the test never rejects exactly where `M` stays below `α⁻¹`
  have hnever : {ω | ∀ k, {ω | ∃ j ≤ k, α⁻¹ ≤ M j ω}.indicator (1 : Ω → ℝ≥0∞) ω = 0} =
      {ω | ∀ k, M k ω < α⁻¹} := by
    ext ω
    simp only [mem_ofPred_eq, h0]
    exact ⟨fun h k ↦ h k k le_rfl, fun h k j _ ↦ h j⟩
  rw [hnever]
  simp only [h0] at hs0
  rcases eq_or_ne α 0 with rfl | hα0
  · -- at level `0`, the test supermartingale is finite almost surely, so it never reaches `∞`
    rwa [measure_inter_conull]
    filter_upwards [hM.ae_lt_top hP] with ω hω
    simpa using hω
  -- by the extended Ville inequality from time `n` on `s`, where `M` has stayed below `α⁻¹`,
  -- `M` reaches `α⁻¹` after `n` on a part of `s` of probability less than that of `s`
  set t := {ω | ∃ k ≥ n, α⁻¹ ≤ M k ω}
  have hc : α⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hα0
  have hlt : P (s ∩ t) < P s := by
    rcases eq_or_ne (P s) ∞ with hs_top | hs_top
    · calc P (s ∩ t) ≤ P {ω | ∃ n, α⁻¹ ≤ M n ω} := measure_mono fun ω ⟨_, k, _, hk⟩ ↦ ⟨k, hk⟩
        _ = α := hPα
        _ < P s := hs_top ▸ hα.lt_top
    exact hM.measure_inter_exists_le_lt hP hc hs hPs hs_top fun ω hω ↦ hs0 hω n le_rfl
  -- on `s \ t`, `M` stays below `α⁻¹` before `n` and after `n`
  have hsub : s \ t ⊆ s ∩ {ω | ∀ k, M k ω < α⁻¹} := fun ω ⟨hωs, hωt⟩ ↦ ⟨hωs, fun k ↦ by
    rcases le_total k n with hk | hk
    · exact hs0 hωs k hk
    · exact not_le.1 fun h ↦ hωt ⟨k, hk, h⟩⟩
  intro h
  have := measure_le_inter_add_sdiff P s t
  rw [measure_mono_null hsub h, add_zero] at this
  exact this.not_gt hlt

end ProbabilityTheory
