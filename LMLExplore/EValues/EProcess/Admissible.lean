/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Admissible
public import LMLExplore.EValues.EProcess.StoppedNull
import LMLExplore.MeasureTheory.Measure.HalmosSavage

/-!
# Admissible e-processes

An e-process `F` for a null `S` dominates an e-process `E` when `E n ≤ F n` quasi-surely at every
time `n`, and dominates it strictly when moreover `E n < F n` with positive probability under some
member of `S` at some time. An e-process is admissible when no e-process dominates it strictly
[RRLK, §4.2]: every e-process that dominates it is quasi-surely equal to it at every time. This is
the sequential form of admissible e-variables (`ProbabilityTheory.IsAdmissibleEVar`): the paths
`ω ↦ (n ↦ E n ω)` are admissible (`Filter.IsAdmissible`) among the paths of e-processes, for the
quasi-sure order of the null. On the space of stopped paths it is exactly the admissibility of
`Function.uncurry E` among the e-variables of the stopped null.

An e-process is admissible as soon as every event of time `n` charged by some member of the null
is charged by a member under which `E n` has expectation one: under such a member, an e-process
that dominates `E` has expectation at most that of `E n` at time `n`, so it is equal to `E n`
almost surely there. Test martingales with initial expectation one are admissible for this reason,
and for a simple null they are all the admissible e-processes [RRLK, Theorem 18]. For a composite
null of probability measures, an admissible e-process is the quasi-sure essential infimum of test
martingales for the members [RRLK, Corollary 26], and, for a locally dominated null, every
e-process is below an admissible one [RRLK, Proposition 9].

## Main definitions

* `ProbabilityTheory.IsAdmissibleEProcess E ℱ S`: `E` is an admissible e-process for the null `S`
  and the filtration `ℱ`.

## Main statements

* `ProbabilityTheory.isAdmissibleEProcess_iff`: an e-process is admissible exactly when every
  e-process that dominates it quasi-surely at every time is quasi-surely at most it at every time.
* `ProbabilityTheory.IsAdmissibleEProcess.congr`: an adapted process quasi-surely equal at every
  time to an admissible e-process is an admissible e-process.
* `ProbabilityTheory.isAdmissibleEProcess_iff_measure_lt_eq_zero`: an e-process is admissible
  exactly when no e-process dominates it strictly, the definition of [RRLK, §4.2].
* `ProbabilityTheory.IsEProcess.isAdmissibleEProcess_of_exists_lintegral_eq`: an e-process such
  that every event of time `n` charged by a member of the null is charged by a member under which
  `E n` has expectation `1` is admissible.
* `ProbabilityTheory.isAdmissibleEProcess_iff_isAdmissibleEVar_stoppedNull`: admissible
  e-processes are the admissible e-variables of the stopped null.
* `ProbabilityTheory.IsTestMartingale.isAdmissibleEProcess`: a test martingale with initial
  expectation `1` under every member is admissible [RRLK, Corollary 29].
* `ProbabilityTheory.isAdmissibleEProcess_singleton_iff`: for a simple null, the admissible
  e-processes are the test martingales with initial expectation `1` [RRLK, Theorem 18].
* `ProbabilityTheory.IsAdmissibleEProcess.eventuallyLE_of_forall_ae_le`,
  `ProbabilityTheory.IsAdmissibleEProcess.exists_isTestMartingale`: an admissible e-process is the
  largest adapted process below test martingales for the members with initial expectation `1`
  that dominate it [RRLK, Corollary 26].
* `ProbabilityTheory.IsEProcess.exists_isAdmissibleEProcess_le`,
  `ProbabilityTheory.IsEProcess.exists_isAdmissibleEProcess_le_of_absolutelyContinuous`: every
  e-process is at most an admissible e-process, for a null with a reference measure with its
  null sets at every time, in particular for a locally dominated null [RRLK, Proposition 9].

## References

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3: §4.2, Proposition 9,
  Theorem 18, Corollaries 26 and 29.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {S : Set (Measure Ω)}
  {P : Measure Ω} {E F : ℕ → Ω → ℝ≥0∞}

/-- An e-process `E` for the null `S` and the filtration `ℱ` is **admissible** when every
e-process `F` that dominates it quasi-surely at every time is quasi-surely at most `E` at every
time: no e-process dominates `E` strictly [RRLK, §4.2]
(`isAdmissibleEProcess_iff_measure_lt_eq_zero`). It is the admissibility (`Filter.IsAdmissible`)
of the paths `ω ↦ (n ↦ E n ω)` among the paths of e-processes for the quasi-sure order of the
null, which compares the processes at every time since time is countable
(`isAdmissibleEProcess_iff`). -/
abbrev IsAdmissibleEProcess (E : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Prop :=
  (quasiSure S).IsAdmissible {X | IsEProcess (Function.swap X) ℱ S} (Function.swap E)

/-- An e-process is admissible exactly when every e-process that dominates it quasi-surely at
every time is quasi-surely at most it at every time. -/
theorem isAdmissibleEProcess_iff :
    IsAdmissibleEProcess E ℱ S ↔ IsEProcess E ℱ S ∧ ∀ F, IsEProcess F ℱ S →
      (∀ n, E n ≤ᶠ[quasiSure S] F n) → ∀ n, F n ≤ᶠ[quasiSure S] E n := by
  -- the quasi-sure order on paths compares the processes quasi-surely at every time
  have hle (E F : ℕ → Ω → ℝ≥0∞) :
      Function.swap E ≤ᶠ[quasiSure S] Function.swap F ↔ ∀ n, E n ≤ᶠ[quasiSure S] F n := by
    simp only [Filter.EventuallyLE, Pi.le_def, Function.swap]
    exact eventually_countable_forall
  exact ⟨fun hE ↦ ⟨hE.mem, fun F hF hEF ↦ (hle F E).1 (hE.eventuallyLE hF ((hle E F).2 hEF))⟩,
    fun ⟨hE, h⟩ ↦ ⟨hE, fun X hX hEX ↦ (hle _ E).2 (h _ hX ((hle E _).1 hEX))⟩⟩

/-- An adapted process quasi-surely equal at every time to an admissible e-process is an
admissible e-process. -/
theorem IsAdmissibleEProcess.congr (hE : IsAdmissibleEProcess E ℱ S) (hF : Adapted ℱ F)
    (hEF : ∀ n, E n =ᶠ[quasiSure S] F n) : IsAdmissibleEProcess F ℱ S :=
  isAdmissibleEProcess_iff.2 ⟨hE.mem.congr hF hEF, fun G hG hFG n ↦
    ((isAdmissibleEProcess_iff.1 hE).2 G hG (fun n ↦ (hEF n).le.trans (hFG n)) n).trans
      (hEF n).le⟩

/-- An e-process is admissible exactly when no e-process dominates it strictly: for every
e-process `F` with `E n ≤ F n` quasi-surely at every time, the event `E n < F n` is null under
every member of the null at every time [RRLK, §4.2]. -/
theorem isAdmissibleEProcess_iff_measure_lt_eq_zero :
    IsAdmissibleEProcess E ℱ S ↔ IsEProcess E ℱ S ∧ ∀ F, IsEProcess F ℱ S →
      (∀ n, E n ≤ᶠ[quasiSure S] F n) → ∀ P ∈ S, ∀ n, P {ω | E n ω < F n ω} = 0 := by
  have key (F : ℕ → Ω → ℝ≥0∞) (n : ℕ) :
      F n ≤ᶠ[quasiSure S] E n ↔ ∀ P ∈ S, P {ω | E n ω < F n ω} = 0 := by
    simp only [Filter.EventuallyLE, eventually_quasiSure_iff, ae_iff, not_le]
  rw [isAdmissibleEProcess_iff]
  exact and_congr_right fun _ ↦ forall₃_congr fun F _ _ ↦ (forall_congr' fun n ↦ key F n).trans
    ⟨fun h P hP n ↦ h n P hP, fun h n P hP ↦ h P hP n⟩

/-- **A sufficient condition for admissibility.** An e-process `E` such that every
`ℱ n`-measurable set charged by a member of the null is charged by a member `P` under which `E n`
has expectation `1` is admissible. -/
theorem IsEProcess.isAdmissibleEProcess_of_exists_lintegral_eq (hE : IsEProcess E ℱ S)
    (h : ∀ n A, MeasurableSet[ℱ n] A → (∃ P ∈ S, P A ≠ 0) →
      ∃ P ∈ S, P A ≠ 0 ∧ ∫⁻ ω, E n ω ∂P = 1) :
    IsAdmissibleEProcess E ℱ S := by
  refine isAdmissibleEProcess_iff_measure_lt_eq_zero.2 ⟨hE, fun F hF hEF P₀ hP₀ n ↦ ?_⟩
  by_contra hP₀A
  -- a member of the null that charges `{E n < F n}` and under which `E n` has expectation `1`
  -- cannot charge it
  obtain ⟨P, hP, hPA, hPE⟩ := h n _
    (measurableSet_lt (hE.adapted n) (hF.adapted n)) ⟨P₀, hP₀, hP₀A⟩
  exact hPA ((hF.isEVar n).measure_lt_eq_zero_of_ae_le hP (ae_of_eventually_quasiSure (hEF n) hP)
    hPE)

/-! ### Admissible e-processes on stopped paths -/

/-- **Admissible e-processes are the admissible e-variables of the stopped null.** An adapted
process `E` is an admissible e-process for `S` exactly when `Function.uncurry E` is an admissible
e-variable on the space of stopped paths for the stopped null `stoppedNull ℱ S`. The quasi-sure
order of the stopped null compares adapted processes at every time
(`eventually_quasiSure_stoppedNull_iff`). -/
theorem isAdmissibleEProcess_iff_isAdmissibleEVar_stoppedNull :
    IsAdmissibleEProcess E ℱ S ↔ IsAdmissibleEVar (Function.uncurry E) (stoppedNull ℱ S) := by
  -- the quasi-sure order of the stopped null on adapted processes
  have hle {F G : ℕ → Ω → ℝ≥0∞} (hF : Adapted ℱ F) (hG : Adapted ℱ G) :
      Function.uncurry F ≤ᶠ[quasiSure (stoppedNull ℱ S)] Function.uncurry G ↔
        ∀ n, F n ≤ᶠ[quasiSure S] G n :=
    eventually_quasiSure_stoppedNull_iff (measurableSet_le (mδ := ℱ.progressive)
      (Filtration.measurable_uncurry_progressive_iff.2 hF)
      (Filtration.measurable_uncurry_progressive_iff.2 hG))
  refine ⟨fun hE ↦ ⟨isEProcess_iff_isEVar_stoppedNull.1 hE.mem, fun G hG hEG ↦ ?_⟩,
    fun hE ↦ isAdmissibleEProcess_iff.2 ⟨isEProcess_iff_isEVar_stoppedNull.2 hE.mem,
      fun F hF hEF ↦ ?_⟩⟩
  · -- a progressive e-variable `G` of the stopped null is the uncurried form of the e-process
    -- `Function.curry G`
    rw [← Function.uncurry_curry G] at hG hEG ⊢
    have hG' : IsEProcess (Function.curry G) ℱ S := isEProcess_iff_isEVar_stoppedNull.2 hG
    exact (hle hG'.adapted hE.mem.adapted).2
      ((isAdmissibleEProcess_iff.1 hE).2 _ hG' ((hle hE.mem.adapted hG'.adapted).1 hEG))
  · have hE' : IsEProcess E ℱ S := isEProcess_iff_isEVar_stoppedNull.2 hE.mem
    exact (hle hF.adapted hE'.adapted).1 (hE.eventuallyLE (isEProcess_iff_isEVar_stoppedNull.1 hF)
      ((hle hE'.adapted hF.adapted).2 hEF))

/-! ### Admissibility and test martingales -/

/-- **Test martingales with initial expectation one are admissible** [RRLK, Corollary 29]. For a
null of finite measures, a test martingale for the null whose initial value has expectation `1`
under every member is an admissible e-process: its expectation is `1` at every time under every
member. -/
theorem IsTestMartingale.isAdmissibleEProcess (hS : ∀ P ∈ S, IsFiniteMeasure P)
    (hE : IsTestMartingale E ℱ S) (h_one : ∀ P ∈ S, ∫⁻ ω, E 0 ω ∂P = 1) :
    IsAdmissibleEProcess E ℱ S :=
  (hE.isTestSupermartingale.isEProcess hS).isAdmissibleEProcess_of_exists_lintegral_eq
    fun n _ _ ⟨P, hP, hPA⟩ ↦ ⟨P, hP, hPA, (hE.lintegral_eq hP 0 n).trans (h_one P hP)⟩

/-- **Admissible e-processes for a simple null** [RRLK, Theorem 18]. For a probability measure
`P`, an e-process for `{P}` is admissible exactly when it is a test martingale for `P` whose
initial value has expectation `1`. -/
theorem isAdmissibleEProcess_singleton_iff [IsProbabilityMeasure P] :
    IsAdmissibleEProcess E ℱ {P} ↔ IsTestMartingale E ℱ {P} ∧ ∫⁻ ω, E 0 ω ∂P = 1 := by
  refine ⟨fun hE ↦ ?_, fun ⟨hM, h_one⟩ ↦ hM.isAdmissibleEProcess
    (fun Q hQ ↦ mem_singleton_iff.1 hQ ▸ inferInstance) fun Q hQ ↦ mem_singleton_iff.1 hQ ▸ h_one⟩
  -- an admissible e-process is a version of a test martingale with initial expectation `1` that
  -- dominates it
  obtain ⟨M, hM, hM_one, hEM⟩ := hE.mem.exists_isTestMartingale_ae_le (mem_singleton P)
  have hM_eP : IsEProcess M ℱ {P} :=
    hM.isTestSupermartingale.isEProcess fun Q hQ ↦ mem_singleton_iff.1 hQ ▸ inferInstance
  -- the test martingale above `E` is below `E`, by admissibility
  have hME := (isAdmissibleEProcess_iff.1 hE).2 M hM_eP fun n ↦ by
    simpa only [quasiSure_singleton] using hEM n
  have h_eq (n : ℕ) : M n =ᶠ[quasiSure {P}] E n := by
    rw [quasiSure_singleton]
    exact (by simpa only [quasiSure_singleton] using hME n : M n ≤ᵐ[P] E n).antisymm (hEM n)
  refine ⟨hM.congr hE.mem.adapted h_eq, ?_⟩
  rw [← lintegral_congr_ae (by simpa only [quasiSure_singleton] using h_eq 0), hM_one]

/-- **An admissible e-process is the largest process below the test supermartingales that
dominate it.** For a null of probability measures, let `E` be an admissible e-process and, for
every member `P`, let `M P` be a test supermartingale for `P` that dominates `E` `P`-almost
surely. Then every adapted process that `M P` dominates `P`-almost surely, for every member `P`,
is quasi-surely at most `E` at every time. -/
theorem IsAdmissibleEProcess.eventuallyLE_of_forall_ae_le (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : IsAdmissibleEProcess E ℱ S) {M : Measure Ω → ℕ → Ω → ℝ≥0∞}
    (hM : ∀ P ∈ S, IsTestSupermartingale (M P) ℱ {P}) (hEM : ∀ P ∈ S, ∀ n, E n ≤ᵐ[P] M P n)
    (hF : Adapted ℱ F) (hFM : ∀ P ∈ S, ∀ n, F n ≤ᵐ[P] M P n) (n : ℕ) :
    F n ≤ᶠ[quasiSure S] E n := by
  -- the maximum of `E` and `F` is an e-process that dominates `E`
  have hG : IsEProcess (fun n ω ↦ max (E n ω) (F n ω)) ℱ S := by
    refine (isEProcess_iff_forall_exists_isTestSupermartingale hS
      fun n ↦ (hE.mem.adapted n).max (hF n)).2 fun P hP ↦ ⟨M P, hM P hP, fun n ↦ ?_⟩
    filter_upwards [hEM P hP n, hFM P hP n] with ω h₁ h₂ using max_le h₁ h₂
  filter_upwards [(isAdmissibleEProcess_iff.1 hE).2 _ hG
    (fun n ↦ .of_forall fun ω ↦ le_max_left _ _) n] with ω hω
  exact (le_max_right _ _).trans hω

/-- **Admissible e-processes are essential infima of test martingales** [RRLK, Corollary 26].
For a null of probability measures, an admissible e-process `E` is dominated, under every member
`P`, by a test martingale `M P` for `P` whose initial value has expectation `1`, and it is the
quasi-sure essential infimum of these martingales among adapted processes: every adapted process
that `M P` dominates `P`-almost surely, for every member `P`, is quasi-surely at most `E`. No
domination of the null is needed. -/
theorem IsAdmissibleEProcess.exists_isTestMartingale (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    (hE : IsAdmissibleEProcess E ℱ S) :
    ∃ M : Measure Ω → ℕ → Ω → ℝ≥0∞, (∀ P ∈ S, IsTestMartingale (M P) ℱ {P} ∧
      ∫⁻ ω, M P 0 ω ∂P = 1 ∧ ∀ n, E n ≤ᵐ[P] M P n) ∧
      ∀ F, Adapted ℱ F → (∀ P ∈ S, ∀ n, F n ≤ᵐ[P] M P n) → ∀ n, F n ≤ᶠ[quasiSure S] E n := by
  have h (P : Measure Ω) : ∃ M : ℕ → Ω → ℝ≥0∞, P ∈ S →
      IsTestMartingale M ℱ {P} ∧ ∫⁻ ω, M 0 ω ∂P = 1 ∧ ∀ n, E n ≤ᵐ[P] M n := by
    by_cases hP : P ∈ S
    · have := hS P hP
      obtain ⟨M, hM⟩ := hE.mem.exists_isTestMartingale_ae_le hP
      exact ⟨M, fun _ ↦ hM⟩
    · exact ⟨0, fun h ↦ absurd h hP⟩
  choose M hM using h
  exact ⟨M, hM, fun F hF hFM ↦ hE.eventuallyLE_of_forall_ae_le hS
    (fun P hP ↦ (hM P hP).1.isTestSupermartingale) (fun P hP ↦ (hM P hP).2.2) hF hFM⟩

/-! ### Every e-process is below an admissible one -/

/-- **Every e-process is dominated by an admissible e-process, under a reference measure**
[RRLK, Proposition 9]. Let `R` be an s-finite measure whose null `ℱ n`-measurable sets are, at every
time `n`, the `ℱ n`-measurable sets polar for the null `S`. Then every e-process for `S` is at
most an admissible e-process. -/
theorem IsEProcess.exists_isAdmissibleEProcess_le (R : Measure Ω) [SFinite R]
    (hR : ∀ n A, MeasurableSet[ℱ n] A → (R A = 0 ↔ ∀ P ∈ S, P A = 0))
    (hE : IsEProcess E ℱ S) : ∃ E' : ℕ → Ω → ℝ≥0∞, IsAdmissibleEProcess E' ℱ S ∧ E ≤ E' := by
  -- an s-finite reference measure on the stopped paths, to which the e-variable form applies
  -- through `isAdmissibleEProcess_iff_isAdmissibleEVar_stoppedNull`
  set R' : @Measure (ℕ × Ω) ℱ.progressive := Measure.sum fun n : ℕ ↦ stoppedLaw ℱ R fun _ ↦ n
    with hR'_def
  have : @SFinite _ ℱ.progressive R' := by
    rw [hR'_def]
    infer_instance
  -- whose null sets are those of the stopped null
  have hR' {A : Set (ℕ × Ω)} (hA : MeasurableSet[ℱ.progressive] A) :
      R' A = 0 ↔ ∀ μ ∈ stoppedNull ℱ S, μ A = 0 := by
    have h := eventually_quasiSure_stoppedNull_iff (ℱ := ℱ) (S := S) (p := fun x ↦ x ∉ A)
      hA.compl
    simp only [eventually_quasiSure_iff, ae_iff, not_not, ofPred_mem_eq] at h
    rw [h, hR'_def, Measure.sum_apply_eq_zero' hA]
    refine forall_congr' fun n ↦ ?_
    rw [stoppedLaw_apply measurable_const hA,
      hR n _ (Filtration.measurableSet_progressive_iff_of_countable.1 hA n)]
  obtain ⟨G, hG, hEG⟩ := (isEProcess_iff_isEVar_stoppedNull.1 hE)
    |>.exists_isAdmissibleEVar_le_of_absolutelyContinuousSet (mΩ := ℱ.progressive) R'
      (Measure.absolutelyContinuousSet_iff.2 fun A hA h ↦ (hR' hA).2 h)
      fun μ hμ ↦ .mk fun A hA h ↦ (hR' hA).1 h μ hμ
  -- `G` is the uncurried form of the admissible e-process `Function.curry G`
  rw [← Function.uncurry_curry G] at hG
  exact ⟨Function.curry G, isAdmissibleEProcess_iff_isAdmissibleEVar_stoppedNull.2 hG,
    fun n ω ↦ hEG (n, ω)⟩

/-- **Every e-process for a locally dominated null is dominated by an admissible e-process**
[RRLK, Proposition 9]. Let `S` be a null that is locally dominated by a measure `μ`: at every
time `n`, the restrictions of the members to `ℱ n` are absolutely continuous with respect to the
restriction of `μ`, whose restrictions are σ-finite, and the members are s-finite. Then every
e-process for `S` is at most an admissible e-process. -/
theorem IsEProcess.exists_isAdmissibleEProcess_le_of_absolutelyContinuous (μ : Measure Ω)
    [SigmaFiniteFiltration μ ℱ] (hSμ : ∀ P ∈ S, ∀ n, P.trim (ℱ.le n) ≪ μ.trim (ℱ.le n))
    (hS : ∀ P ∈ S, SFinite P) (hE : IsEProcess E ℱ S) :
    ∃ E' : ℕ → Ω → ℝ≥0∞, IsAdmissibleEProcess E' ℱ S ∧ E ≤ E' := by
  have (P : S) : SFinite (P : Measure Ω) := hS P P.2
  -- at every time, a countable subfamily with the null `ℱ n`-measurable sets of the null, by the
  -- Halmos–Savage lemma; the sum of the members of their union is a reference measure
  have h (n : ℕ) : ∃ T : Set S, T.Countable ∧ ∀ A, MeasurableSet[ℱ n] A →
      (∀ P ∈ T, (P : Measure Ω) A = 0) → ∀ P ∈ S, P A = 0 := by
    obtain ⟨T, hT, hT_null⟩ := Measure.exists_countable_forall_measure_eq_zero
      (μ := μ.trim (ℱ.le n)) (ν := fun P : S ↦ (P : Measure Ω).trim (ℱ.le n))
      fun P ↦ hSμ P P.2 n
    refine ⟨T, hT, fun A hA hTA P hP ↦ ?_⟩
    have h := hT_null A hA (fun P hPT ↦ by rw [trim_measurableSet_eq _ hA]; exact hTA P hPT)
      ⟨P, hP⟩
    rwa [trim_measurableSet_eq _ hA] at h
  choose T hT hT_null using h
  have : Countable (⋃ n, T n) := (countable_iUnion hT).to_subtype
  refine hE.exists_isAdmissibleEProcess_le
    (Measure.sum fun P : ⋃ n, T n ↦ ((P : S) : Measure Ω)) fun n A hA ↦ ?_
  rw [Measure.sum_apply_eq_zero' (ℱ.le n A hA)]
  refine ⟨fun h ↦ hT_null n A hA fun P hP ↦ h ⟨P, mem_iUnion.2 ⟨n, hP⟩⟩,
    fun h P ↦ h _ (P : S).2⟩

end ProbabilityTheory
