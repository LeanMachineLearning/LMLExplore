/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.Admissible
public import LMLExplore.EValues.EProcess.StoppedNull
import TauCeti.Statistics.Experiments.Mixture

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

The admissibility criterion of Ramdas and Wang for e-variables [RW, Theorem 2.14], applied on the
space of stopped paths, characterizes the admissible e-processes for any null [EVR26, Note 46,
Theorem 6]: `E` is admissible exactly when, for every family of events `B n` of the filtration not
all polar for the null, the deficits `1 - ∫⁻ E τ ∂P` at the bounded stopping times `τ` are
arbitrarily small compared with the masses `P (B τ)` of the events read at `τ`. The infimum of
these ratios is the largest amount that can be added to `E` on the events `B n`. In particular an
e-process is admissible as soon as every event of time `n` charged by some member of the null is
charged by a member under which `E n` has expectation one. Test martingales with initial
expectation one are admissible for this reason, and for a simple null they are all the admissible
e-processes [RRLK, Theorem 18]. For a composite null of probability measures, an admissible
e-process is the quasi-sure essential infimum of test martingales for the members
[RRLK, Corollary 26], and, for a locally dominated null, every e-process is below an admissible
one [RRLK, Proposition 9].

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
* `ProbabilityTheory.isAdmissibleEProcess_iff_isAdmissibleEVar_stoppedNull`: admissible
  e-processes are the admissible e-variables of the stopped null.
* `ProbabilityTheory.IsEProcess.isEProcess_add_indicator_iff`,
  `ProbabilityTheory.IsEProcess.isEProcess_add_indicator_iff'`: raising an e-process by `t` on
  adapted events `B n` gives an e-process exactly when `t` is at most the ratios of the deficits
  at the bounded stopping times, or at the stopping times that are finite everywhere, to the
  masses of the events read at them [EVR26, Note 46].
* `ProbabilityTheory.isAdmissibleEProcess_iff_iInf_div_eq_zero`,
  `ProbabilityTheory.isAdmissibleEProcess_iff_iInf_div_eq_zero'`: **the admissibility criterion**,
  for any null: an e-process is admissible exactly when the infimum of these ratios is zero for
  every family of adapted events not all polar for the null, over the bounded stopping times and
  over the stopping times that are finite everywhere [EVR26, Note 46, Theorem 6].
* `ProbabilityTheory.IsEProcess.isAdmissibleEProcess_of_exists_lintegral_eq`: an e-process such
  that every event of time `n` charged by a member of the null is charged by a member under which
  `E n` has expectation `1` is admissible.
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

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, the notes and the
  Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026, Note 46,
  Theorem 6 (`results/46-admissibility-criterion.md`).
* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3: §4.2, Proposition 9,
  Theorem 18, Corollaries 26 and 29.
* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6: Theorem 2.14.
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
      (∀ n, E n ≤ᶠ[quasiSure S] F n) → ∀ n, F n ≤ᶠ[quasiSure S] E n :=
  Filter.isAdmissible_swap_iff (p := (IsEProcess · ℱ S))

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

/-! ### The admissibility criterion -/

/-- At a stopping time that is finite everywhere, the value of an e-process `E` raised by `t` on
adapted events `B n` is an e-variable exactly when `t` is at most every ratio of the deficit of
`E τ` to the mass of the event `B τ` read at `τ`: the e-variable form
`ProbabilityTheory.IsEVar.isEVar_add_indicator_iff` at `τ`. -/
private theorem IsEProcess.isEVar_stoppedValue_add_indicator_iff (hE : IsEProcess E ℱ S)
    {B : ℕ → Set Ω} (hB : ∀ n, MeasurableSet[ℱ n] (B n)) {t : ℝ≥0∞} {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) (hτ_top : ∀ ω, τ ω ≠ ⊤) :
    IsEVar (stoppedValue (fun n ω ↦ E n ω + (B n).indicator (fun _ ↦ t) ω) τ) S ↔
      t ≤ ⨅ P ∈ S, ⨅ (_ : P (stoppedEvent B τ) ≠ 0),
        (1 - ∫⁻ ω, stoppedValue E τ ω ∂P) / P (stoppedEvent B τ) := by
  -- the raised process read at `τ` is `E τ` raised by `t` on the event `B τ`
  have h_eq : stoppedValue (fun n ω ↦ E n ω + (B n).indicator (fun _ ↦ t) ω) τ =
      fun ω ↦ stoppedValue E τ ω + (stoppedEvent B τ).indicator (fun _ ↦ t) ω :=
    funext fun ω ↦ by
      by_cases hω : ω ∈ B (τ ω).untopA <;>
        simp [stoppedValue, hω, mem_stoppedEvent_of_ne_top (hτ_top ω)]
  rw [h_eq]
  exact (hE.isEVar_stoppedValue hτ hτ_top).isEVar_add_indicator_iff
    (measurableSet_stoppedEvent (fun n ↦ ℱ.le n _ (hB n)) hτ.measurable')

/-- **The largest amount that can be added on adapted events.** For an e-process `E` and events
`B n` of the filtration, raising `E n` by `t` on `B n` at every time `n` gives an e-process exactly
when `t` is at most the deficit `1 - ∫⁻ E τ ∂P` divided by `P (B τ)`, for every bounded stopping
time `τ` and every member `P` of the null that charges the event `B τ` read at `τ`
(`MeasureTheory.stoppedEvent`) [EVR26, Note 46]. At each stopping time this is the e-variable form
`ProbabilityTheory.IsEVar.isEVar_add_indicator_iff`. -/
theorem IsEProcess.isEProcess_add_indicator_iff (hE : IsEProcess E ℱ S) {B : ℕ → Set Ω}
    (hB : ∀ n, MeasurableSet[ℱ n] (B n)) {t : ℝ≥0∞} :
    IsEProcess (fun n ω ↦ E n ω + (B n).indicator (fun _ ↦ t) ω) ℱ S ↔
      t ≤ ⨅ (τ : Ω → WithTop ℕ) (_ : IsStoppingTime ℱ τ) (_ : ∃ N : ℕ, ∀ ω, τ ω ≤ N),
        ⨅ P ∈ S, ⨅ (_ : P (stoppedEvent B τ) ≠ 0),
          (1 - ∫⁻ ω, stoppedValue E τ ω ∂P) / P (stoppedEvent B τ) := by
  refine ⟨fun hF ↦ le_iInf₂ fun τ hτ ↦ le_iInf fun ⟨N, hτN⟩ ↦
    (hE.isEVar_stoppedValue_add_indicator_iff hB hτ fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)).1
      (hF.isEVar_stoppedValue_of_le hτ hτN),
    fun h ↦ ⟨fun n ↦ (hE.adapted n).add (measurable_const.indicator (hB n)), fun τ hτ N hτN ↦
      (hE.isEVar_stoppedValue_add_indicator_iff hB hτ fun ω ↦
        WithTop.ne_top_of_le_natCast (hτN ω)).2
        (h.trans (iInf₂_le_of_le τ hτ (iInf_le _ ⟨N, hτN⟩)))⟩⟩

/-- **The largest amount that can be added on adapted events, at stopping times with values in
`ℕ`.** In `ProbabilityTheory.IsEProcess.isEProcess_add_indicator_iff`, the bounded stopping times
can be replaced by the stopping times that are finite everywhere [EVR26, Note 46]. -/
theorem IsEProcess.isEProcess_add_indicator_iff' (hE : IsEProcess E ℱ S)
    {B : ℕ → Set Ω} (hB : ∀ n, MeasurableSet[ℱ n] (B n)) {t : ℝ≥0∞} :
    IsEProcess (fun n ω ↦ E n ω + (B n).indicator (fun _ ↦ t) ω) ℱ S ↔
      t ≤ ⨅ (τ : Ω → WithTop ℕ) (_ : IsStoppingTime ℱ τ) (_ : ∀ ω, τ ω ≠ ⊤),
        ⨅ P ∈ S, ⨅ (_ : P (stoppedEvent B τ) ≠ 0),
          (1 - ∫⁻ ω, stoppedValue E τ ω ∂P) / P (stoppedEvent B τ) := by
  refine ⟨fun hF ↦ le_iInf₂ fun τ hτ ↦ le_iInf fun hτ_top ↦
    (hE.isEVar_stoppedValue_add_indicator_iff hB hτ hτ_top).1 (hF.isEVar_stoppedValue hτ hτ_top),
    fun h ↦ (hE.isEProcess_add_indicator_iff hB).2 (h.trans <| iInf₂_mono fun τ hτ ↦
      le_iInf fun ⟨N, hτN⟩ ↦ iInf_le_of_le (fun ω ↦ WithTop.ne_top_of_le_natCast (hτN ω)) le_rfl)⟩

/-- The infimum of the ratios of the e-variable criterion over the stopped null, for the set of
stopped paths `{x | x.2 ∈ B x.1}` of adapted events `B n`, is the infimum over the stopping times
that are finite everywhere and the members of the null of the ratios at the event `B τ`. -/
private theorem iInf_stoppedNull_div_eq (hE : Adapted ℱ E) {B : ℕ → Set Ω}
    (hB : ∀ n, MeasurableSet[ℱ n] (B n)) :
    ⨅ μ ∈ stoppedNull ℱ S, ⨅ (_ : μ {x | x.2 ∈ B x.1} ≠ 0),
        (1 - ∫⁻ x, Function.uncurry E x ∂μ) / μ {x | x.2 ∈ B x.1} =
      ⨅ (τ : Ω → WithTop ℕ) (_ : IsStoppingTime ℱ τ) (_ : ∀ ω, τ ω ≠ ⊤),
        ⨅ P ∈ S, ⨅ (_ : P (stoppedEvent B τ) ≠ 0),
          (1 - ∫⁻ ω, stoppedValue E τ ω ∂P) / P (stoppedEvent B τ) := by
  -- under a stopped law, `Function.uncurry E` has the integral of `E τ`
  have h_int {P : Measure Ω} {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
      ∫⁻ x, Function.uncurry E x ∂(stoppedLaw ℱ P fun ω ↦ (τ ω).untopA) =
        ∫⁻ ω, stoppedValue E τ ω ∂P := by
    rw [lintegral_stoppedLaw hτ.measurable'.untopA
      (Filtration.measurable_uncurry_progressive_iff.2 hE)]
    simp [stoppedValue]
  refine le_antisymm (le_iInf₂ fun τ hτ ↦ le_iInf fun hτ_top ↦ le_iInf₂ fun P hP ↦ ?_)
    (le_iInf₂ fun μ hμ ↦ ?_)
  · refine iInf₂_le_of_le _ (stoppedLaw_mem_stoppedNull hP hτ hτ_top) ?_
    rw [stoppedLaw_setOf_mem hB hτ.measurable' hτ_top, h_int hτ]
  · obtain ⟨P, hP, τ, hτ, hτ_top, rfl⟩ := mem_stoppedNull.1 hμ
    refine iInf₂_le_of_le τ hτ (iInf_le_of_le hτ_top (iInf₂_le_of_le P hP ?_))
    rw [stoppedLaw_setOf_mem hB hτ.measurable' hτ_top, h_int hτ]

/-- **The admissibility criterion for e-processes, at stopping times with values in `ℕ`**
[EVR26, Note 46, Theorem 6]. An e-process `E` for any null `S` is admissible exactly when, for
every family of events `B n` of the filtration not all polar for the null, the deficits
`1 - ∫⁻ E τ ∂P` at the stopping times `τ` that are finite everywhere, under the members `P` that
charge the event `B τ` read at `τ`, are arbitrarily small compared with `P (B τ)`. This is the
criterion of Ramdas and Wang for e-variables
(`ProbabilityTheory.isAdmissibleEVar_iff_iInf_div_eq_zero`) for the stopped null, whose measurable
sets are the families of their sections `B n`. No domination, finiteness or mass hypothesis is
needed. -/
theorem isAdmissibleEProcess_iff_iInf_div_eq_zero' :
    IsAdmissibleEProcess E ℱ S ↔ IsEProcess E ℱ S ∧ ∀ B : ℕ → Set Ω,
      (∀ n, MeasurableSet[ℱ n] (B n)) → (∃ n, ∃ P ∈ S, P (B n) ≠ 0) →
        ⨅ (τ : Ω → WithTop ℕ) (_ : IsStoppingTime ℱ τ) (_ : ∀ ω, τ ω ≠ ⊤),
          ⨅ P ∈ S, ⨅ (_ : P (stoppedEvent B τ) ≠ 0),
            (1 - ∫⁻ ω, stoppedValue E τ ω ∂P) / P (stoppedEvent B τ) = 0 := by
  rw [isAdmissibleEProcess_iff_isAdmissibleEVar_stoppedNull, isAdmissibleEVar_iff_iInf_div_eq_zero,
    ← isEProcess_iff_isEVar_stoppedNull]
  refine and_congr_right fun hE ↦ ?_
  refine ⟨fun h B hB ⟨n, P, hP, hPB⟩ ↦ ?_, fun h A hA hSA ↦ ?_⟩
  · -- the set of stopped paths of the family `B` is charged at the constant time `n`
    rw [← iInf_stoppedNull_div_eq hE.adapted hB]
    have hn : IsStoppingTime ℱ fun _ : Ω ↦ (n : WithTop ℕ) := isStoppingTime_const ℱ n
    refine h _ (Filtration.measurableSet_progressive_iff_of_countable.2 hB) ⟨_,
      stoppedLaw_mem_stoppedNull hP hn fun _ ↦ WithTop.natCast_ne_top n, ?_⟩
    rwa [stoppedLaw_setOf_mem hB hn.measurable' fun _ ↦ WithTop.natCast_ne_top n,
      stoppedEvent_const]
  · -- a progressive set of stopped paths is the set of stopped paths of its sections
    set B : ℕ → Set Ω := fun n ↦ {ω | (n, ω) ∈ A} with hB_def
    have hB : ∀ n, MeasurableSet[ℱ n] (B n) :=
      Filtration.measurableSet_progressive_iff_of_countable.1 hA
    have hA_eq : {x : ℕ × Ω | x.2 ∈ B x.1} = A := by
      ext
      simp [hB_def]
    rw [← hA_eq] at hSA ⊢
    rw [iInf_stoppedNull_div_eq hE.adapted hB]
    refine h B hB ?_
    -- a stopped law charges it only if the null charges one of the sections
    obtain ⟨μ, hμ, hμA⟩ := hSA
    obtain ⟨P, hP, τ, hτ, hτ_top, rfl⟩ := mem_stoppedNull.1 hμ
    rw [stoppedLaw_setOf_mem hB hτ.measurable' hτ_top] at hμA
    by_contra hne
    refine hμA (measure_mono_null stoppedEvent_subset_iUnion (measure_iUnion_null fun n ↦ ?_))
    by_contra hPn
    exact hne ⟨n, P, hP, hPn⟩

/-- **The admissibility criterion for e-processes** [EVR26, Note 46, Theorem 6]. An e-process `E`
for any null `S` is admissible exactly when, for every family of events `B n` of the filtration
not all polar for the null, the deficits `1 - ∫⁻ E τ ∂P` at the bounded stopping times `τ`, under
the members `P` that charge the event `B τ` read at `τ`, are arbitrarily small compared with
`P (B τ)`. The infimum is the largest amount that can be added to `E` on the events `B n`
(`ProbabilityTheory.IsEProcess.isEProcess_add_indicator_iff`), as it is over the stopping times
that are finite everywhere (`ProbabilityTheory.isAdmissibleEProcess_iff_iInf_div_eq_zero'`). No
domination, finiteness or mass hypothesis is needed. -/
theorem isAdmissibleEProcess_iff_iInf_div_eq_zero :
    IsAdmissibleEProcess E ℱ S ↔ IsEProcess E ℱ S ∧ ∀ B : ℕ → Set Ω,
      (∀ n, MeasurableSet[ℱ n] (B n)) → (∃ n, ∃ P ∈ S, P (B n) ≠ 0) →
        ⨅ (τ : Ω → WithTop ℕ) (_ : IsStoppingTime ℱ τ) (_ : ∃ N : ℕ, ∀ ω, τ ω ≤ N),
          ⨅ P ∈ S, ⨅ (_ : P (stoppedEvent B τ) ≠ 0),
            (1 - ∫⁻ ω, stoppedValue E τ ω ∂P) / P (stoppedEvent B τ) = 0 := by
  rw [isAdmissibleEProcess_iff_iInf_div_eq_zero']
  refine and_congr_right fun hE ↦ forall₃_congr fun B hB _ ↦ ?_
  -- both infima are the largest amount that can be added to `E` on the events `B n`
  exact ⟨fun h0 ↦ nonpos_iff_eq_zero.1 (((hE.isEProcess_add_indicator_iff' hB).1
      ((hE.isEProcess_add_indicator_iff hB).2 le_rfl)).trans h0.le),
    fun h0 ↦ nonpos_iff_eq_zero.1 (((hE.isEProcess_add_indicator_iff hB).1
      ((hE.isEProcess_add_indicator_iff' hB).2 le_rfl)).trans h0.le)⟩

/-- **A sufficient condition for admissibility.** An e-process `E` such that every
`ℱ n`-measurable set charged by a member of the null is charged by a member `P` under which `E n`
has expectation `1` is admissible: the ratios of the criterion
`ProbabilityTheory.isAdmissibleEProcess_iff_iInf_div_eq_zero` vanish at the constant time `n`. -/
theorem IsEProcess.isAdmissibleEProcess_of_exists_lintegral_eq (hE : IsEProcess E ℱ S)
    (h : ∀ n A, MeasurableSet[ℱ n] A → (∃ P ∈ S, P A ≠ 0) →
      ∃ P ∈ S, P A ≠ 0 ∧ ∫⁻ ω, E n ω ∂P = 1) :
    IsAdmissibleEProcess E ℱ S := by
  refine isAdmissibleEProcess_iff_iInf_div_eq_zero.2 ⟨hE, fun B hB ⟨n, P₀, hP₀, hP₀B⟩ ↦ ?_⟩
  obtain ⟨P, hP, hPB, hPE⟩ := h n (B n) (hB n) ⟨P₀, hP₀, hP₀B⟩
  refine nonpos_iff_eq_zero.1 (iInf₂_le_of_le (fun _ ↦ (n : WithTop ℕ))
    (isStoppingTime_const ℱ n) (iInf_le_of_le ⟨n, fun _ ↦ le_rfl⟩ (iInf₂_le_of_le P hP
      (iInf_le_of_le (by rwa [stoppedEvent_const]) ?_))))
  simp [hPE]

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
restriction of `μ`, whose restrictions are s-finite (as when `μ` is σ-finite on the filtration,
`MeasureTheory.SigmaFiniteFiltration`), and the members are s-finite. Then every e-process for
`S` is at most an admissible e-process. -/
theorem IsEProcess.exists_isAdmissibleEProcess_le_of_absolutelyContinuous (μ : Measure Ω)
    (hμ : ∀ n, SFinite (μ.trim (ℱ.le n)))
    (hSμ : ∀ P ∈ S, ∀ n, P.trim (ℱ.le n) ≪ μ.trim (ℱ.le n))
    (hS : ∀ P ∈ S, SFinite P) (hE : IsEProcess E ℱ S) :
    ∃ E' : ℕ → Ω → ℝ≥0∞, IsAdmissibleEProcess E' ℱ S ∧ E ≤ E' := by
  -- the zero measure is a reference measure for the empty null
  rcases S.eq_empty_or_nonempty with rfl | hS_ne
  · exact hE.exists_isAdmissibleEProcess_le 0 fun _ _ _ ↦ by simp
  have : Nonempty S := hS_ne.to_subtype
  have (P : S) : SFinite (P : Measure Ω) := hS P P.property
  -- the Halmos–Savage lemma, stated over an arbitrary σ-algebra `m` so that elaboration infers it:
  -- a dominated family has the null sets of a countable mixture of its members `Q (θs k)`
  have halmosSavage (m : MeasurableSpace Ω) (Q : S → Measure[m] Ω) (ν : Measure[m] Ω)
      (_ : SFinite ν) (hQ : ∀ P, Q P ≪ ν) :
      ∃ θs : ℕ → S, ∀ P s, (∀ k, Q (θs k) s = 0) → Q P s = 0 :=
    (TauCeti.exists_absolutelyContinuous_countableMixture Q ν hQ).imp fun _ h P _ hs ↦
      h P (TauCeti.countableMixture_apply_eq_zero_iff.2 hs)
  -- at every time `n`, the restrictions of the members to `ℱ n` have the null sets of those of
  -- countably many members `Ps n k`; the sum of all these members is a reference measure
  choose Ps hPs using fun n ↦ halmosSavage (ℱ n) (fun P ↦ (P : Measure Ω).trim (ℱ.le n))
    (μ.trim (ℱ.le n)) (hμ n) fun P ↦ hSμ P P.property n
  refine hE.exists_isAdmissibleEProcess_le (Measure.sum fun k : ℕ × ℕ ↦ (Ps k.1 k.2 : Measure Ω))
    fun n A hA ↦ ?_
  rw [Measure.sum_apply_eq_zero' (ℱ.le n A hA)]
  refine ⟨fun h P hP ↦ ?_, fun h k ↦ h _ (Ps k.1 k.2).property⟩
  rw [← trim_measurableSet_eq (ℱ.le n) hA]
  exact hPs n ⟨P, hP⟩ A fun k ↦ (trim_measurableSet_eq (ℱ.le n) hA).trans (h (n, k))

end ProbabilityTheory
