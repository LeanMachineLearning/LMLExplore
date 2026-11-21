/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.Order.Filter.CompleteClass
import LMLExplore.EValues.Admissible

/-!
# Admissible e-processes

An e-process `F` for a null `S` dominates an e-process `E` when `E n ≤ F n` quasi-surely at every
time `n`, and dominates it strictly when moreover `E n < F n` with positive probability under some
member of `S` at some time. An e-process is admissible when no e-process dominates it strictly
[RRLK, §4.2]: every e-process that dominates it is quasi-surely equal to it at every time. This is
the sequential form of admissible e-variables (`ProbabilityTheory.IsAdmissibleEVar`): the paths
`ω ↦ (n ↦ E n ω)` are admissible (`Filter.IsAdmissible`) among the paths of e-processes, for the
quasi-sure order of the null.

An e-process is admissible as soon as every event of time `n` charged by some member of the null
is charged by a member under which `E n` has expectation one: under such a member, an e-process
that dominates `E` has expectation at most that of `E n` at time `n`, so it is equal to `E n`
almost surely there.

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

## References

* [RRLK] A. Ramdas, J. Ruf, M. Larsson and W. M. Koolen, *Admissible anytime-valid sequential
  inference must rely on nonnegative martingales*, arXiv:2009.03167v3: §4.2.
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

end ProbabilityTheory
