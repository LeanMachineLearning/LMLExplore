/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
import LMLExplore.EValues.Admissible

/-!
# Admissible e-processes

An e-process `F` for a null `S` dominates an e-process `E` when `E n ≤ F n` almost surely under
every member of `S`, at every time `n`, and dominates it strictly when moreover `E n < F n` with
positive probability under some member of `S` at some time. An e-process is admissible when no
e-process dominates it strictly [RRLK, §4.2]: every e-process that dominates it is equal to it at
every time, almost surely under every member of the null. This is the sequential form of
admissible e-variables (`ProbabilityTheory.IsAdmissibleEVar`).

An e-process is admissible as soon as every event of time `n` charged by some member of the null
is charged by a member under which `E n` has expectation one: under such a member, an e-process
that dominates `E` has expectation at most that of `E n` at time `n`, so it is equal to `E n`
almost surely there.

## Main definitions

* `ProbabilityTheory.IsAdmissibleEProcess E ℱ S`: `E` is an admissible e-process for the null `S`
  and the filtration `ℱ`.

## Main statements

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
e-process `F` that dominates it, `E n ≤ F n` almost surely under every member of `S` at every time
`n`, is at most `E` at every time, almost surely under every member of `S`: no e-process dominates
`E` strictly [RRLK, §4.2] (`isAdmissibleEProcess_iff_measure_lt_eq_zero`). -/
structure IsAdmissibleEProcess (E : ℕ → Ω → ℝ≥0∞) (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Prop extends IsEProcess E ℱ S where
  ae_le_of_ae_le : ∀ F, IsEProcess F ℱ S → (∀ P ∈ S, ∀ n, E n ≤ᵐ[P] F n) →
    ∀ P ∈ S, ∀ n, F n ≤ᵐ[P] E n

namespace IsAdmissibleEProcess

/-- An e-process that dominates an admissible e-process is at most it at every time, almost
surely under every member of the null. -/
theorem ae_le (hE : IsAdmissibleEProcess E ℱ S) (hF : IsEProcess F ℱ S)
    (hEF : ∀ P ∈ S, ∀ n, E n ≤ᵐ[P] F n) (hP : P ∈ S) (n : ℕ) : F n ≤ᵐ[P] E n :=
  hE.ae_le_of_ae_le F hF hEF P hP n

/-- An e-process that dominates an admissible e-process is equal to it at every time, almost
surely under every member of the null. -/
theorem ae_eq (hE : IsAdmissibleEProcess E ℱ S) (hF : IsEProcess F ℱ S)
    (hEF : ∀ P ∈ S, ∀ n, E n ≤ᵐ[P] F n) (hP : P ∈ S) (n : ℕ) : F n =ᵐ[P] E n :=
  (hE.ae_le hF hEF hP n).antisymm (hEF P hP n)

/-- An adapted process equal to an admissible e-process at every time, almost surely under every
member of the null, is an admissible e-process. -/
theorem congr (hE : IsAdmissibleEProcess E ℱ S) (hF : Adapted ℱ F)
    (hEF : ∀ P ∈ S, ∀ n, E n =ᵐ[P] F n) : IsAdmissibleEProcess F ℱ S where
  toIsEProcess := hE.toIsEProcess.congr hF hEF
  ae_le_of_ae_le _ hG hFG P hP n :=
    (hE.ae_le hG (fun P hP n ↦ (hEF P hP n).le.trans (hFG P hP n)) hP n).trans (hEF P hP n).le

end IsAdmissibleEProcess

/-- An e-process is admissible exactly when no e-process dominates it strictly: for every
e-process `F` with `E n ≤ F n` almost surely under every member of the null at every time, the
event `E n < F n` is null under every member of the null at every time [RRLK, §4.2]. -/
theorem isAdmissibleEProcess_iff_measure_lt_eq_zero :
    IsAdmissibleEProcess E ℱ S ↔ IsEProcess E ℱ S ∧ ∀ F, IsEProcess F ℱ S →
      (∀ P ∈ S, ∀ n, E n ≤ᵐ[P] F n) → ∀ P ∈ S, ∀ n, P {ω | E n ω < F n ω} = 0 := by
  have key (F : ℕ → Ω → ℝ≥0∞) (P : Measure Ω) (n : ℕ) :
      F n ≤ᵐ[P] E n ↔ P {ω | E n ω < F n ω} = 0 := by
    simp only [Filter.EventuallyLE, ae_iff, not_le]
  exact ⟨fun h ↦ ⟨h.toIsEProcess, fun F hF hEF P hP n ↦ (key F P n).1 (h.ae_le hF hEF hP n)⟩,
    fun h ↦ ⟨h.1, fun F hF hEF P hP n ↦ (key F P n).2 (h.2 F hF hEF P hP n)⟩⟩

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
  exact hPA ((hF.isEVar n).measure_lt_eq_zero_of_ae_le hP (hEF P hP n) hPE)

end ProbabilityTheory
