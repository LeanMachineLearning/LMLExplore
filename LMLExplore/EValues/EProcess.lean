/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EVariable
public import LMLExplore.Probability.Martingale.OptionalStopping

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

Every test supermartingale for a null of probability measures is an e-process, by optional
stopping (`ProbabilityTheory.IsTestSupermartingale.isEVar_stoppedValueLimsup`), but not
conversely. This file also proves the closure properties of e-processes that follow from those of
e-variables at each stopping time: restricting the null, passing to an adapted process that is
almost surely smaller, and convex combinations.

## Main definitions

* `ProbabilityTheory.IsEProcess E ℱ S`: `E` is an e-process for the null `S` and the filtration
  `ℱ`.

## Main statements

* `ProbabilityTheory.IsEProcess.isEVar`: the value of an e-process at every fixed time is an
  e-variable.
* `ProbabilityTheory.IsEProcess.lintegral_le_one`: under every probability measure of the null, an
  e-process has expectation at most `1` at every stopping time with values in `ℕ`.
* `ProbabilityTheory.isEProcess_iff_lintegral_le_one`,
  `ProbabilityTheory.IsEProcess.of_lintegral_le_one`: for a null of probability measures, an
  adapted process is an e-process exactly when it has expectation at most `1` at every stopping
  time with values in `ℕ`, under every member of the null.
* `ProbabilityTheory.IsEProcess.anti_set`, `ProbabilityTheory.isEProcess_iff_forall_singleton`: an
  e-process for `S` is one for every subset of `S`, and an adapted process is an e-process for `S`
  exactly when it is one for each simple null `{P}` with `P ∈ S`.
* `ProbabilityTheory.IsEProcess.mono_ae`, `ProbabilityTheory.IsEProcess.mono`: for a null of
  finite measures, an adapted process dominated by an e-process, almost surely under every member
  of the null or pointwise, is an e-process.
* `ProbabilityTheory.isEProcess_one`, `ProbabilityTheory.convex_isEProcess`: the constant process
  `1` is an e-process, and the e-processes for a null form a convex set.
* `ProbabilityTheory.IsTestSupermartingale.isEProcess`: a test supermartingale for a null of
  probability measures is an e-process [RW, Fact 7.5].

## Implementation notes

The definition and its closure properties are adapted from
`EValuesResearch/ForLMLExplore/EValues/EProcess.lean` (commit `d2da7b7`) in the paper project
`RemyDegenne/evalues_research` (same author), which also fixes the field name
`isEVar_stoppedValue`.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614.
-/

public section

open MeasureTheory Set
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

/-- Under every probability measure of the null, an e-process has expectation at most `1` at every
stopping time with values in `ℕ`. -/
theorem lintegral_le_one (hE : IsEProcess E ℱ S)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ))) (hP : P ∈ S) [IsProbabilityMeasure P] :
    ∫⁻ ω, E (τ ω) ω ∂P ≤ 1 :=
  (hE.isEVar_stoppedValue τ hτ).lintegral_le_one hP

/-- The value `fun ω ↦ E (τ ω) ω` of an e-process at a stopping time with values in `ℕ` is
measurable. -/
theorem measurable_stoppedValue (hE : IsEProcess E ℱ S)
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ))) : Measurable fun ω ↦ E (τ ω) ω :=
  hE.adapted.measurable_apply_stoppingTime hτ

/-- For a null of probability measures, an adapted process with expectation at most `1` at every
stopping time with values in `ℕ`, under every member of the null, is an e-process. -/
theorem of_lintegral_le_one (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hE : Adapted ℱ E)
    (h : ∀ τ : Ω → ℕ, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) →
      ∀ P ∈ S, ∫⁻ ω, E (τ ω) ω ∂P ≤ 1) :
    IsEProcess E ℱ S :=
  ⟨hE, fun τ hτ ↦ IsEVar.of_lintegral_le_one hS (hE.measurable_apply_stoppingTime hτ) (h τ hτ)⟩

/-- An e-process for `T` is one for every subset of `T`. -/
theorem anti_set (hST : S ⊆ T) (hE : IsEProcess E ℱ T) : IsEProcess E ℱ S :=
  ⟨hE.adapted, fun τ hτ ↦ (hE.isEVar_stoppedValue τ hτ).anti_set hST⟩

/-- **Domination.** For a null of finite measures, an adapted process that is almost surely at most
an e-process at every time, under every member of the null, is an e-process. -/
theorem mono_ae (hS : ∀ P ∈ S, IsFiniteMeasure P) (hE : IsEProcess E ℱ S) (hF : Adapted ℱ F)
    (hFE : ∀ P ∈ S, ∀ n, F n ≤ᵐ[P] E n) : IsEProcess F ℱ S := by
  refine ⟨hF, fun τ hτ ↦ IsEVar.of_lintegral_le_measure_univ hS
    (hF.measurable_apply_stoppingTime hτ) fun P hP ↦ ?_⟩
  refine (lintegral_mono_ae ?_).trans
    ((hE.isEVar_stoppedValue τ hτ).lintegral_le_measure_univ P hP)
  filter_upwards [ae_all_iff.2 (hFE P hP)] with ω hω using hω (τ ω)

/-- **Domination.** For a null of finite measures, an adapted process that is at most an e-process
is an e-process. -/
theorem mono (hS : ∀ P ∈ S, IsFiniteMeasure P) (hE : IsEProcess E ℱ S) (hF : Adapted ℱ F)
    (hFE : F ≤ E) : IsEProcess F ℱ S :=
  hE.mono_ae hS hF fun _ _ n ↦ ae_of_all _ (hFE n)

end IsEProcess

/-- For a null of probability measures, a process is an e-process exactly when it is adapted and has
expectation at most `1` at every stopping time with values in `ℕ`, under every member of the null.
-/
theorem isEProcess_iff_lintegral_le_one (hS : ∀ P ∈ S, IsProbabilityMeasure P) :
    IsEProcess E ℱ S ↔ Adapted ℱ E ∧ ∀ τ : Ω → ℕ, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℕ)) →
      ∀ P ∈ S, ∫⁻ ω, E (τ ω) ω ∂P ≤ 1 := by
  refine ⟨fun hE ↦ ⟨hE.adapted, fun τ hτ P hP ↦ ?_⟩, fun h ↦ .of_lintegral_le_one hS h.1 h.2⟩
  have := hS P hP
  exact hE.lintegral_le_one hτ hP

/-- A process is an e-process for `S` exactly when it is adapted and an e-process for each simple
null `{P}` with `P ∈ S`. Adaptedness is needed only when `S` is empty. -/
theorem isEProcess_iff_forall_singleton :
    IsEProcess E ℱ S ↔ Adapted ℱ E ∧ ∀ P ∈ S, IsEProcess E ℱ {P} := by
  refine ⟨fun hE ↦ ⟨hE.adapted, fun P hP ↦ hE.anti_set (singleton_subset_iff.2 hP)⟩,
    fun ⟨hE, h⟩ ↦ ⟨hE, fun τ hτ ↦ ⟨hE.measurable_apply_stoppingTime hτ, fun P hP ↦ ?_,
      fun P hP ↦ ?_⟩⟩⟩
  · exact ((h P hP).isEVar_stoppedValue τ hτ).eintegral_ne_bot P (mem_singleton P)
  · exact ((h P hP).isEVar_stoppedValue τ hτ).eintegral_nonpos P (mem_singleton P)

/-- The constant process `1` is an e-process for every null and every filtration. -/
theorem isEProcess_one (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) : IsEProcess 1 ℱ S :=
  ⟨fun _ ↦ measurable_const, fun _ _ ↦ isEVar_one S⟩

/-- The e-processes for a null form a convex set: a convex combination `a • E + b • F`, with
`a + b = 1`, of two e-processes is an e-process. -/
theorem convex_isEProcess (ℱ : Filtration ℕ mΩ) (S : Set (Measure Ω)) :
    Convex ℝ≥0∞ {E : ℕ → Ω → ℝ≥0∞ | IsEProcess E ℱ S} := by
  intro E hE F hF a b ha hb hab
  exact ⟨fun n ↦ ((hE.adapted n).const_smul a).add ((hF.adapted n).const_smul b), fun τ hτ ↦
    convex_isEVar S (hE.isEVar_stoppedValue τ hτ) (hF.isEVar_stoppedValue τ hτ) ha hb hab⟩

/-- **Test supermartingales are e-processes** [RW, Fact 7.5]. By optional stopping, a test
supermartingale for a null of probability measures has expectation at most `1` at every stopping
time, so it is an e-process. -/
theorem IsTestSupermartingale.isEProcess (hS : ∀ P ∈ S, IsProbabilityMeasure P)
    {M : ℕ → Ω → ℝ≥0∞} (hM : IsTestSupermartingale M ℱ S) : IsEProcess M ℱ S :=
  ⟨hM.adapted, fun τ hτ ↦ by simpa using hM.isEVar_stoppedValueLimsup hS hτ⟩

end ProbabilityTheory
