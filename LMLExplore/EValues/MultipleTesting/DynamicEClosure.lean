/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.MultipleTesting.EClosure
public import LMLExplore.MeasureTheory.MeasurableSpace.Constructions

/-!
# Dynamic e-closure

Hypotheses arrive over time and their evidence keeps evolving. The hypotheses are indexed by a
type `ι`, with nulls `H : ι → Set (Measure Ω)`, and `I t : Finset ι` is the finite set of
hypotheses that have arrived at time `t`, nondecreasing in `t`. Data arrive along a filtration
`ℱ` indexed by `ℕ`. Under a probability measure `P` the active true nulls at time `t` are the
hypotheses `i ∈ I t` with `P ∈ H i` (`ProbabilityTheory.activeTrueNulls`). A candidate family
process `C : ℕ → Ω → Set (Finset ι)` certifies at each time a family `C t ω` of subsets of `I t`,
from which any rejection set may be selected after seeing the data. A loss `f N R : ℝ≥0∞`
measures the error of rejecting `R` when the active true nulls are `N`: the false discovery
proportion `fdp`, the family-wise loss `fwerLoss`, or any other loss.

The candidate family process controls the loss at stopping times at level `α`
(`ProbabilityTheory.ControlsStoppedLoss`) when, for every probability measure `P` and every
stopping time `τ` that is finite `P`-almost surely, the largest loss of the candidates at `τ` has
expectation at most `α` [dH26, Definition 2.1]; it controls the supremum loss
(`ProbabilityTheory.ControlsSupLoss`) when the supremum over all times of the largest loss of the
candidates has expectation at most `α` [dH26, Definition 2.2]. The second implies the first; for
an adapted and setwise persistent process (`Monotone C`) and a loss that depends only on the
rejected true nulls, both follow from control at every fixed time [dH26, Proposition 3.13].

A dynamic intersection e-process collection (`ProbabilityTheory.IsDynamicECollection`) is a
family `E S` of processes, indexed by the nonempty finite sets `S` of hypotheses, with `E S` an
e-process for the probability measures under which every hypothesis of `S` is true
[dH26, Definition 2.4]. It is future-extension coherent (`ProbabilityTheory.IsFutureCoherent`)
when adding hypotheses that have not arrived yet never decreases the current evidence,
`E (S ∩ I t) t ≤ E S t` [dH26, Definition 2.5], and time-monotone when every `E S` is
nondecreasing in time [dH26, Definition 2.7]. Its dynamic e-closure
(`ProbabilityTheory.dynamicEClosure`) at time `t` is the family of the sets `R ⊆ I t` with
`f S R ≤ α * E S t` for every nonempty `S ⊆ I t` [dH26, (3.1)].

The **dynamic e-closure principle** [dH26, Theorems 3.6–3.7 and 3.10–3.12]: for a coherent
collection, the dynamic e-closure controls the loss at stopping times; for a coherent and
time-monotone collection, it controls the supremum loss and is setwise persistent; and conversely
every adapted candidate family process that controls the loss at stopping times, or the supremum
loss, is contained in the dynamic e-closure of such a collection. The statements hold for every
loss vanishing when no hypothesis is a true null, with no bound on the loss: monotonicity in the
true nulls is used only by the converse, and locality in the rejection set only by persistence.
The false discovery proportion and the family-wise loss have all three properties
(`ProbabilityTheory.fdp_mono_left`, `ProbabilityTheory.fdp_inter_self`,
`ProbabilityTheory.fwerLoss_mono_left`, `ProbabilityTheory.fwerLoss_inter_self`).

The forward direction rests on random-intersection localization [dH26, Lemma 3.4]: the process
`ProbabilityTheory.trueNullProcess` that reads, at each time, the e-process of the active true
nulls is an e-process for `P`, because before a horizon `T` the active true nulls are those of
time `T` intersected with the current hypotheses, and coherence bounds their evidence by that of
the fixed set of true nulls of time `T`. The converse uses the normalized largest loss of the
candidates as evidence (`ProbabilityTheory.lossECollection`, and its running maximum
`ProbabilityTheory.runningLossECollection`) [dH26, Theorems 7.1–7.2]. With all hypotheses
present from the start, the dynamic e-closure at a fixed time is the e-closure
`ProbabilityTheory.eClosure` of the values of the collection at that time [dH26, Remark 3.8].

## Main definitions

* `ProbabilityTheory.activeTrueNulls H I P t`: the true nulls under `P` among the hypotheses
  `I t`.
* `ProbabilityTheory.IsDynamicECollection E H ℱ`: `E S` is an e-process for the intersection
  null of every nonempty `S`.
* `ProbabilityTheory.IsFutureCoherent E I`: future-extension coherence.
* `ProbabilityTheory.dynamicEClosure f α E I t ω`: the dynamic e-closure at time `t`.
* `ProbabilityTheory.ControlsStoppedLoss f α C H I ℱ`,
  `ProbabilityTheory.ControlsSupLoss f α C H I`: simultaneous control of the loss at stopping
  times and of the supremum loss.
* `ProbabilityTheory.trueNullProcess E H I P`: the process of the evidence of the active true
  nulls.
* `ProbabilityTheory.lossECollection f α C I`, `ProbabilityTheory.runningLossECollection f α C I`:
  the canonical collections of a candidate family process.

## Main statements

* `ProbabilityTheory.isEProcess_trueNullProcess`,
  `ProbabilityTheory.lintegral_iSup_trueNullProcess_le_one`: random-intersection localization
  [dH26, Lemma 3.4].
* `ProbabilityTheory.controlsStoppedLoss_dynamicEClosure`: the dynamic e-closure principle for
  stopped losses [dH26, Theorem 3.6].
* `ProbabilityTheory.controlsSupLoss_dynamicEClosure`, `ProbabilityTheory.monotone_dynamicEClosure`:
  the persistent dynamic e-closure principle [dH26, Theorem 3.7].
* `ProbabilityTheory.controlsStoppedLoss_iff_exists_subset_dynamicEClosure`,
  `ProbabilityTheory.controlsSupLoss_iff_exists_subset_dynamicEClosure`: the necessary and
  sufficient forms [dH26, Theorems 3.10–3.12].
* `ProbabilityTheory.ControlsSupLoss.controlsStoppedLoss`,
  `ProbabilityTheory.controlsSupLoss_of_monotone`: the supremum loss bounds the stopped losses,
  and for setwise persistent processes control at fixed times suffices [dH26, Proposition 3.13].
* `ProbabilityTheory.dynamicEClosure_const_univ`: with all hypotheses present, the dynamic
  e-closure is the fixed-time e-closure [dH26, Remark 3.8].

## References

* [dH26] R. de Heide, *Dynamic e-closure for online hypotheses with any-time-valid evidence:
  closure principles and projective mergers*, arXiv:2608.09927v1.
* [XSF+26] Z. Xu, A. Solari, L. Fischer, R. de Heide, A. Ramdas and J. Goeman, *Bringing closure
  to false discovery rate control: a general principle for multiple testing*,
  arXiv:2509.02517v3.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {H : ι → Set (Measure Ω)}
  {I : ℕ → Finset ι} {P : Measure Ω} {t u : ℕ}

/-! ### Active true nulls -/

/-- The active true nulls at time `t` under `P`: the hypotheses `i` of `I t` with `P ∈ H i`. -/
noncomputable def activeTrueNulls (H : ι → Set (Measure Ω)) (I : ℕ → Finset ι) (P : Measure Ω)
    (t : ℕ) : Finset ι := by
  classical exact (I t).filter fun i ↦ P ∈ H i

@[simp]
theorem mem_activeTrueNulls {i : ι} : i ∈ activeTrueNulls H I P t ↔ i ∈ I t ∧ P ∈ H i := by
  classical simp [activeTrueNulls]

theorem activeTrueNulls_subset : activeTrueNulls H I P t ⊆ I t :=
  fun _ hi ↦ (mem_activeTrueNulls.1 hi).1

/-- Before a time `u`, the active true nulls are those of time `u` that have already arrived. -/
theorem activeTrueNulls_eq_inter [DecidableEq ι] (hI : Monotone I) (htu : t ≤ u) :
    activeTrueNulls H I P t = activeTrueNulls H I P u ∩ I t := by
  ext i
  simp only [mem_activeTrueNulls, mem_inter]
  exact ⟨fun h ↦ ⟨⟨hI htu h.1, h.2⟩, h.1⟩, fun h ↦ ⟨h.2, h.1.2⟩⟩

theorem activeTrueNulls_mono (hI : Monotone I) : Monotone (activeTrueNulls H I P) :=
  fun _ _ htu _ hi ↦ mem_activeTrueNulls.2
    ⟨hI htu (mem_activeTrueNulls.1 hi).1, (mem_activeTrueNulls.1 hi).2⟩

/-- With all hypotheses present, the active true nulls are the true nulls. -/
@[simp]
theorem activeTrueNulls_const_univ [Fintype ι] :
    activeTrueNulls H (fun _ ↦ univ) P t = trueNulls H P := by
  ext i
  simp

/-! ### Dynamic intersection e-process collections -/

/-- A **dynamic intersection e-process collection** for the hypotheses `H` and the filtration `ℱ`
[dH26, Definition 2.4]: for every nonempty finite set `S` of hypotheses, `E S` is an e-process for
the probability measures under which every hypothesis of `S` is true. The process `E ∅` is free. -/
structure IsDynamicECollection (E : Finset ι → ℕ → Ω → ℝ≥0∞) (H : ι → Set (Measure Ω))
    (ℱ : Filtration ℕ mΩ) : Prop where
  /-- The process of a nonempty set of hypotheses is an e-process for its intersection null. -/
  isEProcess (S : Finset ι) (hS : S.Nonempty) :
    IsEProcess (E S) ℱ {P | IsProbabilityMeasure P ∧ ∀ i ∈ S, P ∈ H i}

/-- A dynamic intersection e-process collection for larger nulls is one for smaller nulls. -/
theorem IsDynamicECollection.anti {E : Finset ι → ℕ → Ω → ℝ≥0∞} {H' : ι → Set (Measure Ω)}
    (hE : IsDynamicECollection E H' ℱ) (hH : ∀ i, H i ⊆ H' i) : IsDynamicECollection E H ℱ where
  isEProcess S hS := (hE.isEProcess S hS).anti_set fun _ hP ↦
    Set.mem_ofPred.2 ⟨hP.1, fun i hi ↦ hH i (hP.2 i hi)⟩

/-- **Future-extension coherence** [dH26, Definition 2.5]: at every time `t`, adding to a set of
hypotheses some that have not arrived yet never decreases the evidence, `E (S ∩ I t) t ≤ E S t`
whenever `S ∩ I t` is nonempty. -/
structure IsFutureCoherent [DecidableEq ι] (E : Finset ι → ℕ → Ω → ℝ≥0∞) (I : ℕ → Finset ι) :
    Prop where
  /-- The evidence of the arrived hypotheses of `S` is at most that of `S`. -/
  le (S : Finset ι) (t : ℕ) (hS : (S ∩ I t).Nonempty) : E (S ∩ I t) t ≤ E S t

/-! ### The dynamic e-closure -/

section Closure

variable {f : Finset ι → Finset ι → ℝ≥0∞} {α : ℝ≥0∞} {E : Finset ι → ℕ → Ω → ℝ≥0∞} {ω : Ω}
  {R : Finset ι}

/-- The **dynamic e-closure** at time `t` of the collection `E` for the loss `f` at level `α`
[dH26, (3.1)]: the sets `R` of arrived hypotheses with `f S R ≤ α * E S t ω` for every nonempty
set `S` of arrived hypotheses. -/
def dynamicEClosure (f : Finset ι → Finset ι → ℝ≥0∞) (α : ℝ≥0∞) (E : Finset ι → ℕ → Ω → ℝ≥0∞)
    (I : ℕ → Finset ι) (t : ℕ) (ω : Ω) : Set (Finset ι) :=
  {R | R ⊆ I t ∧ ∀ S ⊆ I t, S.Nonempty → f S R ≤ α * E S t ω}

@[simp]
theorem mem_dynamicEClosure :
    R ∈ dynamicEClosure f α E I t ω ↔ R ⊆ I t ∧ ∀ S ⊆ I t, S.Nonempty → f S R ≤ α * E S t ω :=
  Iff.rfl

/-- **The fixed-time case** [dH26, Remark 3.8]: with all hypotheses present from the start, the
dynamic e-closure at time `t` is the e-closure of the values of the collection at time `t`, for a
loss vanishing when there are no true nulls. -/
theorem dynamicEClosure_const_univ [Fintype ι] (hf₀ : ∀ R, f ∅ R = 0) :
    dynamicEClosure f α E (fun _ ↦ univ) t ω = eClosure f α (fun S ↦ E S t) ω := by
  ext R
  simp only [mem_dynamicEClosure, subset_univ, true_and, forall_const, mem_eClosure]
  refine ⟨fun h S ↦ ?_, fun h S hS ↦ h S⟩
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [hf₀]
  · exact h S hS

/-- **Setwise persistence** [dH26, Theorem 3.7 (b)]: for a coherent and time-monotone collection
and a loss that vanishes when there are no true nulls and depends only on the rejected true nulls,
every set in the dynamic e-closure at time `t` stays in it at every later time. -/
theorem monotone_dynamicEClosure [DecidableEq ι] (hI : Monotone I) (hf₀ : ∀ R, f ∅ R = 0)
    (hf : ∀ S R, f S R = f (S ∩ R) R) (hcoh : IsFutureCoherent E I)
    (hmono : ∀ S, S.Nonempty → Monotone (E S)) :
    Monotone fun t ↦ dynamicEClosure f α E I t := by
  intro t u htu ω R ⟨hRI, hR⟩
  refine ⟨hRI.trans (hI htu), fun S _ hS ↦ ?_⟩
  -- The loss of `S` is the loss of its arrived hypotheses, since `R` has arrived.
  have hSR : f S R = f (S ∩ I t) R := by
    rw [hf S R, hf (S ∩ I t) R, inter_right_comm, inter_eq_left.2 (inter_subset_right.trans hRI)]
  rcases (S ∩ I t).eq_empty_or_nonempty with hB | hB
  · simp [hSR, hB, hf₀]
  calc f S R = f (S ∩ I t) R := hSR
    _ ≤ α * E (S ∩ I t) t ω := hR _ inter_subset_right hB
    _ ≤ α * E S u ω := by
      gcongr
      exact (hcoh.le S t hB ω).trans (hmono S hS htu ω)

end Closure

/-! ### Random-intersection localization -/

section Localization

variable {E : Finset ι → ℕ → Ω → ℝ≥0∞} {T : ℕ}

/-- The **evidence of the active true nulls** under `P`: at time `t`, the value of the process of
the active true nulls under `P`, and `0` when none is active [dH26, Lemma 3.4]. -/
noncomputable def trueNullProcess (E : Finset ι → ℕ → Ω → ℝ≥0∞) (H : ι → Set (Measure Ω))
    (I : ℕ → Finset ι) (P : Measure Ω) (t : ℕ) : Ω → ℝ≥0∞ :=
  if (activeTrueNulls H I P t).Nonempty then E (activeTrueNulls H I P t) t else 0

theorem trueNullProcess_of_nonempty (h : (activeTrueNulls H I P t).Nonempty) :
    trueNullProcess E H I P t = E (activeTrueNulls H I P t) t := by
  simp [trueNullProcess, h]

theorem trueNullProcess_of_eq_empty (h : activeTrueNulls H I P t = ∅) :
    trueNullProcess E H I P t = 0 := by
  simp [trueNullProcess, h]

theorem IsDynamicECollection.adapted_trueNullProcess (hE : IsDynamicECollection E H ℱ) :
    Adapted ℱ (trueNullProcess E H I P) := by
  intro t
  rcases (activeTrueNulls H I P t).eq_empty_or_nonempty with h | h
  · rw [trueNullProcess_of_eq_empty h]
    exact measurable_const
  · rw [trueNullProcess_of_nonempty h]
    exact (hE.isEProcess _ h).adapted t

/-- Before a horizon `T`, the evidence of the active true nulls is at most the evidence of the
fixed set of the true nulls active at `T`. -/
theorem trueNullProcess_le [DecidableEq ι] (hI : Monotone I) (hcoh : IsFutureCoherent E I)
    (htT : t ≤ T) : trueNullProcess E H I P t ≤ E (activeTrueNulls H I P T) t := by
  rcases (activeTrueNulls H I P t).eq_empty_or_nonempty with h | h
  · rw [trueNullProcess_of_eq_empty h]
    exact fun _ ↦ zero_le
  · rw [trueNullProcess_of_nonempty h]
    rw [activeTrueNulls_eq_inter hI htT] at h ⊢
    exact hcoh.le _ _ h

/-- Before a horizon `T` at which no true null is active, the evidence of the active true nulls
vanishes. -/
theorem trueNullProcess_eq_zero (hI : Monotone I) (htT : t ≤ T)
    (hT : activeTrueNulls H I P T = ∅) : trueNullProcess E H I P t = 0 := by
  classical
  exact trueNullProcess_of_eq_empty <| by rw [activeTrueNulls_eq_inter hI htT, hT, empty_inter]

/-- **Random-intersection localization** [dH26, Lemma 3.4, (3.4)]: for a coherent dynamic
intersection e-process collection, the evidence of the active true nulls under a probability
measure `P` is an e-process for `P`, although the set of active true nulls changes with time. -/
theorem isEProcess_trueNullProcess [DecidableEq ι] [IsProbabilityMeasure P] (hI : Monotone I)
    (hE : IsDynamicECollection E H ℱ) (hcoh : IsFutureCoherent E I) :
    IsEProcess (trueNullProcess E H I P) ℱ {P} := by
  refine .of_lintegral_le_one hE.adapted_trueNullProcess fun τ hτ T hτT Q hQ ↦ ?_
  rw [Set.mem_singleton_iff.1 hQ]
  have hle (ω : Ω) : (τ ω).untopA ≤ T := WithTop.untopA_le (hτT ω)
  rcases (activeTrueNulls H I P T).eq_empty_or_nonempty with hT | hT
  · have h0 (ω : Ω) : stoppedValue (trueNullProcess E H I P) τ ω = 0 := by
      simp only [stoppedValue, trueNullProcess_eq_zero hI (hle ω) hT, Pi.zero_apply]
    simp [h0]
  -- Before `T`, the evidence is dominated by the e-process of the true nulls active at `T`.
  refine (lintegral_mono fun ω ↦ trueNullProcess_le hI hcoh (hle ω) ω).trans ?_
  exact ((hE.isEProcess _ hT).isEVar_stoppedValue_of_le hτ hτT).lintegral_le_one
    ⟨inferInstance, fun i hi ↦ (mem_activeTrueNulls.1 hi).2⟩

/-- For a coherent and time-monotone collection, the evidence of the active true nulls is
nondecreasing in time. -/
theorem monotone_trueNullProcess [DecidableEq ι] (hI : Monotone I) (hcoh : IsFutureCoherent E I)
    (hmono : ∀ S, S.Nonempty → Monotone (E S)) : Monotone (trueNullProcess E H I P) := by
  intro t u htu
  rcases (activeTrueNulls H I P u).eq_empty_or_nonempty with hu | hu
  · rw [trueNullProcess_eq_zero hI htu hu, trueNullProcess_eq_zero hI le_rfl hu]
  · rw [trueNullProcess_of_nonempty hu]
    exact (trueNullProcess_le hI hcoh htu).trans (hmono _ hu htu)

/-- **Random-intersection localization**, maximal form [dH26, Lemma 3.4, (3.5)]: for a coherent
and time-monotone dynamic intersection e-process collection, the supremum over time of the
evidence of the active true nulls has expectation at most one under every probability measure. -/
theorem lintegral_iSup_trueNullProcess_le_one [DecidableEq ι] [IsProbabilityMeasure P]
    (hI : Monotone I) (hE : IsDynamicECollection E H ℱ) (hcoh : IsFutureCoherent E I)
    (hmono : ∀ S, S.Nonempty → Monotone (E S)) :
    ∫⁻ ω, ⨆ t, trueNullProcess E H I P t ω ∂P ≤ 1 := by
  have hZ := isEProcess_trueNullProcess hI hE hcoh (P := P)
  rw [lintegral_iSup hZ.measurable (monotone_trueNullProcess hI hcoh hmono)]
  exact iSup_le fun t ↦ (hZ.isEVar t).lintegral_le_one (Set.mem_singleton P)

end Localization

/-! ### Simultaneous control and the forward principles -/

section Control

variable {f : Finset ι → Finset ι → ℝ≥0∞} {α : ℝ≥0∞} {E : Finset ι → ℕ → Ω → ℝ≥0∞}
  {C C' : ℕ → Ω → Set (Finset ι)}

/-- The largest loss of the members of the dynamic e-closure, for the active true nulls under `P`,
is at most `α` times the evidence of the active true nulls, for a loss vanishing when there are no
true nulls. -/
theorem biSup_dynamicEClosure_le (hf₀ : ∀ R, f ∅ R = 0) (t : ℕ) (ω : Ω) :
    ⨆ R ∈ dynamicEClosure f α E I t ω, f (activeTrueNulls H I P t) R ≤
      α * trueNullProcess E H I P t ω := by
  refine iSup₂_le fun R hR ↦ ?_
  rcases (activeTrueNulls H I P t).eq_empty_or_nonempty with h | h
  · simp [h, hf₀]
  · rw [trueNullProcess_of_nonempty h]
    exact hR.2 _ activeTrueNulls_subset h

/-- The candidate family process `C` **controls the loss `f` at stopping times** at level `α`
[dH26, Definition 2.1]: for every probability measure `P` and every stopping time `τ` that is
finite `P`-almost surely, the largest loss of the candidates at `τ`, for the true nulls active at
`τ`, has expectation at most `α`. -/
structure ControlsStoppedLoss (f : Finset ι → Finset ι → ℝ≥0∞) (α : ℝ≥0∞)
    (C : ℕ → Ω → Set (Finset ι)) (H : ι → Set (Measure Ω)) (I : ℕ → Finset ι)
    (ℱ : Filtration ℕ mΩ) : Prop where
  /-- The expected largest loss at a stopping time is at most `α`. -/
  lintegral_le (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → WithTop ℕ}
    (hτ : IsStoppingTime ℱ τ) (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∫⁻ ω, stoppedValue (fun t ω ↦ ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R) τ ω ∂P ≤ α

/-- The candidate family process `C` **controls the supremum loss** `f` at level `α`
[dH26, Definition 2.2]: for every probability measure `P`, the supremum over time of the largest
loss of the candidates, for the active true nulls, has expectation at most `α`. -/
structure ControlsSupLoss (f : Finset ι → Finset ι → ℝ≥0∞) (α : ℝ≥0∞)
    (C : ℕ → Ω → Set (Finset ι)) (H : ι → Set (Measure Ω)) (I : ℕ → Finset ι) : Prop where
  /-- The expected supremum over time of the largest loss is at most `α`. -/
  lintegral_iSup_le (P : Measure Ω) [IsProbabilityMeasure P] :
    ∫⁻ ω, ⨆ t, ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R ∂P ≤ α

/-- Control at stopping times passes to smaller candidate families. -/
theorem ControlsStoppedLoss.mono (h : ControlsStoppedLoss f α C' H I ℱ)
    (hC : ∀ t ω, C t ω ⊆ C' t ω) : ControlsStoppedLoss f α C H I ℱ where
  lintegral_le P _ _ hτ hτ_top := (lintegral_mono fun ω ↦ biSup_mono fun _ hR ↦
    hC _ ω hR).trans (h.lintegral_le P hτ hτ_top)

/-- Control of the supremum loss passes to smaller candidate families. -/
theorem ControlsSupLoss.mono (h : ControlsSupLoss f α C' H I) (hC : ∀ t ω, C t ω ⊆ C' t ω) :
    ControlsSupLoss f α C H I where
  lintegral_iSup_le P _ := (lintegral_mono fun ω ↦ iSup_mono fun t ↦ biSup_mono fun _ hR ↦
    hC t ω hR).trans (h.lintegral_iSup_le P)

/-- **Control of the supremum loss gives control at stopping times** [dH26, §2.3]: the loss at a
stopping time is at most the supremum over time of the loss. -/
theorem ControlsSupLoss.controlsStoppedLoss (h : ControlsSupLoss f α C H I) :
    ControlsStoppedLoss f α C H I ℱ where
  lintegral_le P _ τ _ _ := (lintegral_mono fun ω ↦
    le_iSup (fun t ↦ ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R) (τ ω).untopA).trans
      (h.lintegral_iSup_le P)

/-- **The dynamic e-closure principle for stopped losses** [dH26, Theorem 3.6]: the dynamic
e-closure of a coherent dynamic intersection e-process collection controls, at every level `α`,
every loss vanishing when there are no true nulls at stopping times. With `fdp`, it controls the
simultaneous stopped false discovery rate. -/
theorem controlsStoppedLoss_dynamicEClosure [DecidableEq ι] (hI : Monotone I) (hf₀ : ∀ R, f ∅ R = 0)
    (hE : IsDynamicECollection E H ℱ) (hcoh : IsFutureCoherent E I) :
    ControlsStoppedLoss f α (dynamicEClosure f α E I) H I ℱ where
  lintegral_le P _ τ hτ hτ_top := by
    have hZ := isEProcess_trueNullProcess hI hE hcoh (P := P)
    calc ∫⁻ ω, stoppedValue (fun t ω ↦ ⨆ R ∈ dynamicEClosure f α E I t ω,
          f (activeTrueNulls H I P t) R) τ ω ∂P
        ≤ ∫⁻ ω, α * stoppedValue (trueNullProcess E H I P) τ ω ∂P :=
          lintegral_mono fun ω ↦ biSup_dynamicEClosure_le hf₀ _ ω
      _ = α * ∫⁻ ω, stoppedValue (trueNullProcess E H I P) τ ω ∂P :=
          lintegral_const_mul α (hZ.measurable_stoppedValue hτ)
      _ ≤ α := mul_le_of_le_one_right' (hZ.lintegral_le_one_of_ae hτ hτ_top (Set.mem_singleton P))

/-- **The persistent dynamic e-closure principle** [dH26, Theorem 3.7 (a)]: the dynamic e-closure
of a coherent and time-monotone dynamic intersection e-process collection controls, at every level
`α`, the supremum loss of every loss vanishing when there are no true nulls. With `fdp`, it
controls the simultaneous SupFDR. Its candidate families are setwise persistent
(`ProbabilityTheory.monotone_dynamicEClosure`). -/
theorem controlsSupLoss_dynamicEClosure [DecidableEq ι] (hI : Monotone I) (hf₀ : ∀ R, f ∅ R = 0)
    (hE : IsDynamicECollection E H ℱ) (hcoh : IsFutureCoherent E I)
    (hmono : ∀ S, S.Nonempty → Monotone (E S)) :
    ControlsSupLoss f α (dynamicEClosure f α E I) H I where
  lintegral_iSup_le P _ := by
    have hZ := isEProcess_trueNullProcess hI hE hcoh (P := P)
    calc ∫⁻ ω, ⨆ t, ⨆ R ∈ dynamicEClosure f α E I t ω, f (activeTrueNulls H I P t) R ∂P
        ≤ ∫⁻ ω, α * ⨆ t, trueNullProcess E H I P t ω ∂P := by
          refine lintegral_mono fun ω ↦ iSup_le fun t ↦ (biSup_dynamicEClosure_le hf₀ t ω).trans ?_
          gcongr
          exact le_iSup (fun t ↦ trueNullProcess E H I P t ω) t
      _ = α * ∫⁻ ω, ⨆ t, trueNullProcess E H I P t ω ∂P :=
          lintegral_const_mul α (Measurable.iSup hZ.measurable)
      _ ≤ α := mul_le_of_le_one_right' (lintegral_iSup_trueNullProcess_le_one hI hE hcoh hmono)

end Control

/-! ### Canonical collections and the necessary and sufficient principles -/

section Converse

variable [DecidableEq ι] {f : Finset ι → Finset ι → ℝ≥0∞} {α : ℝ≥0∞}
  {C : ℕ → Ω → Set (Finset ι)}

/-- The **canonical collection** of a candidate family process [dH26, Theorem 7.1]: the evidence of
`S` at time `t` is the largest loss of the candidates for the arrived hypotheses of `S`, divided by
the level. -/
noncomputable def lossECollection (f : Finset ι → Finset ι → ℝ≥0∞) (α : ℝ≥0∞)
    (C : ℕ → Ω → Set (Finset ι)) (I : ℕ → Finset ι) (S : Finset ι) (t : ℕ) (ω : Ω) : ℝ≥0∞ :=
  α⁻¹ * ⨆ R ∈ C t ω, f (S ∩ I t) R

theorem lossECollection_def (S : Finset ι) (t : ℕ) :
    lossECollection f α C I S t = fun ω ↦ α⁻¹ * ⨆ R ∈ C t ω, f (S ∩ I t) R := (rfl)

/-- The **canonical running collection** of a candidate family process [dH26, Theorem 7.2]: the
evidence of `S` at time `t` is the largest loss of the candidates up to time `t`, for the
hypotheses of `S` arrived at each time, divided by the level. -/
noncomputable def runningLossECollection (f : Finset ι → Finset ι → ℝ≥0∞) (α : ℝ≥0∞)
    (C : ℕ → Ω → Set (Finset ι)) (I : ℕ → Finset ι) (S : Finset ι) (t : ℕ) (ω : Ω) : ℝ≥0∞ :=
  α⁻¹ * ⨆ (u) (_ : u ≤ t), ⨆ R ∈ C u ω, f (S ∩ I u) R

theorem runningLossECollection_def (S : Finset ι) (t : ℕ) :
    runningLossECollection f α C I S t =
      fun ω ↦ α⁻¹ * ⨆ (u) (_ : u ≤ t), ⨆ R ∈ C u ω, f (S ∩ I u) R := (rfl)

/-- The canonical collection is coherent, with equality. -/
theorem isFutureCoherent_lossECollection : IsFutureCoherent (lossECollection f α C I) I where
  le S t _ ω := by simp only [lossECollection_def, inter_assoc, inter_self, le_refl]

/-- The canonical running collection is coherent, with equality. -/
theorem isFutureCoherent_runningLossECollection (hI : Monotone I) :
    IsFutureCoherent (runningLossECollection f α C I) I where
  le S t _ ω := le_of_eq <| by
    simp only [runningLossECollection_def]
    congr 1
    exact biSup_congr fun u hu ↦ by rw [inter_assoc, inter_eq_right.2 (hI hu)]

/-- The canonical running collection is nondecreasing in time. -/
theorem monotone_runningLossECollection (S : Finset ι) :
    Monotone (runningLossECollection f α C I S) := by
  intro t t' htt' ω
  simp only [runningLossECollection_def]
  gcongr α⁻¹ * ?_
  exact iSup₂_le fun u (hu : u ≤ t) ↦
    le_iSup₂_of_le (f := fun u (_ : u ≤ t') ↦ ⨆ R ∈ C u ω, f (S ∩ I u) R) u (hu.trans htt') le_rfl

/-- Every candidate family process is contained in the dynamic e-closure of its canonical
collection, at a level `α ∉ {0, ∞}`. -/
theorem subset_dynamicEClosure_lossECollection (hα₀ : α ≠ 0) (hα : α ≠ ∞)
    (hCI : ∀ t ω, ∀ R ∈ C t ω, R ⊆ I t) (t : ℕ) (ω : Ω) :
    C t ω ⊆ dynamicEClosure f α (lossECollection f α C I) I t ω := by
  refine fun R hR ↦ ⟨hCI t ω R hR, fun S hS _ ↦ ?_⟩
  simp only [lossECollection_def]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hα₀ hα, one_mul, inter_eq_left.2 hS]
  exact le_iSup₂_of_le R hR le_rfl

/-- Every candidate family process is contained in the dynamic e-closure of its canonical running
collection, at a level `α ∉ {0, ∞}`. -/
theorem subset_dynamicEClosure_runningLossECollection (hα₀ : α ≠ 0) (hα : α ≠ ∞)
    (hCI : ∀ t ω, ∀ R ∈ C t ω, R ⊆ I t) (t : ℕ) (ω : Ω) :
    C t ω ⊆ dynamicEClosure f α (runningLossECollection f α C I) I t ω := by
  refine fun R hR ↦ ⟨hCI t ω R hR, fun S hS _ ↦ ?_⟩
  simp only [runningLossECollection_def]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hα₀ hα, one_mul]
  refine le_iSup₂_of_le t le_rfl (le_iSup₂_of_le R hR ?_)
  rw [inter_eq_left.2 hS]

/-- For a loss nondecreasing in the true nulls, the loss of the arrived hypotheses of a set of
true nulls is at most the loss of the active true nulls. -/
private lemma le_activeTrueNulls (hf : ∀ S S' R, S ⊆ S' → f S R ≤ f S' R) {S : Finset ι}
    (hP : ∀ i ∈ S, P ∈ H i) (t : ℕ) (R : Finset ι) :
    f (S ∩ I t) R ≤ f (activeTrueNulls H I P t) R :=
  hf _ _ _ fun i hi ↦ mem_activeTrueNulls.2 ⟨(mem_inter.1 hi).2, hP i (mem_inter.1 hi).1⟩

/-- The canonical collection of an adapted candidate family process that controls the loss at
stopping times is a dynamic intersection e-process collection, for a loss nondecreasing in the
true nulls and a level `α ≠ 0` [dH26, Theorem 7.1]. -/
theorem ControlsStoppedLoss.isDynamicECollection_lossECollection
    (h : ControlsStoppedLoss f α C H I ℱ) (hα₀ : α ≠ 0)
    (hf : ∀ S S' R, S ⊆ S' → f S R ≤ f S' R) (hC : Adapted ℱ C)
    (hCI : ∀ t ω, ∀ R ∈ C t ω, R ⊆ I t) :
    IsDynamicECollection (lossECollection f α C I) H ℱ where
  isEProcess S _ := by
    refine .of_lintegral_le_one (fun t ↦ ?_) fun τ hτ T hτT P hPS ↦ ?_
    · rw [lossECollection_def]
      exact (Measurable.biSup_of_forall_subset (hC t) (hCI t) _).const_mul _
    obtain ⟨_, hP⟩ := hPS
    calc ∫⁻ ω, stoppedValue (lossECollection f α C I S) τ ω ∂P
        ≤ ∫⁻ ω, α⁻¹ * stoppedValue (fun t ω ↦ ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R) τ ω ∂P :=
          lintegral_mono fun ω ↦ by
            simp only [stoppedValue, lossECollection_def]
            gcongr with R hR
            exact le_activeTrueNulls hf hP _ R
      _ = α⁻¹ * ∫⁻ ω, stoppedValue (fun t ω ↦ ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R) τ ω ∂P :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hα₀)
      _ ≤ α⁻¹ * α := by
          gcongr
          exact h.lintegral_le P hτ (.of_forall fun ω ↦ WithTop.ne_top_of_le_natCast (hτT ω))
      _ ≤ 1 := by
          rcases eq_or_ne α ∞ with rfl | hα
          · simp
          · rw [ENNReal.inv_mul_cancel hα₀ hα]

/-- The canonical running collection of an adapted candidate family process that controls the
supremum loss is a dynamic intersection e-process collection, for a loss nondecreasing in the
true nulls and a level `α ≠ 0` [dH26, Theorem 7.2]. -/
theorem ControlsSupLoss.isDynamicECollection_runningLossECollection
    (h : ControlsSupLoss f α C H I) (hα₀ : α ≠ 0) (hf : ∀ S S' R, S ⊆ S' → f S R ≤ f S' R)
    (hC : Adapted ℱ C) (hCI : ∀ t ω, ∀ R ∈ C t ω, R ⊆ I t) :
    IsDynamicECollection (runningLossECollection f α C I) H ℱ where
  isEProcess S _ := by
    refine .of_lintegral_le_one (fun t ↦ ?_) fun τ _ _ _ P hPS ↦ ?_
    · rw [runningLossECollection_def]
      refine Measurable.const_mul
        (Measurable.biSup (Set.Iic t) (Set.to_countable _) fun u hu ↦ ?_) _
      exact (Measurable.biSup_of_forall_subset (hC u) (hCI u) _).mono (ℱ.mono hu) le_rfl
    obtain ⟨_, hP⟩ := hPS
    calc ∫⁻ ω, stoppedValue (runningLossECollection f α C I S) τ ω ∂P
        ≤ ∫⁻ ω, α⁻¹ * ⨆ t, ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R ∂P :=
          lintegral_mono fun ω ↦ by
            simp only [stoppedValue, runningLossECollection_def]
            gcongr with u
            exact iSup_le fun _ ↦ iSup₂_mono fun R _ ↦ le_activeTrueNulls hf hP u R
      _ = α⁻¹ * ∫⁻ ω, ⨆ t, ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R ∂P :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hα₀)
      _ ≤ α⁻¹ * α := by
          gcongr
          exact h.lintegral_iSup_le P
      _ ≤ 1 := by
          rcases eq_or_ne α ∞ with rfl | hα
          · simp
          · rw [ENNReal.inv_mul_cancel hα₀ hα]

/-- **The necessary and sufficient dynamic e-closure principle for stopped losses**
[dH26, Theorems 3.10 and 3.12]: for a loss vanishing when there are no true nulls and
nondecreasing in the true nulls, and a level `α ∉ {0, ∞}`, an adapted candidate family process of
sets of arrived hypotheses controls the loss at stopping times exactly when it is contained in the
dynamic e-closure of a coherent dynamic intersection e-process collection. With `fdp`, this
characterizes the control of the simultaneous stopped false discovery rate. -/
theorem controlsStoppedLoss_iff_exists_subset_dynamicEClosure (hI : Monotone I) (hα₀ : α ≠ 0)
    (hα : α ≠ ∞) (hf₀ : ∀ R, f ∅ R = 0) (hf : ∀ S S' R, S ⊆ S' → f S R ≤ f S' R)
    (hC : Adapted ℱ C) (hCI : ∀ t ω, ∀ R ∈ C t ω, R ⊆ I t) :
    ControlsStoppedLoss f α C H I ℱ ↔ ∃ E : Finset ι → ℕ → Ω → ℝ≥0∞,
      IsDynamicECollection E H ℱ ∧ IsFutureCoherent E I ∧
        ∀ t ω, C t ω ⊆ dynamicEClosure f α E I t ω :=
  ⟨fun h ↦ ⟨_, h.isDynamicECollection_lossECollection hα₀ hf hC hCI,
      isFutureCoherent_lossECollection, subset_dynamicEClosure_lossECollection hα₀ hα hCI⟩,
    fun ⟨_, hE, hcoh, hCE⟩ ↦ (controlsStoppedLoss_dynamicEClosure hI hf₀ hE hcoh).mono hCE⟩

/-- **The necessary and sufficient dynamic e-closure principle for supremum losses**
[dH26, Theorems 3.11 and 3.12]: for a loss vanishing when there are no true nulls and
nondecreasing in the true nulls, and a level `α ∉ {0, ∞}`, an adapted candidate family process of
sets of arrived hypotheses controls the supremum loss exactly when it is contained in the dynamic
e-closure of a coherent and time-monotone dynamic intersection e-process collection. With `fdp`,
this characterizes the control of the simultaneous SupFDR. -/
theorem controlsSupLoss_iff_exists_subset_dynamicEClosure (hI : Monotone I) (hα₀ : α ≠ 0)
    (hα : α ≠ ∞) (hf₀ : ∀ R, f ∅ R = 0) (hf : ∀ S S' R, S ⊆ S' → f S R ≤ f S' R)
    (hC : Adapted ℱ C) (hCI : ∀ t ω, ∀ R ∈ C t ω, R ⊆ I t) :
    ControlsSupLoss f α C H I ↔ ∃ E : Finset ι → ℕ → Ω → ℝ≥0∞,
      IsDynamicECollection E H ℱ ∧ IsFutureCoherent E I ∧ (∀ S, S.Nonempty → Monotone (E S)) ∧
        ∀ t ω, C t ω ⊆ dynamicEClosure f α E I t ω :=
  ⟨fun h ↦ ⟨_, h.isDynamicECollection_runningLossECollection hα₀ hf hC hCI,
      isFutureCoherent_runningLossECollection hI, fun S _ ↦ monotone_runningLossECollection S,
      subset_dynamicEClosure_runningLossECollection hα₀ hα hCI⟩,
    fun ⟨_, hE, hcoh, hmono, hCE⟩ ↦
      (controlsSupLoss_dynamicEClosure hI hf₀ hE hcoh hmono).mono hCE⟩

/-- **Persistence collapses the error criteria** [dH26, Proposition 3.13]: for a setwise
persistent adapted candidate family process of sets of arrived hypotheses and a loss that depends
only on the rejected true nulls, control of the loss at every fixed time gives control of the
supremum loss, hence at stopping times. -/
theorem controlsSupLoss_of_monotone (hI : Monotone I) (hf : ∀ S R, f S R = f (S ∩ R) R)
    (hC : Adapted ℱ C) (hCI : ∀ t ω, ∀ R ∈ C t ω, R ⊆ I t) (hCmono : Monotone C)
    (h : ∀ (P : Measure Ω) [IsProbabilityMeasure P] (t : ℕ),
      ∫⁻ ω, ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R ∂P ≤ α) :
    ControlsSupLoss f α C H I where
  lintegral_iSup_le P _ := by
    -- A candidate stays a candidate, with the same loss: the loss of a set of arrived hypotheses
    -- does not see the true nulls that arrive later.
    have hmono : Monotone fun t ω ↦ ⨆ R ∈ C t ω, f (activeTrueNulls H I P t) R := by
      intro t u htu ω
      refine iSup₂_le fun R hR ↦ le_iSup₂_of_le R (hCmono htu ω hR) (le_of_eq ?_)
      rw [hf, hf (activeTrueNulls H I P u), activeTrueNulls_eq_inter hI htu, inter_right_comm,
        inter_eq_left.2 (inter_subset_right.trans (hCI t ω R hR))]
    rw [lintegral_iSup (fun t ↦ (Measurable.biSup_of_forall_subset (hC t) (hCI t) _).mono
      (ℱ.le t) le_rfl) hmono]
    exact iSup_le (h P)

end Converse

end ProbabilityTheory
