/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EProcess.Basic
public import LMLExplore.EValues.PVariable

/-!
# The quasi-sure filter of a null

A property holds `S`-quasi-surely when it holds `P`-almost surely for every member `P` of the null
`S : Set (Measure Ω)`. This file defines the filter `ProbabilityTheory.quasiSure S`, the supremum
of the filters `ae P` over `P ∈ S`, so that "almost surely under every member" is written
`∀ᶠ ω in quasiSure S, p ω`, `f =ᶠ[quasiSure S] g` and `f ≤ᶠ[quasiSure S] g`. The null is any set
of measures, with no domination: the quasi-sure filter of a dominated null is the almost
everywhere filter of a dominating mixture, but no such measure exists in general.

Among measurable functions, and among adapted processes for the process notions, e-variables,
p-variables, conditional e-variables, test supermartingales and e-processes depend on their argument
only up to quasi-sure equality; e-variables, conditional e-variables and e-processes are solid
(closed downward) in the quasi-sure order, and p-variables are closed upward in it. The regularity
cannot be dropped, as each of these notions includes measurability or adaptedness. This file states
those congruence and monotonicity lemmas with the quasi-sure filter.

## Main definitions

* `ProbabilityTheory.quasiSure S`: the quasi-sure filter of a null.

## Main statements

* `ProbabilityTheory.eventually_quasiSure_iff`: a property holds quasi-surely exactly when it holds
  almost surely under every member of the null; `eventuallyEq_quasiSure_iff` and
  `eventuallyLE_quasiSure_iff` are the forms for `=ᶠ` and `≤ᶠ`.
* `ProbabilityTheory.quasiSure_mono`, `quasiSure_union`, `quasiSure_singleton`,
  `quasiSure_empty`: the quasi-sure filter is monotone in the null, takes unions to suprema, and
  is the almost everywhere filter for a simple null.
* `ProbabilityTheory.IsEVar.mono_quasiSure`: a measurable function quasi-surely below an
  e-variable is an e-variable, the solidity of the set of e-variables in the quasi-sure form.
* The congruence lemmas `IsEVar.congr_quasiSure`, `IsPVar.congr_quasiSure`,
  `IsCondEVar.congr_quasiSure`, `IsTestSupermartingale.congr_quasiSure`,
  `IsEProcess.congr_quasiSure`, and the monotonicity lemmas `IsPVar.mono_quasiSure`,
  `IsCondEVar.mono_quasiSure`, `IsEProcess.mono_quasiSure`.

## References

* [RW] A. Ramdas and R. Wang, *Hypothesis Testing with E-values*, Foundations and Trends in
  Statistics 1 (2025), arXiv:2410.23614v6, Definitions 1.2 and 7.3.

The definition and `eventually_quasiSure_iff` follow the prototypes of `notes/book/Suggested.lean`
(commit `88fb487`) in the paper project `RemyDegenne/evalues_research` (Apache 2.0).
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S T : Set (Measure Ω)} {P : Measure Ω}

/-- The quasi-sure filter of a null `S`: the sets that have a null complement under every member
of `S`. A property holds eventually for it exactly when it holds almost surely under every member
of `S` (`eventually_quasiSure_iff`). -/
def quasiSure (S : Set (Measure Ω)) : Filter Ω :=
  ⨆ P ∈ S, ae P

@[simp]
theorem eventually_quasiSure_iff {p : Ω → Prop} :
    (∀ᶠ ω in quasiSure S, p ω) ↔ ∀ P ∈ S, ∀ᵐ ω ∂P, p ω := by
  simp only [quasiSure, eventually_iSup]

@[simp]
theorem mem_quasiSure_iff {s : Set Ω} : s ∈ quasiSure S ↔ ∀ P ∈ S, s ∈ ae P :=
  eventually_quasiSure_iff

theorem eventuallyEq_quasiSure_iff {β : Type*} {f g : Ω → β} :
    f =ᶠ[quasiSure S] g ↔ ∀ P ∈ S, f =ᵐ[P] g :=
  eventually_quasiSure_iff

theorem eventuallyLE_quasiSure_iff {β : Type*} [LE β] {f g : Ω → β} :
    f ≤ᶠ[quasiSure S] g ↔ ∀ P ∈ S, f ≤ᵐ[P] g :=
  eventually_quasiSure_iff

/-- The almost everywhere filter of a member is finer than the quasi-sure filter: a quasi-sure
property holds almost surely under each member. -/
theorem ae_le_quasiSure (hP : P ∈ S) : ae P ≤ quasiSure S :=
  le_biSup ae hP

/-- The universal property of the quasi-sure filter as a supremum: it is finer than a filter `f`
exactly when the almost everywhere filter of every member is. -/
theorem quasiSure_le_iff {f : Filter Ω} : quasiSure S ≤ f ↔ ∀ P ∈ S, ae P ≤ f :=
  iSup₂_le_iff

/-- A property that holds quasi-surely holds almost surely under every member. -/
theorem ae_of_eventually_quasiSure {p : Ω → Prop} (h : ∀ᶠ ω in quasiSure S, p ω) (hP : P ∈ S) :
    ∀ᵐ ω ∂P, p ω :=
  eventually_quasiSure_iff.1 h P hP

/-- A larger null has a coarser (larger) quasi-sure filter: fewer properties hold quasi-surely. -/
@[gcongr]
theorem quasiSure_mono (hST : S ⊆ T) : quasiSure S ≤ quasiSure T :=
  biSup_mono fun _ hP ↦ hST hP

@[simp]
theorem quasiSure_empty : quasiSure (∅ : Set (Measure Ω)) = ⊥ := by
  simp [quasiSure]

@[simp]
theorem quasiSure_singleton : quasiSure {P} = ae P := by
  simp [quasiSure]

theorem quasiSure_union : quasiSure (S ∪ T) = quasiSure S ⊔ quasiSure T :=
  iSup_union

/-! ### Congruence and monotonicity -/

section Variables

variable {X Y : Ω → ℝ≥0∞}

/-- A measurable function quasi-surely equal to an e-variable is an e-variable. -/
theorem IsEVar.congr_quasiSure (hX : IsEVar X S) (hY : Measurable Y) (hXY : X =ᶠ[quasiSure S] Y) :
    IsEVar Y S :=
  hX.congr hY (eventuallyEq_quasiSure_iff.1 hXY)

/-- The set of e-variables is solid in the quasi-sure order: a measurable function quasi-surely
below an e-variable is an e-variable. Measurability cannot be dropped, as every e-variable is
measurable. -/
theorem IsEVar.mono_quasiSure (hY : IsEVar Y S) (hX : Measurable X) (hXY : X ≤ᶠ[quasiSure S] Y) :
    IsEVar X S :=
  ⟨hX, fun _ hP ↦ (lintegral_mono_ae (ae_of_eventually_quasiSure hXY hP)).trans
    (hY.lintegral_le_one hP)⟩

/-- A measurable function quasi-surely at least a p-variable is a p-variable. -/
theorem IsPVar.mono_quasiSure (hX : IsPVar X S) (hY : Measurable Y) (hXY : X ≤ᶠ[quasiSure S] Y) :
    IsPVar Y S :=
  hX.mono hY (eventuallyLE_quasiSure_iff.1 hXY)

/-- A measurable function quasi-surely equal to a p-variable is a p-variable. -/
theorem IsPVar.congr_quasiSure (hX : IsPVar X S) (hY : Measurable Y) (hXY : X =ᶠ[quasiSure S] Y) :
    IsPVar Y S :=
  hX.congr hY (eventuallyEq_quasiSure_iff.1 hXY)

variable {m : MeasurableSpace Ω}

/-- A measurable function quasi-surely below a conditional e-variable is a conditional
e-variable. -/
theorem IsCondEVar.mono_quasiSure (hY : IsCondEVar Y m S) (hX : Measurable[mΩ] X)
    (hXY : X ≤ᶠ[quasiSure S] Y) : IsCondEVar X m S :=
  ⟨hX, fun P hP s hs ↦ (lintegral_mono_ae (ae_restrict_of_ae
    (ae_of_eventually_quasiSure hXY hP))).trans (hY.setLIntegral_le P hP s hs)⟩

/-- A measurable function quasi-surely equal to a conditional e-variable is a conditional
e-variable. -/
theorem IsCondEVar.congr_quasiSure (hX : IsCondEVar X m S) (hY : Measurable[mΩ] Y)
    (hXY : X =ᶠ[quasiSure S] Y) : IsCondEVar Y m S :=
  hX.congr hY (eventuallyEq_quasiSure_iff.1 hXY)

end Variables

section Processes

variable {ℱ : Filtration ℕ mΩ} {E F : ℕ → Ω → ℝ≥0∞}

/-- An adapted process quasi-surely equal at every time to a test supermartingale is a test
supermartingale. -/
theorem IsTestSupermartingale.congr_quasiSure (hE : IsTestSupermartingale E ℱ S)
    (hF : Adapted ℱ F) (hEF : ∀ n, E n =ᶠ[quasiSure S] F n) : IsTestSupermartingale F ℱ S :=
  hE.congr hF fun _ hP n ↦ ae_of_eventually_quasiSure (hEF n) hP

/-- An adapted process quasi-surely equal at every time to an e-process is an e-process. -/
theorem IsEProcess.congr_quasiSure (hE : IsEProcess E ℱ S) (hF : Adapted ℱ F)
    (hEF : ∀ n, E n =ᶠ[quasiSure S] F n) : IsEProcess F ℱ S :=
  hE.congr hF fun _ hP n ↦ ae_of_eventually_quasiSure (hEF n) hP

/-- An adapted process quasi-surely at most an e-process at every time is an e-process. -/
theorem IsEProcess.mono_quasiSure (hE : IsEProcess E ℱ S) (hF : Adapted ℱ F)
    (hFE : ∀ n, F n ≤ᶠ[quasiSure S] E n) : IsEProcess F ℱ S :=
  hE.mono_ae hF fun _ hP n ↦ ae_of_eventually_quasiSure (hFE n) hP

end Processes

end ProbabilityTheory
