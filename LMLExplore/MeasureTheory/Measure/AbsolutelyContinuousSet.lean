/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Absolute continuity with respect to a set of measures

A measure `Q` is absolutely continuous with respect to a set of measures `S`,
`Q.AbsolutelyContinuousSet S`, when every measurable set that is null for every member of `S` is
`Q`-null. For a singleton `{P}` this is `Q ≪ P`. This is the condition `Q ≪ S` under which the
e-variables for a null `S` are `Q`-almost surely finite [LRR25, Theorem 2.6].

## Main definitions

* `MeasureTheory.Measure.AbsolutelyContinuousSet Q S`: every measurable set that is null for every
  member of `S` is `Q`-null.

## Main statements

* `MeasureTheory.Measure.AbsolutelyContinuousSet.ae_of_forall_ae`: a property `p` with
  `{ω | p ω}` measurable that holds almost surely under every member of `S` holds `Q`-almost
  surely.
* `MeasureTheory.Measure.AbsolutelyContinuousSet.absolutelyContinuous`: `Q` is absolutely
  continuous with respect to every measure that dominates all members of `S`.
* `MeasureTheory.Measure.absolutelyContinuousSet_singleton_iff`: absolute continuity with respect
  to `{P}` is `Q ≪ P`.

## References

* [LRR25] M. Larsson, A. Ramdas and J. Ruf, *The numeraire e-variable and reverse information
  projection*, Ann. Statist. 53 (2025), arXiv:2402.18810v4, Theorem 2.6.
-/

public section

open MeasureTheory Set

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {S T : Set (Measure Ω)} {P Q Q' ν : Measure Ω}

namespace MeasureTheory.Measure

/-- A measure `Q` is absolutely continuous with respect to a set of measures `S` when every
measurable set that is null for every member of `S` is `Q`-null. For a singleton `{P}` this is
`Q ≪ P` (`MeasureTheory.Measure.absolutelyContinuousSet_singleton_iff`). -/
def AbsolutelyContinuousSet (Q : Measure Ω) (S : Set (Measure Ω)) : Prop :=
  ∀ ⦃s : Set Ω⦄, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0

/-- The defining property of `MeasureTheory.Measure.AbsolutelyContinuousSet`. -/
theorem absolutelyContinuousSet_iff :
    Q.AbsolutelyContinuousSet S ↔
      ∀ ⦃s : Set Ω⦄, MeasurableSet s → (∀ P ∈ S, P s = 0) → Q s = 0 :=
  Iff.rfl

/-- A measurable set that is null for every member of `S` is null for a measure absolutely
continuous with respect to `S`. -/
theorem AbsolutelyContinuousSet.measure_eq_zero (hQS : Q.AbsolutelyContinuousSet S) {s : Set Ω}
    (hs : MeasurableSet s) (h : ∀ P ∈ S, P s = 0) : Q s = 0 :=
  hQS hs h

/-- A property `p` with `{ω | p ω}` measurable that holds almost surely under every member of `S`
holds almost surely under a measure absolutely continuous with respect to `S`. This is the
counterpart of `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`. -/
theorem AbsolutelyContinuousSet.ae_of_forall_ae (hQS : Q.AbsolutelyContinuousSet S)
    {p : Ω → Prop} (hp : MeasurableSet {ω | p ω}) (h : ∀ P ∈ S, ∀ᵐ ω ∂P, p ω) :
    ∀ᵐ ω ∂Q, p ω :=
  ae_iff.mpr (hQS hp.compl fun P hP ↦ ae_iff.mp (h P hP))

/-- A measure absolutely continuous with respect to `S` is absolutely continuous with respect to
every measure `ν` that dominates all members of `S`. -/
theorem AbsolutelyContinuousSet.absolutelyContinuous (hQS : Q.AbsolutelyContinuousSet S)
    (h : ∀ P ∈ S, P ≪ ν) : Q ≪ ν :=
  .mk fun _ hs hνs ↦ hQS hs fun P hP ↦ h P hP hνs

/-- Absolute continuity with respect to a set of measures is monotone in the set. -/
theorem AbsolutelyContinuousSet.mono (hQS : Q.AbsolutelyContinuousSet S) (hST : S ⊆ T) :
    Q.AbsolutelyContinuousSet T :=
  fun _ hs h ↦ hQS hs fun P hP ↦ h P (hST hP)

/-- A measure absolutely continuous with respect to a measure absolutely continuous with respect
to `S` is absolutely continuous with respect to `S`. -/
theorem AbsolutelyContinuous.trans_absolutelyContinuousSet (hQ'Q : Q' ≪ Q)
    (hQS : Q.AbsolutelyContinuousSet S) : Q'.AbsolutelyContinuousSet S :=
  fun _ hs h ↦ hQ'Q (hQS hs h)

/-- Absolute continuity with respect to a singleton is absolute continuity. -/
@[simp]
theorem absolutelyContinuousSet_singleton_iff : Q.AbsolutelyContinuousSet {P} ↔ Q ≪ P :=
  ⟨fun h ↦ .mk fun _ hs hPs ↦ h hs (by simpa using hPs), fun h _ _ hs ↦ h (hs P rfl)⟩

/-- A measure absolutely continuous with respect to a member of `S` is absolutely continuous
with respect to `S`. -/
theorem AbsolutelyContinuous.absolutelyContinuousSet (hQP : Q ≪ P) (hP : P ∈ S) :
    Q.AbsolutelyContinuousSet S :=
  (absolutelyContinuousSet_singleton_iff.mpr hQP).mono (singleton_subset_iff.mpr hP)

end MeasureTheory.Measure
