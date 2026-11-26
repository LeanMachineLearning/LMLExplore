/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.PVariable
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The level attained by a statistic

A test of a null hypothesis `S : Set (Measure Ω)` that rejects for large values of a statistic
`T : Ω → β` rejects at `ω` at every level above the *level attained* at `ω` [Bah67],
`levelAttained T S ω = ⨆ P ∈ S, P {ω' | T ω ≤ T ω'}`: the largest probability, under a member of
the null, that the statistic is at least its observed value `T ω`. It is the p-value of the
statistic `T`.

For a measurable statistic with values in a linear order whose topology is order-closed and
hereditarily Lindelöf, for instance `ℝ`, `ℝ≥0∞` or any linear order with a second-countable
order-closed topology, the level attained is a p-variable for `S`, whatever the members of `S`.
The level attained by an e-variable is at most its inverse, by Markov's inequality, and the level
attained by the inverse of a p-variable is at most the p-variable.

## Main definitions

* `ProbabilityTheory.levelAttained T S`: the level attained by the statistic `T` against the null
  `S`.

## Main statements

* `ProbabilityTheory.measurable_levelAttained`: the level attained by a measurable statistic is
  measurable.
* `ProbabilityTheory.isPVar_levelAttained`: the level attained by a measurable statistic is a
  p-variable.
* `ProbabilityTheory.levelAttained_comp`: composing the statistic with an order embedding does not
  change its level attained.
* `ProbabilityTheory.IsEVar.levelAttained_le_inv`: the level attained by an e-variable is at most
  its inverse.
* `ProbabilityTheory.IsPVar.levelAttained_inv_le`: the level attained by the inverse of a
  p-variable is at most the p-variable.

## Implementation notes

The values `t` with `⨆ P ∈ S, P {ω' | t ≤ T ω'} ≤ α` form a set `A`, and the event
`{levelAttained T S ≤ α}` is `T ⁻¹' A`. If `A` has a least element `t₀`, this event is contained
in `{t₀ ≤ T}`, whose probability is at most `α`. Otherwise every element of `A` is above another
one, so `T ⁻¹' A` is contained in the union of the events `{t ≤ T}` over `t ∈ A`, and, since the
union of the open rays `Set.Ioi t` over `t ∈ A` is the union of countably many of them, over
countably many `t ∈ A`. These events form a chain, so the probability of their union is the
supremum of their probabilities (`Directed.measure_iUnion`, which asks no measurability), each at
most `α`. No finiteness of the members of `S` is needed.

First countability of the values does not suffice: on the first uncountable ordinal with the
reversed order and the Dieudonné measure, which charges the Borel sets that contain a closed
unbounded set, the level attained by the identity is `0` everywhere, so it is not a p-variable.

The definition and the statements are adapted from `EValuesResearch/Results/BahadurSlope.lean`
(commit `83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore.

## References

* [Bah67] R. R. Bahadur, *Rates of convergence of estimates and test statistics*, Ann. Math.
  Statist. 38 (1967), 303–324.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω β γ : Type*} {mΩ : MeasurableSpace Ω} {S S' : Set (Measure Ω)} {P : Measure Ω}

section LE

variable [LE β] {T : Ω → β}

/-- The **level attained** by a statistic `T` against a null `S`, at `ω` [Bah67]: the largest
probability, under a member of `S`, that the statistic is at least its observed value `T ω`. A
test that rejects for large values of `T` rejects at `ω` at every level above it. -/
noncomputable def levelAttained (T : Ω → β) (S : Set (Measure Ω)) (ω : Ω) : ℝ≥0∞ :=
  ⨆ P ∈ S, P {ω' | T ω ≤ T ω'}

/-- The definition of the level attained. -/
theorem levelAttained_def (T : Ω → β) (S : Set (Measure Ω)) (ω : Ω) :
    levelAttained T S ω = ⨆ P ∈ S, P {ω' | T ω ≤ T ω'} := (rfl)

/-- The level attained is at most `a` exactly when the probability, under every member of the
null, that the statistic is at least its observed value is at most `a`. -/
theorem levelAttained_le_iff {ω : Ω} {a : ℝ≥0∞} :
    levelAttained T S ω ≤ a ↔ ∀ P ∈ S, P {ω' | T ω ≤ T ω'} ≤ a :=
  iSup₂_le_iff

/-- The probability, under a member of the null, that the statistic is at least its observed
value is at most the level attained. -/
theorem measure_le_levelAttained (hP : P ∈ S) (ω : Ω) :
    P {ω' | T ω ≤ T ω'} ≤ levelAttained T S ω :=
  le_biSup (fun P ↦ P {ω' | T ω ≤ T ω'}) hP

/-- The level attained grows with the null. -/
theorem levelAttained_mono (hSS' : S ⊆ S') (ω : Ω) :
    levelAttained T S ω ≤ levelAttained T S' ω :=
  biSup_mono hSS'

/-- The level attained against the empty null is `0`. -/
@[simp]
theorem levelAttained_empty (T : Ω → β) : levelAttained T (∅ : Set (Measure Ω)) = 0 := by
  ext ω
  simp [levelAttained_def]

/-- Against a null of measures of mass at most one, the level attained is at most one. -/
theorem levelAttained_le_one (hS : ∀ P ∈ S, P univ ≤ 1) (ω : Ω) : levelAttained T S ω ≤ 1 :=
  levelAttained_le_iff.2 fun P hP ↦ (measure_mono (subset_univ _)).trans (hS P hP)

/-- Composing the statistic with an order embedding does not change its level attained. -/
theorem levelAttained_comp [LE γ] (f : β ↪o γ) (T : Ω → β) (S : Set (Measure Ω)) :
    levelAttained (f ∘ T) S = levelAttained T S := by
  ext ω
  simp [levelAttained_def, f.map_rel_iff]

end LE

/-- **The level attained by an e-variable is at most its inverse**, by Markov's inequality under
each member of the null. -/
theorem IsEVar.levelAttained_le_inv {E : Ω → ℝ≥0∞} (hE : IsEVar E S) (ω : Ω) :
    levelAttained E S ω ≤ (E ω)⁻¹ :=
  levelAttained_le_iff.2 fun P hP ↦ by simpa using hE.measure_inv_le_le hP (E ω)⁻¹

/-- **The level attained by the inverse of a p-variable is at most the p-variable**: the
statistic `p⁻¹` is large when `p` is small, and its level attained is the probability that `p`
is at most its observed value. -/
theorem IsPVar.levelAttained_inv_le {p : Ω → ℝ≥0∞} (hp : IsPVar p S) (ω : Ω) :
    levelAttained (fun ω ↦ (p ω)⁻¹) S ω ≤ p ω :=
  levelAttained_le_iff.2 fun P hP ↦ by simpa using hp.measure_le_le P hP (p ω)

section LinearOrder

variable [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β]
  [OpensMeasurableSpace β] {T : Ω → β}

/-- The level attained by a measurable statistic is measurable: it is an antitone function of the
statistic. -/
theorem measurable_levelAttained (hT : Measurable T) (S : Set (Measure Ω)) :
    Measurable (levelAttained T S) := by
  have hG : Antitone fun t : β ↦ ⨆ P ∈ S, P {ω' | t ≤ T ω'} := fun t t' htt' ↦
    iSup₂_mono fun P _ ↦ measure_mono fun ω' (h : t' ≤ T ω') ↦ htt'.trans h
  exact hG.measurable.comp hT

/-- **The level attained is a p-variable.** For a measurable statistic `T` with values in a linear
order whose topology is order-closed and hereditarily Lindelöf (for instance `ℝ` or `ℝ≥0∞`),
`P {levelAttained T S ≤ α} ≤ α` for every member `P` of `S` and every `α`. No finiteness of the
members of `S` is needed. -/
theorem isPVar_levelAttained [HereditarilyLindelofSpace β] (hT : Measurable T)
    (S : Set (Measure Ω)) : IsPVar (levelAttained T S) S := by
  refine ⟨measurable_levelAttained hT S, fun P hP α ↦ ?_⟩
  -- the values of the statistic whose level attained is at most `α`
  set A : Set β := {t | ⨆ P' ∈ S, P' {ω' | t ≤ T ω'} ≤ α}
  have hle (t : β) (ht : t ∈ A) : P {ω | t ≤ T ω} ≤ α :=
    (le_biSup (fun P' ↦ P' {ω' | t ≤ T ω'}) hP).trans ht
  change P (T ⁻¹' A) ≤ α
  by_cases hmin : ∃ t₀ ∈ A, ∀ t ∈ A, t₀ ≤ t
  · obtain ⟨t₀, ht₀, hmin⟩ := hmin
    exact (measure_mono (t := {ω | t₀ ≤ T ω}) fun ω hω ↦ hmin _ hω).trans (hle t₀ ht₀)
  -- every element of `A` is above another one, and countably many rays `Ioi t` cover `A`
  push Not at hmin
  obtain ⟨D, hDc, hDU⟩ := eq_open_union_countable (fun t : A ↦ Ioi (t : β)) fun _ ↦ isOpen_Ioi
  have : Countable D := hDc.to_subtype
  have hdir : Directed (· ⊆ ·) fun t : D ↦ {ω | ((t : A) : β) ≤ T ω} := fun a b ↦ by
    rcases le_total ((a : A) : β) ((b : A) : β) with h | h
    · exact ⟨a, subset_rfl, fun ω (hω : ((b : A) : β) ≤ T ω) ↦ h.trans hω⟩
    · exact ⟨b, fun ω (hω : ((a : A) : β) ≤ T ω) ↦ h.trans hω, subset_rfl⟩
  calc P (T ⁻¹' A)
  _ ≤ P (⋃ t : D, {ω | ((t : A) : β) ≤ T ω}) := by
    refine measure_mono fun ω (hω : T ω ∈ A) ↦ ?_
    obtain ⟨t, htA, ht⟩ := hmin (T ω) hω
    have hω' : T ω ∈ ⋃ i ∈ D, Ioi ((i : A) : β) := hDU ▸ mem_iUnion.2 ⟨⟨t, htA⟩, ht⟩
    obtain ⟨i, hiD, hi⟩ := mem_iUnion₂.1 hω'
    exact mem_iUnion.2 ⟨⟨i, hiD⟩, hi.le⟩
  _ = ⨆ t : D, P {ω | ((t : A) : β) ≤ T ω} := hdir.measure_iUnion
  _ ≤ α := iSup_le fun t ↦ hle _ (t : A).property

end LinearOrder

end ProbabilityTheory
