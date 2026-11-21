/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Process.Stopping
public import LMLExplore.Data.ENat.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Stopping times valued in `WithTop ℕ` and stopped adapted processes

A stopping time of a filtration indexed by `ℕ` takes values in `WithTop ℕ`, which Mathlib equips
with its Borel σ-algebra, and `IsStoppingTime.measurable'` is measurability for that σ-algebra.
The same type seen as `ℕ∞` carries the discrete σ-algebra `⊤`; the two instances are not
syntactically equal. This file states measurability of such a stopping time for the discrete
σ-algebra of `ℕ∞`. It also restates Mathlib's stopping-time API for `WithTop ℕ`-valued times at
the cast `(n : WithTop ℕ)` of a natural number.

A process that is adapted, in the sense of measurability, to a filtration indexed by a discrete
order stays adapted when it is stopped at a stopping time; Mathlib states this for strongly adapted
processes. Finally, two stopping times can be glued along an event known at an earlier stopping
time, which is how a statistician switches between two stopping rules after seeing the data.

## Main statements

* `MeasureTheory.IsStoppingTime.measurable_enat`: a stopping time `τ : Ω → ℕ∞` of a filtration
  indexed by `ℕ` is measurable for the discrete σ-algebra of `ℕ∞`.
* `MeasureTheory.IsStoppingTime.measurableSet_le_natCast`,
  `MeasureTheory.IsStoppingTime.measurableSet_natCast_lt`, `MeasureTheory.isStoppingTime_natCast`,
  `MeasureTheory.IsStoppingTime.min_natCast`: Mathlib's stopping-time API for `WithTop ℕ`-valued
  times, stated at the cast `(n : WithTop ℕ)` rather than the coercion `WithTop.some n`.
* `MeasureTheory.isStoppingTime_add_one_iff`: for filtrations with `𝒢 (n + 1) = ℱ n`, a time `τ`
  is a stopping time of `ℱ` exactly when `τ + 1` is one of `𝒢`.
* `MeasureTheory.Adapted.shift`, `MeasureTheory.adapted_shift_iff`: for filtrations with
  `𝒢 (n + 1) = ℱ n`, a process `M` with `M 0` measurable at time `0` is adapted to `𝒢` exactly
  when its shift `fun n ↦ M (n + 1)` is adapted to `ℱ`.
* `MeasureTheory.IsStoppingTime.eq_of_forall_le`: a stopping time of the coordinate filtration
  `Filtration.piLE` is determined, where it is finite, by the coordinates up to it.
* `MeasureTheory.Adapted.stoppedProcess_of_discrete`: a stopped adapted process is adapted.
* `MeasureTheory.IsStoppingTime.piecewise_of_stoppingTime_le`: two stopping times at least a
  stopping time `ρ`, glued along a set of the σ-algebra at `ρ`, form a stopping time.
-/

public section

open TopologicalSpace

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {f : Filtration ℕ mΩ} {τ : Ω → ℕ∞}

/-- A stopping time `τ : Ω → ℕ∞` of a filtration indexed by `ℕ` is measurable for the discrete
σ-algebra of `ℕ∞`.

`IsStoppingTime.measurable'` gives measurability for the Borel σ-algebra of `WithTop ℕ`, a
different instance on the same type. -/
lemma measurable_enat (hτ : IsStoppingTime f τ) : Measurable τ :=
  -- the preimage of each (Borel-measurable) singleton is measurable
  measurable_to_countable' fun x ↦ hτ.measurable' (measurableSet_singleton (α := WithTop ℕ) x)

end MeasureTheory.IsStoppingTime

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- If the indexing order has the discrete topology, then the stopped process of an adapted
process with values in a second-countable pseudo-metrizable Borel space is adapted. This is the
measurable form of Mathlib's `StronglyAdapted.stoppedProcess_of_discrete`. -/
theorem Adapted.stoppedProcess_of_discrete {ι γ : Type*} [Nonempty ι] [LinearOrder ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [MeasurableSpace ι]
    [BorelSpace ι] [DiscreteTopology ι] [TopologicalSpace γ] [PseudoMetrizableSpace γ]
    [SecondCountableTopology γ] [MeasurableSpace γ] [BorelSpace γ] {f : Filtration ι mΩ}
    {u : ι → Ω → γ} (hu : Adapted f u) {τ : Ω → WithTop ι} (hτ : IsStoppingTime f τ) :
    Adapted f (stoppedProcess u τ) :=
  (hu.stronglyAdapted.stoppedProcess_of_discrete hτ).adapted

/-! ### Stopping times in `WithTop ℕ` at the cast of a natural number

Mathlib's stopping-time API is stated at the coercion `WithTop.some n`, while statements about
`WithTop ℕ`-valued times use the cast `(n : WithTop ℕ)`; the following lemmas convert between them
by `Nat.cast_withTop`. -/

section NatCast

variable {ℱ : Filtration ℕ mΩ} {τ : Ω → WithTop ℕ}

/-- For a stopping time with values in `WithTop ℕ`, `{ω | τ ω ≤ n}` is `ℱ n`-measurable, at the
cast `(n : WithTop ℕ)`. -/
theorem IsStoppingTime.measurableSet_le_natCast (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    MeasurableSet[ℱ n] {ω | τ ω ≤ n} := by
  rw [Nat.cast_withTop]
  exact hτ n

/-- For a stopping time with values in `WithTop ℕ`, `{ω | n < τ ω}` is `ℱ n`-measurable, at the
cast `(n : WithTop ℕ)`. -/
theorem IsStoppingTime.measurableSet_natCast_lt (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    MeasurableSet[ℱ n] {ω | (n : WithTop ℕ) < τ ω} := by
  rw [Nat.cast_withTop]
  exact hτ.measurableSet_gt n

/-- The constant time `(n : WithTop ℕ)` is a stopping time. -/
theorem isStoppingTime_natCast (n : ℕ) : IsStoppingTime ℱ fun _ ↦ (n : WithTop ℕ) := by
  rw [Nat.cast_withTop]
  exact isStoppingTime_const ℱ n

/-- The minimum of a stopping time with values in `WithTop ℕ` and the cast `(n : WithTop ℕ)` is a
stopping time. -/
theorem IsStoppingTime.min_natCast (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ min (τ ω) n := by
  rw [Nat.cast_withTop]
  exact hτ.min_const n

end NatCast

/-! ### Stopping times of filtrations indexed by `ℕ` -/

section Nat

variable {ℱ : Filtration ℕ mΩ} {τ : Ω → WithTop ℕ}

/-- A stopping time of the coordinate filtration `Filtration.piLE` is determined by the
coordinates up to it: if `τ ω = n` and `ω'` agrees with `ω` up to `n`, then `τ ω' = n`. -/
theorem IsStoppingTime.eq_of_forall_le {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    {τ : (∀ i, X i) → WithTop ℕ} (hτ : IsStoppingTime Filtration.piLE τ) {ω ω' : ∀ i, X i}
    {n : ℕ} (hn : τ ω = n) (h : ∀ i ≤ n, ω i = ω' i) : τ ω' = n := by
  have hm : MeasurableSet[Filtration.piLE n] {ω' | τ ω' = n} := by
    simpa using hτ.measurableSet_eq n
  have hd : DependsOn ({ω' | τ ω' = n}.indicator fun _ ↦ (1 : ℕ)) (Set.Iic n) :=
    (measurable_const.indicator hm).dependsOn_of_piLE
  have h1 := hd fun i hi ↦ h i hi
  by_contra hne
  simp [Set.indicator, hne, hn] at h1

/-- For filtrations with `𝒢 (n + 1) = ℱ n`, such as `Filtration.piLT` and `Filtration.piLE`, a
random time `τ` is a stopping time of `ℱ` exactly when `τ + 1` is a stopping time of `𝒢`. -/
theorem isStoppingTime_add_one_iff {𝒢 : Filtration ℕ mΩ} (h : ∀ n, 𝒢 (n + 1) = ℱ n) :
    IsStoppingTime 𝒢 (fun ω ↦ τ ω + 1) ↔ IsStoppingTime ℱ τ := by
  have hset (n : ℕ) : {ω | τ ω + 1 ≤ ((n + 1 : ℕ) : WithTop ℕ)} = {ω | τ ω ≤ n} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Nat.cast_add, Nat.cast_one]
    exact WithTop.add_le_add_iff_right WithTop.one_ne_top
  refine ⟨fun hτ n ↦ ?_, fun hτ n ↦ ?_⟩
  · rw [← Nat.cast_withTop, ← h, ← hset]
    exact hτ.measurableSet_le_natCast (n + 1)
  · rcases n with _ | n
    · convert @MeasurableSet.empty _ (𝒢 0) using 1
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (by simp) le_add_self
    · rw [← Nat.cast_withTop, h, hset]
      exact hτ.measurableSet_le_natCast n

/-- The shift `fun n ↦ M (n + 1)` of a process adapted to `𝒢` is adapted to any filtration `ℱ`
with `𝒢 (n + 1) = ℱ n`. -/
theorem Adapted.shift {β : Type*} [MeasurableSpace β] {𝒢 : Filtration ℕ mΩ} {M : ℕ → Ω → β}
    (hM : Adapted 𝒢 M) (h : ∀ n, 𝒢 (n + 1) = ℱ n) : Adapted ℱ fun n ↦ M (n + 1) :=
  fun n ↦ h n ▸ hM (n + 1)

/-- For filtrations with `𝒢 (n + 1) = ℱ n`, such as `Filtration.piLT` and `Filtration.piLE`, a
process `M` whose value `M 0` is `𝒢 0`-measurable is adapted to `𝒢` exactly when its shift
`fun n ↦ M (n + 1)` is adapted to `ℱ`. -/
theorem adapted_shift_iff {β : Type*} [MeasurableSpace β] {𝒢 : Filtration ℕ mΩ}
    {M : ℕ → Ω → β} (h : ∀ n, 𝒢 (n + 1) = ℱ n) (hM₀ : Measurable[𝒢 0] (M 0)) :
    Adapted ℱ (fun n ↦ M (n + 1)) ↔ Adapted 𝒢 M := by
  refine ⟨fun hM ↦ ?_, fun hM ↦ hM.shift h⟩
  rintro (_ | n)
  · exact hM₀
  · exact (h n).symm ▸ hM n

end Nat

/-! ### Piecewise stopping times -/

section Piecewise

variable {ι : Type*} [Preorder ι] {𝒢 : Filtration ι mΩ} {τ η ρ : Ω → WithTop ι} {s : Set Ω}
  [DecidablePred (· ∈ s)]

/-- For stopping times `τ` and `η` that are at least a stopping time `ρ`, and a set `s` of the
σ-algebra at `ρ`, the time equal to `τ` on `s` and to `η` off `s` is a stopping time. Mathlib's
`IsStoppingTime.piecewise_of_le` is the case of a constant `ρ`. -/
theorem IsStoppingTime.piecewise_of_stoppingTime_le (hτ_st : IsStoppingTime 𝒢 τ)
    (hη_st : IsStoppingTime 𝒢 η) (hρ_st : IsStoppingTime 𝒢 ρ) (hτ : ∀ ω, ρ ω ≤ τ ω)
    (hη : ∀ ω, ρ ω ≤ η ω) (hs : MeasurableSet[hρ_st.measurableSpace] s) :
    IsStoppingTime 𝒢 (s.piecewise τ η) := by
  intro n
  have h_eq : {ω | s.piecewise τ η ω ≤ n} =
      (s ∩ {ω | ρ ω ≤ n}) ∩ {ω | τ ω ≤ n} ∪ (sᶜ ∩ {ω | ρ ω ≤ n}) ∩ {ω | η ω ≤ n} := by
    ext ω
    by_cases hω : ω ∈ s
    · simpa [hω] using fun h ↦ (hτ ω).trans h
    · simpa [hω] using fun h ↦ (hη ω).trans h
  rw [h_eq]
  exact ((hs.2 n).inter (hτ_st n)).union ((hs.compl.2 n).inter (hη_st n))

end Piecewise

end MeasureTheory
