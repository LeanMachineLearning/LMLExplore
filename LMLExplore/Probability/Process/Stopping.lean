/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Probability.Process.Stopping
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
processes.

## Main statements

* `MeasureTheory.IsStoppingTime.measurable_enat`: a stopping time `τ : Ω → ℕ∞` of a filtration
  indexed by `ℕ` is measurable for the discrete σ-algebra of `ℕ∞`.
* `MeasureTheory.IsStoppingTime.measurableSet_le_natCast`,
  `MeasureTheory.IsStoppingTime.measurableSet_natCast_lt`, `MeasureTheory.isStoppingTime_natCast`,
  `MeasureTheory.IsStoppingTime.min_natCast`: Mathlib's stopping-time API for `WithTop ℕ`-valued
  times, stated at the cast `(n : WithTop ℕ)` rather than the coercion `WithTop.some n`.
* `MeasureTheory.IsStoppingTime.toNat_min`, `ENat.natCast_toNat_min`: the minimum of a stopping
  time with values in `WithTop ℕ` and a constant is a stopping time with values in `ℕ`.
* `MeasureTheory.IsStoppingTime.measurable_nat`, `MeasureTheory.IsStoppingTime.natCast_min`: a
  stopping time with values in `ℕ` is measurable, and so is its minimum with a constant a stopping
  time.
* `MeasureTheory.IsStoppingTime.eq_of_forall_le`: a stopping time of the coordinate filtration
  `Filtration.piLE` with values in `ℕ` is determined by the coordinates up to it.
* `MeasureTheory.Adapted.stoppedProcess_of_discrete`: a stopped adapted process is adapted.
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

/-- The minimum of `t : WithTop ℕ` and the cast `(n : WithTop ℕ)` is finite, so its value as a
natural number casts back to it. -/
theorem _root_.ENat.natCast_toNat_min (t : WithTop ℕ) (n : ℕ) :
    ((ENat.toNat (min t n) : ℕ) : WithTop ℕ) = min t n :=
  ENat.natCast_toNat (ne_top_of_le_ne_top (WithTop.natCast_ne_top n) (min_le_right _ _))

/-- The minimum of a stopping time with values in `WithTop ℕ` and the cast `(n : WithTop ℕ)`, as a
natural number, is a stopping time with values in `ℕ`; it casts back to `min (τ ω) n`
(`ENat.natCast_toNat_min`). -/
theorem IsStoppingTime.toNat_min (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ ((ENat.toNat (min (τ ω) n) : ℕ) : WithTop ℕ) := by
  simp_rw [ENat.natCast_toNat_min]
  exact hτ.min_natCast n

end NatCast

/-! ### Stopping times with values in `ℕ` -/

section Nat

variable {ℱ : Filtration ℕ mΩ} {τ : Ω → ℕ}

/-- A stopping time with values in `ℕ` is measurable. -/
theorem IsStoppingTime.measurable_nat (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℕ)) :
    Measurable τ := by
  convert (measurable_of_countable (WithTop.untopD 0)).comp hτ.measurable' using 1
  exact funext fun ω ↦ (WithTop.untopD_coe 0 (τ ω)).symm

/-- The minimum of a stopping time with values in `ℕ` and a constant is a stopping time. -/
theorem IsStoppingTime.natCast_min (hτ : IsStoppingTime ℱ fun ω ↦ (τ ω : WithTop ℕ)) (n : ℕ) :
    IsStoppingTime ℱ fun ω ↦ ((min (τ ω) n : ℕ) : WithTop ℕ) := by
  have h : (fun ω ↦ ((min (τ ω) n : ℕ) : WithTop ℕ)) = fun ω ↦ min (τ ω : WithTop ℕ) n :=
    funext fun ω ↦ WithTop.coe_min _ _
  rw [h]
  exact hτ.min_natCast n

/-- A stopping time with values in `ℕ` of the coordinate filtration `Filtration.piLE` is
determined by the coordinates up to it: if `ω'` agrees with `ω` up to `τ ω`, then
`τ ω' = τ ω`. -/
theorem IsStoppingTime.eq_of_forall_le {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    {τ : (∀ i, X i) → ℕ} (hτ : IsStoppingTime Filtration.piLE fun ω ↦ (τ ω : WithTop ℕ))
    {ω ω' : ∀ i, X i} (h : ∀ i ≤ τ ω, ω i = ω' i) : τ ω' = τ ω := by
  have hm : MeasurableSet[Filtration.piLE (τ ω)] {ω' | τ ω' = τ ω} := by
    simpa using hτ.measurableSet_eq (τ ω)
  have hd : DependsOn ({ω' | τ ω' = τ ω}.indicator fun _ ↦ (1 : ℕ)) (Set.Iic (τ ω)) :=
    (measurable_const.indicator hm).dependsOn_of_piLE
  have h1 := hd fun i hi ↦ h i hi
  by_contra hne
  simp [Set.indicator, hne] at h1

end Nat

end MeasureTheory
