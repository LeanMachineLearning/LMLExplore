/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Probability.Process.Filtration.Progressive

/-!
# The progressive σ-algebra in countable time

For a filtration `ℱ` indexed by a countable preorder `ι` with measurable singletons, such as `ℕ`,
the progressive σ-algebra `Filtration.progressive ℱ` on `ι × Ω` of Tau Ceti is the σ-algebra of
the sets whose section `{ω | (i, ω) ∈ s}` at each time `i` is `ℱ i`-measurable, and its measurable
functions are the adapted processes: in countable time, progressive measurability is
adaptedness. In discrete time this σ-algebra is also the optional σ-algebra, and `ι × Ω` with it
is the space of stopped paths: for a measurable random time `τ`, the map `ω ↦ (τ ω, ω)` is
measurable into it, so that an adapted process read at `τ` is a measurable function of the
stopped path.

## Main statements

* `MeasureTheory.Adapted.isProgressive_of_countable`, `MeasureTheory.isProgressive_iff_adapted`:
  in countable time, a process is progressive exactly when it is adapted.
* `MeasureTheory.Filtration.measurable_uncurry_progressive_iff`: a process is a measurable
  function on `ι × Ω` for the progressive σ-algebra exactly when it is adapted.
* `MeasureTheory.Filtration.measurableSet_progressive_iff_of_countable`: a set is progressive
  exactly when its section at each time `i` is `ℱ i`-measurable.
* `MeasureTheory.Filtration.progressive_le_prod_of_countable`: the progressive σ-algebra is
  smaller than the product σ-algebra.
* `MeasureTheory.Filtration.measurable_prodMk_progressive`: for a measurable random time `τ`, the
  map `ω ↦ (τ ω, ω)` is measurable for the progressive σ-algebra.
-/

public section

open Set

namespace MeasureTheory

variable {ι Ω β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace β] [Preorder ι] [Countable ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] {ℱ : Filtration ι mΩ} {u : ι → Ω → β}

/-- In countable time with measurable singletons, an adapted process is progressive. -/
theorem Adapted.isProgressive_of_countable (hu : Adapted ℱ u) : IsProgressive ℱ u := fun _ ↦
  measurable_from_prod_countable_right fun j ↦ hu.measurable_le (mem_Iic.1 j.2)

/-- In countable time with measurable singletons, a process is progressive exactly when it is
adapted. -/
theorem isProgressive_iff_adapted : IsProgressive ℱ u ↔ Adapted ℱ u :=
  ⟨IsProgressive.adapted, Adapted.isProgressive_of_countable⟩

namespace Filtration

/-- In countable time, a function on `ι × Ω` is measurable for the progressive σ-algebra exactly
when its sections form an adapted process. -/
theorem measurable_progressive_iff_adapted {f : ι × Ω → β} :
    Measurable[ℱ.progressive] f ↔ Adapted ℱ (Function.curry f) := by
  rw [measurable_progressive_iff, isProgressive_iff_adapted]

/-- In countable time, a process is a measurable function on `ι × Ω` for the progressive
σ-algebra exactly when it is adapted. -/
theorem measurable_uncurry_progressive_iff :
    Measurable[ℱ.progressive] (Function.uncurry u) ↔ Adapted ℱ u := by
  rw [measurable_progressive_iff_adapted, Function.curry_uncurry]

/-- In countable time, a set is measurable for the progressive σ-algebra exactly when its section
at each time `i` is `ℱ i`-measurable. -/
theorem measurableSet_progressive_iff_of_countable {s : Set (ι × Ω)} :
    MeasurableSet[ℱ.progressive] s ↔ ∀ i, MeasurableSet[ℱ i] {ω | (i, ω) ∈ s} := by
  rw [← @measurable_mem _ s ℱ.progressive, measurable_progressive_iff_adapted]
  exact forall_congr' fun i ↦ @measurable_mem Ω {ω | (i, ω) ∈ s} (ℱ i)

/-- In countable time, the progressive σ-algebra is smaller than the product σ-algebra. -/
theorem progressive_le_prod_of_countable :
    ℱ.progressive ≤ (inferInstance : MeasurableSpace ι).prod mΩ := by
  intro s hs
  have h_eq : s = ⋃ i, {i} ×ˢ {ω | (i, ω) ∈ s} := by
    ext ⟨i, ω⟩
    simp
  rw [h_eq]
  exact .iUnion fun i ↦ (measurableSet_singleton i).prod
    (ℱ.le i _ (measurableSet_progressive_iff_of_countable.1 hs i))

/-- For a measurable random time `τ`, the stopped path `ω ↦ (τ ω, ω)` is measurable for the
progressive σ-algebra. -/
theorem measurable_prodMk_progressive {τ : Ω → ι} (hτ : Measurable τ) :
    Measurable[mΩ, ℱ.progressive] fun ω ↦ (τ ω, ω) :=
  (hτ.prodMk measurable_id).mono le_rfl progressive_le_prod_of_countable

end Filtration

end MeasureTheory
