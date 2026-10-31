/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Probability measures which are Dirac masses

## Main statements

* `MeasureTheory.Measure.id_ae_eq_const_iff`: a probability measure `ρ` is the Dirac mass at `c`
  if and only if the identity is almost surely equal to `c` under `ρ`.
-/

public section

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} [MeasurableSingletonClass α] {ρ : Measure α}
  [IsProbabilityMeasure ρ] {c : α}

/-- The identity is almost surely equal to `c` under a probability measure `ρ` if and only if `ρ`
is the Dirac mass at `c`. -/
lemma id_ae_eq_const_iff : (id : α → α) =ᵐ[ρ] (fun _ ↦ c) ↔ ρ = dirac c := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ae_eq_dirac id⟩
  rw [← map_id (μ := ρ), map_congr h, map_const, measure_univ, one_smul]

end MeasureTheory.Measure
