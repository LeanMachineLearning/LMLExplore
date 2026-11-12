/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of the inverse in a complete normed ring

In a complete normed ring `R`, the units form an open set on which `Ring.inverse` is continuous,
and `Ring.inverse` vanishes off it, so `Ring.inverse` is Borel measurable. For the algebra
`E →L[ℝ] E` of operators on a finite-dimensional space, this makes measurable the random
operators `V⁻¹` built from random design operators `V`, such as the inverse design operators of
the loss estimates of adversarial linear bandits.

## Main statements

* `LMLExplore.measurable_ringInverse`: `Ring.inverse : R → R` is measurable.
* `Measurable.ringInverse`, `AEMeasurable.ringInverse`: composition forms.
-/

public section

open MeasureTheory

variable {R : Type*} [NormedRing R] [CompleteSpace R] [MeasurableSpace R] [BorelSpace R]

namespace LMLExplore

/-- In a complete normed ring, `Ring.inverse` is measurable: it is continuous on the open set of
units and vanishes off it. -/
@[fun_prop]
theorem measurable_ringInverse : Measurable (Ring.inverse : R → R) := by
  classical
  have h : (Ring.inverse : R → R) = {x : R | IsUnit x}.piecewise Ring.inverse 0 := by
    ext x
    by_cases hx : IsUnit x
    · simp [hx]
    · simp [hx, Ring.inverse_non_unit]
  rw [h]
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const Units.isOpen.measurableSet
  rintro x ⟨u, rfl⟩
  exact (NormedRing.inverse_continuousAt u).continuousWithinAt

end LMLExplore

variable {α : Type*} {mα : MeasurableSpace α} {f : α → R}

/-- The inverse of a measurable function to a complete normed ring is measurable. -/
@[fun_prop]
theorem Measurable.ringInverse (hf : Measurable f) : Measurable fun a ↦ Ring.inverse (f a) :=
  LMLExplore.measurable_ringInverse.comp hf

/-- The inverse of an almost everywhere measurable function to a complete normed ring is almost
everywhere measurable. -/
@[fun_prop]
theorem AEMeasurable.ringInverse {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a ↦ Ring.inverse (f a)) μ :=
  LMLExplore.measurable_ringInverse.comp_aemeasurable hf
