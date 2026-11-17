/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import TauCeti.InformationTheory.KullbackLeibler.Pinsker

/-!
# Pinsker's inequality for the real total variation distance

Tau Ceti proves Pinsker's inequality `etvDist μ ν ^ 2 ≤ 2 * klDiv μ ν` for probability measures,
in `ℝ≥0∞` (`TauCeti.etvDist_sq_le_two_mul_klDiv`). This file states it for the real total
variation distance `tvDist`, at finite relative entropy, in the two forms in which lower bounds use
it: `tvDist μ ν ^ 2 ≤ 2 * KL` and `tvDist μ ν / 2 ≤ √(KL / 2)`, where `KL = (klDiv μ ν).toReal`.

## Main statements

* `LMLExplore.tvDist_sq_le_two_mul_toReal_klDiv`: `tvDist μ ν ^ 2 ≤ 2 * (klDiv μ ν).toReal`.
* `LMLExplore.tvDist_div_two_le_sqrt_toReal_klDiv_div_two`:
  `tvDist μ ν / 2 ≤ √((klDiv μ ν).toReal / 2)`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Section 14.2.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace LMLExplore

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Pinsker's inequality** for the real total variation distance: for probability measures at
finite relative entropy, `tvDist μ ν ^ 2 ≤ 2 * (klDiv μ ν).toReal`. -/
theorem tvDist_sq_le_two_mul_toReal_klDiv (h : klDiv μ ν ≠ ∞) :
    tvDist μ ν ^ 2 ≤ 2 * (klDiv μ ν).toReal := by
  have h2 := TauCeti.etvDist_sq_le_two_mul_klDiv (μ := μ) (ν := ν)
  rw [← ENNReal.ofReal_toReal h, ← ofReal_tvDist, ← ENNReal.ofReal_pow tvDist_nonneg,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- **Pinsker's inequality** for the real total variation distance, in the form
`tvDist μ ν / 2 ≤ √((klDiv μ ν).toReal / 2)`, for probability measures at finite relative
entropy. -/
theorem tvDist_div_two_le_sqrt_toReal_klDiv_div_two (h : klDiv μ ν ≠ ∞) :
    tvDist μ ν / 2 ≤ √((klDiv μ ν).toReal / 2) := by
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [tvDist_sq_le_two_mul_toReal_klDiv h]

end LMLExplore
