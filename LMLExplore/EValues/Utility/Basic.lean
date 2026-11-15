/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Statlib.EValues.Utility.Basic

/-!
# Expected utility of a constant multiple of an indicator

Under a probability measure `μ` carried by a set `A`, the e-variable `c` times the indicator of
`A` is almost surely `c`, so its expected utility is `U c`, for every utility function `U`
(Statlib's `ProbabilityTheory.Utility`). With the logarithmic utility, this is the expected
logarithm `log c` of the e-variables that bound relative entropies and growth rates from below.

## Main statements

* `ProbabilityTheory.Utility.eintegral_comp_indicator_const`:
  `∫ᵉ x, (U ∘ A.indicator fun _ ↦ c) x ∂μ = U c` for `μ Aᶜ = 0`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Under a probability measure `μ` carried by a set `A`, the expected utility of `c` times the
indicator of `A` is `U c`. -/
lemma Utility.eintegral_comp_indicator_const (U : Utility) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : μ Aᶜ = 0) (c : ℝ≥0∞) :
    ∫ᵉ x, (U ∘ A.indicator fun _ ↦ c) x ∂μ = U c := by
  rw [eintegral_congr_ae (g := fun _ ↦ U c), eintegral_const, measure_univ,
    EReal.coe_ennreal_one, mul_one]
  filter_upwards [mem_ae_iff.2 hA] with x hx
  simp [hx]

end ProbabilityTheory
