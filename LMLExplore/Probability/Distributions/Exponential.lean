/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import TauCeti.Probability.Distributions.Exponential.Basic

/-!
# Exponential laws: nonpositive rates and tilting

The exponential law `expMeasure r` of a nonpositive rate `r` is the zero measure, since its density
vanishes. Tilting `expMeasure r` of positive rate by `x ↦ η x` lowers its rate by `η`; for `η ≥ r`
the exponential moment is infinite and both sides are the zero measure.

## Main statements

* `LMLExplore.expMeasure_of_nonpos`: `expMeasure r = 0` for `r ≤ 0`.
* `LMLExplore.tilted_mul_expMeasure`: `expMeasure r` tilted by `x ↦ η x` is `expMeasure (r - η)`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace LMLExplore

variable {r : ℝ}

/-- The exponential law of a nonpositive rate is the zero measure: its density vanishes. -/
@[simp]
lemma expMeasure_of_nonpos (hr : r ≤ 0) : expMeasure r = 0 := by
  rw [TauCeti.Probability.expMeasure_eq_withDensity, ← withDensity_zero]
  congr 1
  funext x
  rw [exponentialPDF_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero]
  split_ifs
  · exact mul_nonpos_of_nonpos_of_nonneg hr (exp_pos _).le
  · exact le_rfl

/-- Tilting an exponential law by `x ↦ η x` lowers its rate by `η`: `expMeasure r` tilted by
`x ↦ η x` is `expMeasure (r - η)`. For `η ≥ r`, both sides are the zero measure. -/
@[simp]
theorem tilted_mul_expMeasure (hr : 0 < r) (η : ℝ) :
    (expMeasure r).tilted (fun x ↦ η * x) = expMeasure (r - η) := by
  rcases lt_or_ge η r with hη | hη
  swap
  · -- `x ↦ exp (η x)` is not integrable, and the rate `r - η` is nonpositive.
    rw [tilted_of_not_integrable (by simpa [hr] using hη), expMeasure_of_nonpos (by linarith)]
  rw [Measure.tilted, TauCeti.Probability.expMeasure_eq_withDensity,
    TauCeti.Probability.expMeasure_eq_withDensity,
    ← withDensity_mul _ (f := exponentialPDF r) (measurable_exponentialPDFReal r).ennreal_ofReal
      (by fun_prop)]
  congr 1
  funext x
  have h_mgf : ∫ y, exp (η * y) ∂(volume.withDensity (exponentialPDF r)) = r / (r - η) := by
    rw [← TauCeti.Probability.expMeasure_eq_withDensity]
    simpa only [mgf, id] using TauCeti.Probability.mgf_id_expMeasure hr hη
  have hrη : 0 < r - η := sub_pos.2 hη
  simp only [Pi.mul_apply, h_mgf, exponentialPDF_eq]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    -- `r exp (-(r x)) * (exp (η x) / (r / (r - η))) = (r - η) exp (-((r - η) x))`
    have h : exp (-((r - η) * x)) = exp (-(r * x)) * exp (η * x) := by
      rw [← exp_add]
      ring_nf
    rw [h]
    field_simp
  · simp

end LMLExplore
