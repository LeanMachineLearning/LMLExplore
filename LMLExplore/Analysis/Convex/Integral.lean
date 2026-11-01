/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Integral

/-!
# The mean of a measure concentrated on an interval

## Main statements

* `MeasureTheory.integral_id_mem_Icc_of_ae_mem_Icc`: the mean of a probability measure on `ℝ`
  concentrated on `[l, u]` lies in `[l, u]`, by `Convex.integral_mem`.
-/

public section

namespace MeasureTheory

/-- The mean of a probability measure on `ℝ` concentrated on `[l, u]` lies in `[l, u]`. -/
theorem integral_id_mem_Icc_of_ae_mem_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ] {l u : ℝ}
    (h : ∀ᵐ x ∂μ, x ∈ Set.Icc l u) : ∫ x, id x ∂μ ∈ Set.Icc l u :=
  (convex_Icc l u).integral_mem isClosed_Icc h (Integrable.of_mem_Icc l u aemeasurable_id h)

end MeasureTheory
