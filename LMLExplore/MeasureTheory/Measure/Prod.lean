/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Preimages by the first projection under a product measure

## Main statements

* `MeasureTheory.Measure.prod_preimage_fst`: `μ.prod ν (Prod.fst ⁻¹' s) = ν univ * μ s`, for any
  set `s`, measurable or not.
-/

public section

open Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Under a product measure, the preimage of a set by the first projection has measure
`ν univ * μ s`. The set `s` need not be measurable. -/
@[simp]
lemma prod_preimage_fst (μ : Measure α) (ν : Measure β) [SFinite ν] (s : Set α) :
    μ.prod ν (Prod.fst ⁻¹' s) = ν univ * μ s := by
  rw [← prod_univ, prod_prod, mul_comm]

end MeasureTheory.Measure
