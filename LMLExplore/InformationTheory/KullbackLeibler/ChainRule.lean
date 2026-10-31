/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
# Reassociating composition-products inside the Kullback–Leibler divergence

The measures `μ ⊗ₘ (κ ⊗ₖ η)` on `α × β × γ` and `μ ⊗ₘ κ ⊗ₘ η` on `(α × β) × γ` are images of
each other under `MeasurableEquiv.prodAssoc` (`MeasureTheory.Measure.compProd_assoc`), and the
Kullback–Leibler divergence is invariant under measurable equivalences.

## Main statements

* `InformationTheory.klDiv_compProd_assoc`:
  `klDiv (μ ⊗ₘ (κ ⊗ₖ η)) (ν ⊗ₘ (κ' ⊗ₖ η')) = klDiv (μ ⊗ₘ κ ⊗ₘ η) (ν ⊗ₘ κ' ⊗ₘ η')`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ ν : Measure α} {κ κ' : Kernel α β} {η η' : Kernel (α × β) γ}

/-- The Kullback–Leibler divergence between two three-step composition-products does not depend
on how the products are associated. -/
lemma klDiv_compProd_assoc [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ]
    [IsFiniteKernel κ'] [IsFiniteKernel η] [IsFiniteKernel η'] :
    klDiv (μ ⊗ₘ (κ ⊗ₖ η)) (ν ⊗ₘ (κ' ⊗ₖ η')) = klDiv (μ ⊗ₘ κ ⊗ₘ η) (ν ⊗ₘ κ' ⊗ₘ η') := by
  rw [← klDiv_map_measurableEquiv _ _ MeasurableEquiv.prodAssoc.symm, Measure.compProd_assoc,
    Measure.compProd_assoc]

end InformationTheory
