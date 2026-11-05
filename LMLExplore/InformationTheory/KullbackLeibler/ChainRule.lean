/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.DataProcessing
public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.Restrict
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd

/-!
# Composition-products inside the Kullback–Leibler divergence

The measures `μ ⊗ₘ (κ ⊗ₖ η)` on `α × β × γ` and `μ ⊗ₘ κ ⊗ₘ η` on `(α × β) × γ` are images of
each other under `MeasurableEquiv.prodAssoc` (`MeasureTheory.Measure.compProd_assoc`), and the
Kullback–Leibler divergence is invariant under measurable equivalences.

If the second kernel `Kernel.piecewise hs η κ` agrees with the first kernel `κ` outside a
measurable set `s`, the divergence between `μ ⊗ₘ κ` and `μ ⊗ₘ Kernel.piecewise hs η κ` only
collects the points of `s`: it is the divergence between the composition-products with the
restriction `μ.restrict s`. This is how a change of measure that only acts on an event, such as
the rounds before a stopping time, is computed.

## Main statements

* `InformationTheory.klDiv_compProd_assoc`:
  `klDiv (μ ⊗ₘ (κ ⊗ₖ η)) (ν ⊗ₘ (κ' ⊗ₖ η')) = klDiv (μ ⊗ₘ κ ⊗ₘ η) (ν ⊗ₘ κ' ⊗ₘ η')`.
* `InformationTheory.klDiv_compProd_piecewise`:
  `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ Kernel.piecewise hs η κ) = klDiv (μ.restrict s ⊗ₘ κ) (μ.restrict s ⊗ₘ η)`.
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

/-- The divergence between `μ ⊗ₘ κ` and `μ ⊗ₘ Kernel.piecewise hs η κ`, whose second kernel is
`η` on `s` and `κ` elsewhere, is the divergence between the composition-products of the
restriction of `μ` to `s` with `κ` and with `η`. -/
lemma klDiv_compProd_piecewise (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] {s : Set α} (hs : MeasurableSet s)
    [DecidablePred (· ∈ s)] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ Kernel.piecewise hs η κ) =
      klDiv (μ.restrict s ⊗ₘ κ) (μ.restrict s ⊗ₘ η) := by
  -- The piecewise kernel agrees with `η` almost everywhere on `s` and with `κ` on `sᶜ`.
  have h_on : μ.restrict s ⊗ₘ Kernel.piecewise hs η κ = μ.restrict s ⊗ₘ η :=
    Measure.compProd_congr ((ae_restrict_mem hs).mono fun x hx ↦ by
      simp [Kernel.piecewise_apply, hx])
  have h_off : μ.restrict sᶜ ⊗ₘ Kernel.piecewise hs η κ = μ.restrict sᶜ ⊗ₘ κ :=
    Measure.compProd_congr ((ae_restrict_mem hs.compl).mono fun x hx ↦ by
      simp [Kernel.piecewise_apply, Set.notMem_of_mem_compl hx])
  have h_compl : (s ×ˢ (Set.univ : Set β))ᶜ = sᶜ ×ˢ Set.univ := by ext; simp
  -- Split the divergence over `s` and `sᶜ`; the part over `sᶜ` vanishes.
  rw [← klDiv_restrict_add_restrict_compl (hs.prod .univ), h_compl,
    ← Measure.compProd_restrict_left _ _ hs, ← Measure.compProd_restrict_left _ _ hs,
    ← Measure.compProd_restrict_left _ _ hs.compl, ← Measure.compProd_restrict_left _ _ hs.compl,
    h_on, h_off, klDiv_self, add_zero]

end InformationTheory
