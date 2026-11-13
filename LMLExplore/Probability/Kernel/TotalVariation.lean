/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Statlib.Divergence.TotalVariation
import Statlib.ForMathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Total variation distance under Markov kernels

Composition with a Markov kernel does not increase the total variation distance between two
measures: this is Statlib's data processing inequality `ProbabilityTheory.tvDist_comp_le`,
`tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν`. It gives the same bound for composition-products
`μ ⊗ₘ κ` and `ν ⊗ₘ κ` with a common Markov kernel. Replacing the kernel of a composition-product
`μ ⊗ₘ κ` by a kernel `η` with `tvDist (κ x) (η x) ≤ ε` for almost every `x` moves the measure by
at most `μ univ * ε`.

These are the two ways a perturbation propagates along a Markov chain: through the law of the
current state, and through the transition kernel. Together they bound the distance between the
laws of Markov chains with close kernels, such as the occupancy measures of two close policies of
a Markov decision process.

## Main statements

* `MeasureTheory.tvDist_compProd_left_le`: `tvDist (μ ⊗ₘ κ) (ν ⊗ₘ κ) ≤ tvDist μ ν` for a Markov
  kernel `κ` and s-finite measures `μ` and `ν`;
* `MeasureTheory.tvDist_compProd_right_le`: `tvDist (μ ⊗ₘ κ) (μ ⊗ₘ η) ≤ μ.real univ * ε` for
  Markov kernels `κ` and `η` with `tvDist (κ x) (η x) ≤ ε` for `μ`-almost every `x`.

## Implementation notes

The composition-product `μ ⊗ₘ κ` is the composition of `μ` with the kernel `Kernel.id ×ₖ κ`
(`MeasureTheory.Measure.compProd_eq_comp_prod`), so the first bound is the data processing
inequality. The bound for a change of kernel is proved eventwise, through
`MeasureTheory.tvDist_le_two_mul_of_forall_measureReal_le_add`: the mass of an event under
`μ ⊗ₘ κ` is the integral of a function with values in `[0, 1]`
(Statlib's `ProbabilityTheory.Measure.compProd_apply_toReal`).
-/

public section

open Set ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

/-- Composition-products with a common Markov kernel `κ` do not increase the total variation
distance between s-finite measures `μ` and `ν`. -/
theorem tvDist_compProd_left_le [SFinite μ] [SFinite ν] (κ : Kernel α β) [IsMarkovKernel κ] :
    tvDist (μ ⊗ₘ κ) (ν ⊗ₘ κ) ≤ tvDist μ ν := by
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod]
  exact tvDist_comp_le _ _ _

/-- Replacing the kernel `κ` of the composition-product `μ ⊗ₘ κ` by a Markov kernel `η` with
`tvDist (κ x) (η x) ≤ ε` for `μ`-almost every `x` moves it by at most `μ.real univ * ε` in total
variation. -/
theorem tvDist_compProd_right_le [IsFiniteMeasure μ] {κ η : Kernel α β} [IsMarkovKernel κ]
    [IsMarkovKernel η] {ε : ℝ} (hε : ∀ᵐ x ∂μ, tvDist (κ x) (η x) ≤ ε) :
    tvDist (μ ⊗ₘ κ) (μ ⊗ₘ η) ≤ μ.real univ * ε := by
  rw [← mul_div_cancel₀ (μ.real univ * ε) (two_ne_zero' ℝ)]
  refine tvDist_le_two_mul_of_forall_measureReal_le_add
    (by rw [Measure.compProd_apply_univ, Measure.compProd_apply_univ]) fun s hs ↦ ?_
  rw [measureReal_def, Measure.compProd_apply_toReal hs, measureReal_def,
    Measure.compProd_apply_toReal hs]
  simp only [← measureReal_def]
  have hκ : Measurable fun x ↦ (κ x).real (Prod.mk x ⁻¹' s) :=
    (Kernel.measurable_kernel_prodMk_left hs).ennreal_toReal
  have hη : Measurable fun x ↦ (η x).real (Prod.mk x ⁻¹' s) :=
    (Kernel.measurable_kernel_prodMk_left hs).ennreal_toReal
  have hint {f : α → ℝ} (hf : Measurable f) (hf1 : ∀ x, f x ∈ Icc 0 1) : Integrable f μ :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (hf1 x).1]; exact (hf1 x).2)
  have hκ1 (x : α) : (κ x).real (Prod.mk x ⁻¹' s) ∈ Icc 0 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hη1 (x : α) : (η x).real (Prod.mk x ⁻¹' s) ∈ Icc 0 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  -- the integrands differ by at most `ε / 2` almost everywhere
  have hle : ∫ x, (κ x).real (Prod.mk x ⁻¹' s) ∂μ ≤
      ∫ x, ((η x).real (Prod.mk x ⁻¹' s) + ε / 2) ∂μ := by
    refine integral_mono_ae (hint hκ hκ1) ((hint hη hη1).add (integrable_const _)) ?_
    filter_upwards [hε] with x hx
    have h := (abs_le.1 (abs_measureReal_sub_measureReal_le_tvDist_div_two (μ := κ x) (ν := η x)
      (by simp) (measurable_prodMk_left (x := x) hs))).2
    linarith
  rw [integral_add (hint hη hη1) (integrable_const _), integral_const, smul_eq_mul] at hle
  linarith

end MeasureTheory
