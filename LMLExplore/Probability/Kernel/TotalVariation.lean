/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Total variation distance under Markov kernels

Composition with a Markov kernel does not increase the total variation distance between two
finite measures (the data processing inequality for the total variation distance), and
replacing the kernel of a composition-product `μ ⊗ₘ κ` by a kernel `η` with
`tvDist (κ x) (η x) ≤ ε` for almost every `x` moves the measure by at most `μ univ * ε`.

These are the two ways a perturbation propagates along a Markov chain: through the law of the
current state, and through the transition kernel. Together they bound the distance between the
laws of Markov chains with close kernels, such as the occupancy measures of two close policies of
a Markov decision process.

## Main statements

* `MeasureTheory.Measure.measureReal_bind_eq_integral`,
  `MeasureTheory.Measure.measureReal_compProd_eq_integral`: the mass of an event under `κ ∘ₘ μ`
  or `μ ⊗ₘ κ`, as an integral against `μ`;
* `MeasureTheory.tvDist_comp_right_le`: `tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν` for a Markov
  kernel `κ` and finite measures `μ` and `ν`;
* `MeasureTheory.tvDist_compProd_left_le`: `tvDist (μ ⊗ₘ κ) (ν ⊗ₘ κ) ≤ tvDist μ ν`, under the
  same hypotheses;
* `MeasureTheory.tvDist_compProd_right_le`: `tvDist (μ ⊗ₘ κ) (μ ⊗ₘ η) ≤ μ.real univ * ε` for
  Markov kernels `κ` and `η` with `tvDist (κ x) (η x) ≤ ε` for `μ`-almost every `x`.

## Implementation notes

The mass of an event under a composition is the integral of a function with values in
`[0, 1]`. The data processing inequality evaluates the distance on a Hahn decomposition `s` of
the two compositions, where it is the gap between the integrals of `x ↦ κ x sᶜ - κ x s`, bounded
by `MeasureTheory.norm_integral_sub_integral_le_mul_tvDist`. The bound for a change of kernel is
proved eventwise, through `MeasureTheory.tvDist_le_two_mul_of_forall_measureReal_le_add`.
-/

public section

open Set ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

/-- The mass of an event `s` under the composition of a measure `μ` with a finite kernel `κ`,
as the integral of `x ↦ κ x s`. -/
theorem Measure.measureReal_bind_eq_integral (κ : Kernel α β) [IsFiniteKernel κ] {s : Set β}
    (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s = ∫ x, (κ x).real s ∂μ := by
  simp only [measureReal_def]
  rw [Measure.bind_apply hs κ.aemeasurable,
    integral_toReal (κ.measurable_coe hs).aemeasurable (ae_of_all _ fun _ ↦ measure_lt_top _ _)]

/-- The mass of an event `s` under the composition-product of a measure `μ` with a finite kernel
`κ`, as the integral of `x ↦ κ x (Prod.mk x ⁻¹' s)`. -/
theorem Measure.measureReal_compProd_eq_integral [SFinite μ] (κ : Kernel α β) [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ).real s = ∫ x, (κ x).real (Prod.mk x ⁻¹' s) ∂μ := by
  simp only [measureReal_def]
  rw [Measure.compProd_apply hs,
    integral_toReal (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
      (ae_of_all _ fun _ ↦ measure_lt_top _ _)]

/-- **Data processing inequality** for the total variation distance: composing two finite
measures `μ` and `ν` with a Markov kernel `κ` does not increase their total variation
distance. -/
theorem tvDist_comp_right_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel α β)
    [IsMarkovKernel κ] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν := by
  -- on a Hahn set `s` of the two compositions, the distance is the gap between the integrals of
  -- `f x = κ x sᶜ - κ x s`, which has absolute value at most `1`
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition (κ ∘ₘ μ) (κ ∘ₘ ν)
  have hm := hs.measurableSet
  have hf : Measurable fun x ↦ (κ x).real sᶜ - (κ x).real s :=
    (κ.measurable_coe hm.compl).ennreal_toReal.sub (κ.measurable_coe hm).ennreal_toReal
  have hf1 (x : α) : ‖(κ x).real sᶜ - (κ x).real s‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [measureReal_nonneg (μ := κ x) (s := s),
      measureReal_nonneg (μ := κ x) (s := sᶜ), measureReal_le_one (μ := κ x) (s := s),
      measureReal_le_one (μ := κ x) (s := sᶜ)]
  have hint (ρ : Measure α) [IsFiniteMeasure ρ] {t : Set β} (ht : MeasurableSet t) :
      Integrable (fun x ↦ (κ x).real t) ρ :=
    Integrable.of_bound (κ.measurable_coe ht).ennreal_toReal.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by
        rw [Real.norm_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
  have h := norm_integral_sub_integral_le_mul_tvDist hf.aestronglyMeasurable
    hf.aestronglyMeasurable (ae_of_all μ hf1) (ae_of_all ν hf1)
  rw [integral_sub (hint μ hm.compl) (hint μ hm), integral_sub (hint ν hm.compl) (hint ν hm),
    one_mul, Real.norm_eq_abs] at h
  rw [hs.tvDist_eq, Measure.measureReal_bind_eq_integral κ hm,
    Measure.measureReal_bind_eq_integral κ hm, Measure.measureReal_bind_eq_integral κ hm.compl,
    Measure.measureReal_bind_eq_integral κ hm.compl]
  linarith [(abs_le.1 h).2]

/-- Composition-products with a common Markov kernel `κ` do not increase the total variation
distance between finite measures `μ` and `ν`. -/
theorem tvDist_compProd_left_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ : Kernel α β)
    [IsMarkovKernel κ] :
    tvDist (μ ⊗ₘ κ) (ν ⊗ₘ κ) ≤ tvDist μ ν := by
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod]
  exact tvDist_comp_right_le _

/-- Replacing the kernel `κ` of the composition-product `μ ⊗ₘ κ` by a Markov kernel `η` with
`tvDist (κ x) (η x) ≤ ε` for `μ`-almost every `x` moves it by at most `μ.real univ * ε` in total
variation. -/
theorem tvDist_compProd_right_le [IsFiniteMeasure μ] {κ η : Kernel α β} [IsMarkovKernel κ]
    [IsMarkovKernel η] {ε : ℝ} (hε : ∀ᵐ x ∂μ, tvDist (κ x) (η x) ≤ ε) :
    tvDist (μ ⊗ₘ κ) (μ ⊗ₘ η) ≤ μ.real univ * ε := by
  rw [← mul_div_cancel₀ (μ.real univ * ε) (two_ne_zero' ℝ)]
  refine tvDist_le_two_mul_of_forall_measureReal_le_add
    (by rw [Measure.compProd_apply_univ, Measure.compProd_apply_univ]) fun s hs ↦ ?_
  rw [Measure.measureReal_compProd_eq_integral κ hs,
    Measure.measureReal_compProd_eq_integral η hs]
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
