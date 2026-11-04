/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Integrals against measures close in total variation

The total variation distance `tvDist μ ν` of two finite measures (with values in `[0, 2]` for
probability measures) controls the difference of the integrals of bounded functions: if
`‖f‖ ≤ C`, then `‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν`. When `μ` and `ν` have the same mass, the
bound depends only on the oscillation of `f`: if `f` takes values in `[a, b]`, then
`|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`.

These are the bounds through which errors in transition kernels, measured in total variation,
propagate to expected values, as in the simulation lemma for Markov decision processes and in the
contraction of the oscillation of functions by a Markov kernel (Dobrushin's coefficient).

## Main statements

* `MeasureTheory.tvDist_eq_measureReal_variation_sub_toSignedMeasure`: `tvDist μ ν` is the total
  mass of the variation of the signed measure `μ - ν`.
* `MeasureTheory.norm_integral_sub_integral_le_mul_tvDist`:
  `‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν` for `‖f‖ ≤ C` almost everywhere, `f` with values in a
  normed space.
* `MeasureTheory.abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc`: for measures of the same
  mass and `f` with values in `[a, b]` almost everywhere,
  `|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`.

## Implementation notes

The first bound is the bound `MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const` on
integrals against the signed measure `μ - ν`, whose variation has mass `tvDist μ ν`.
-/

public section

open Set

namespace MeasureTheory

variable {𝓧 E : Type*} {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ ν : Measure 𝓧} {C : ℝ}

/-- The total variation distance of two finite measures is the total mass of the variation of the
difference of the associated signed measures. -/
theorem tvDist_eq_measureReal_variation_sub_toSignedMeasure [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν = (μ.toSignedMeasure - ν.toSignedMeasure).variation.real univ := by
  rw [tvDist, etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist, measureReal_def]

/-- **Integrals against measures close in total variation**: for finite measures `μ` and `ν` and
a function `f` with values in a normed space, bounded in norm by `C` almost everywhere for both,
`‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν`. -/
theorem norm_integral_sub_integral_le_mul_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : 𝓧 → E} (hfμ : AEStronglyMeasurable f μ) (hfν : AEStronglyMeasurable f ν)
    (hfCμ : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) (hfCν : ∀ᵐ x ∂ν, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂μ - ∫ x, f x ∂ν‖ ≤ C * tvDist μ ν := by
  have hint (ρ : Measure 𝓧) [IsFiniteMeasure ρ] (hf : AEStronglyMeasurable f ρ)
      (hC : ∀ᵐ x ∂ρ, ‖f x‖ ≤ C) : ρ.toSignedMeasure.Integrable f := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hf C hC
  -- write `∫ f dμ - ∫ f dν` as the integral of `f` against the signed measure `μ - ν`
  rw [← VectorMeasure.integral_toSignedMeasure, ← VectorMeasure.integral_toSignedMeasure (μ := ν),
    ← VectorMeasure.integral_sub_vectorMeasure (hint μ hfμ hfCμ) (hint ν hfν hfCν),
    tvDist_eq_measureReal_variation_sub_toSignedMeasure]
  -- the variation of `μ - ν` is dominated by `μ + ν`, so `‖f‖ ≤ C` almost everywhere for it
  have hle : (μ.toSignedMeasure - ν.toSignedMeasure).variation ≤ μ + ν := by
    simpa using VectorMeasure.variation_sub_le (μ := μ.toSignedMeasure) (ν := ν.toSignedMeasure)
  have := isFiniteMeasure_of_le _ hle
  have hae : ∀ᵐ x ∂(μ.toSignedMeasure - ν.toSignedMeasure).variation, ‖f x‖ ≤ C :=
    ae_mono hle (ae_add_measure_iff.2 ⟨hfCμ, hfCν⟩)
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hae
  -- `C` is nonnegative unless the variation of `μ - ν` vanishes
  rcases eq_or_ne (μ.toSignedMeasure - ν.toSignedMeasure).variation 0 with h0 | h0
  · simpa [h0] using h
  have := ae_neBot.2 h0
  obtain ⟨x, hx⟩ := hae.exists
  refine h.trans (mul_le_mul_of_nonneg_right ?_ measureReal_nonneg)
  rw [ContinuousLinearMap.opNorm_flip]
  exact mul_le_of_le_one_right ((norm_nonneg _).trans hx) ContinuousLinearMap.opNorm_lsmul_le

/-- **Integrals against measures of the same mass close in total variation**: for finite measures
`μ` and `ν` of the same mass and a function `f` with values in `[a, b]` almost everywhere for
both, `|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`. -/
theorem abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) {f : 𝓧 → ℝ} {a b : ℝ}
    (hfμ : AEStronglyMeasurable f μ) (hfν : AEStronglyMeasurable f ν)
    (hfμ' : ∀ᵐ x ∂μ, f x ∈ Icc a b) (hfν' : ∀ᵐ x ∂ν, f x ∈ Icc a b) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (b - a) / 2 * tvDist μ ν := by
  -- center `f` at the midpoint of `[a, b]`
  have hc {x : 𝓧} (hx : f x ∈ Icc a b) : ‖f x - (a + b) / 2‖ ≤ (b - a) / 2 :=
    abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hB {x : 𝓧} (hx : f x ∈ Icc a b) : ‖f x‖ ≤ max |a| |b| :=
    abs_le_max_abs_abs hx.1 hx.2
  have h := norm_integral_sub_integral_le_mul_tvDist (f := fun x ↦ f x - (a + b) / 2)
    (hfμ.sub aestronglyMeasurable_const) (hfν.sub aestronglyMeasurable_const)
    (hfμ'.mono fun _ ↦ hc) (hfν'.mono fun _ ↦ hc)
  rw [integral_sub (Integrable.of_bound hfμ _ (hfμ'.mono fun _ ↦ hB)) (integrable_const _),
    integral_sub (Integrable.of_bound hfν _ (hfν'.mono fun _ ↦ hB)) (integrable_const _)] at h
  simpa [measureReal_def, hμν] using h

end MeasureTheory
