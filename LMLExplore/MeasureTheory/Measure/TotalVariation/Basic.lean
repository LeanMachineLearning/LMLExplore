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
`|f| ≤ C`, then `|∫ f dμ - ∫ f dν| ≤ C * tvDist μ ν`. When `μ` and `ν` have the same mass, the
bound depends only on the oscillation of `f`: if `f` takes values in `[a, b]`, then
`|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`.

These are the bounds through which errors in transition kernels, measured in total variation,
propagate to expected values, as in the simulation lemma for Markov decision processes and in the
contraction of the oscillation of functions by a Markov kernel (Dobrushin's coefficient).

## Main statements

* `MeasureTheory.abs_integral_sub_integral_le_mul_tvDist`: `|∫ f dμ - ∫ f dν| ≤ C * tvDist μ ν`
  for `|f| ≤ C` almost everywhere.
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

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧} {f : 𝓧 → ℝ} {C : ℝ}

/-- **Integrals against measures close in total variation**: for finite measures `μ` and `ν` and
a function `f` bounded by `C` almost everywhere for both,
`|∫ f dμ - ∫ f dν| ≤ C * tvDist μ ν`. -/
theorem abs_integral_sub_integral_le_mul_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfμ : AEStronglyMeasurable f μ) (hfν : AEStronglyMeasurable f ν)
    (hfCμ : ∀ᵐ x ∂μ, |f x| ≤ C) (hfCν : ∀ᵐ x ∂ν, |f x| ≤ C) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ C * tvDist μ ν := by
  have hint (ρ : Measure 𝓧) [IsFiniteMeasure ρ] (hf : AEStronglyMeasurable f ρ)
      (hC : ∀ᵐ x ∂ρ, |f x| ≤ C) : ρ.toSignedMeasure.Integrable f := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hf C (by simpa using hC)
  -- write `∫ f dμ - ∫ f dν` as the integral of `f` against the signed measure `μ - ν`
  rw [← VectorMeasure.integral_toSignedMeasure, ← VectorMeasure.integral_toSignedMeasure (μ := ν),
    ← VectorMeasure.integral_sub_vectorMeasure (hint μ hfμ hfCμ) (hint ν hfν hfCν)]
  -- the variation of `μ - ν` is dominated by `μ + ν`, so `|f| ≤ C` almost everywhere for it
  have hle : (μ.toSignedMeasure - ν.toSignedMeasure).variation ≤ μ + ν := by
    simpa using VectorMeasure.variation_sub_le (μ := μ.toSignedMeasure) (ν := ν.toSignedMeasure)
  have := isFiniteMeasure_of_le _ hle
  have hae : ∀ᵐ x ∂(μ.toSignedMeasure - ν.toSignedMeasure).variation, ‖f x‖ ≤ C :=
    ae_mono hle (ae_add_measure_iff.2 ⟨by simpa using hfCμ, by simpa using hfCν⟩)
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hae
  rwa [ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.opNorm_lsmul, mul_one,
    Real.norm_eq_abs, measureReal_def, ← VectorMeasure.etvDist,
    ← etvDist_eq_etvDist_toSignedMeasure, ← tvDist] at h

/-- **Integrals against measures of the same mass close in total variation**: for finite measures
`μ` and `ν` of the same mass and a function `f` with values in `[a, b]` almost everywhere for
both, `|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`. -/
theorem abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) {a b : ℝ} (hfμ : AEStronglyMeasurable f μ)
    (hfν : AEStronglyMeasurable f ν) (hfμ' : ∀ᵐ x ∂μ, f x ∈ Icc a b)
    (hfν' : ∀ᵐ x ∂ν, f x ∈ Icc a b) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (b - a) / 2 * tvDist μ ν := by
  -- center `f` at the midpoint of `[a, b]`
  have hc {x : 𝓧} (hx : f x ∈ Icc a b) : |f x - (a + b) / 2| ≤ (b - a) / 2 :=
    abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hB {x : 𝓧} (hx : f x ∈ Icc a b) : ‖f x‖ ≤ max |a| |b| := by
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx.1 hx.2
  have h := abs_integral_sub_integral_le_mul_tvDist (f := fun x ↦ f x - (a + b) / 2)
    (hfμ.sub aestronglyMeasurable_const) (hfν.sub aestronglyMeasurable_const)
    (hfμ'.mono fun _ ↦ hc) (hfν'.mono fun _ ↦ hc)
  rwa [integral_sub (Integrable.of_bound hfμ _ (hfμ'.mono fun _ ↦ hB)) (integrable_const _),
    integral_sub (Integrable.of_bound hfν _ (hfν'.mono fun _ ↦ hB)) (integrable_const _),
    integral_const, integral_const, measureReal_def, measureReal_def, hμν, sub_sub_sub_cancel_right]
    at h

end MeasureTheory
