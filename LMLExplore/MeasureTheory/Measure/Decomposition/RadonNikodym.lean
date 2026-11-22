/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import LMLExplore.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Radon–Nikodym derivatives as ratios of densities

For measures `μ`, `ν` and `ξ` with `ν ≪ ξ`, the Radon–Nikodym derivative `μ.rnDeriv ν` is
`ν`-almost everywhere the ratio `μ.rnDeriv ξ / ν.rnDeriv ξ` of the densities of `μ` and `ν` with
respect to `ξ`. Mathlib's `MeasureTheory.Measure.rnDeriv_eq_div` also assumes `μ ≪ ξ`; this is
not needed, since the part of `μ` that is singular with respect to `ξ` is also singular with
respect to `ν`. This is the form in which likelihood ratios are computed from densities with
respect to a reference measure that need not dominate the alternative.

Dividing instead by an upper envelope `f` of the density of `ν` can only decrease the ratio: it is
`ν`-almost everywhere at most `μ.rnDeriv ν`. This is the domination behind universal inference,
where `f` is the maximal likelihood of a composite null, an envelope of the densities of all its
members.

## Main statements

* `MeasureTheory.Measure.rnDeriv_eq_div'`: for `ν ≪ ξ`, `μ.rnDeriv ν` is `ν`-a.e. equal to
  `μ.rnDeriv ξ / ν.rnDeriv ξ`.
* `MeasureTheory.Measure.rnDeriv_div_ae_le_rnDeriv`: for `ν ≪ ξ` and `ν.rnDeriv ξ ≤ f`
  `ξ`-a.e., `μ.rnDeriv ξ / f` is `ν`-a.e. at most `μ.rnDeriv ν`.
* `MeasureTheory.Measure.rnDeriv_le_of_le_withDensity`: for `μ ≤ ν.withDensity f`,
  `μ.rnDeriv ν` is `ν`-a.e. at most `f`.
* `MeasureTheory.Measure.rnDeriv_le_rnDeriv_of_le`: the density with respect to `ξ` is monotone
  in the measure, below a finite measure.
* `MeasureTheory.Measure.lintegral_rpow_rnDeriv_withDensity`: for an almost everywhere finite
  density `f` and `a < 1`, `∫⁻ (dμ/dν) ^ a dν = ∫⁻ f ^ (1 - a) dμ` with `ν = μ.withDensity f`,
  the affinity of order `a` between `μ` and a measure with a density with respect to it.

## Implementation notes

`rnDeriv_le_of_le_withDensity` is adapted from the lemma of the same name in
`EValuesResearch/Results/TTestGrowAux.lean` (commit `562b62e`) of the paper project
`RemyDegenne/evalues_research`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α} {μ ν ξ : Measure α}

/-- For a measure `ξ` dominating `ν`, the Radon–Nikodym derivative of `μ` with respect to `ν` is
`ν`-almost everywhere the ratio of the Radon–Nikodym derivatives of `μ` and `ν` with respect to
`ξ`. Unlike `MeasureTheory.Measure.rnDeriv_eq_div`, `μ` need not be absolutely continuous with
respect to `ξ`. -/
theorem rnDeriv_eq_div' [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ] (hν : ν ≪ ξ) :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv ξ x / ν.rnDeriv ξ x := by
  filter_upwards [rnDeriv_mul_rnDeriv' (μ := μ) hν, rnDeriv_pos hν,
    hν.ae_le (ν.rnDeriv_lt_top ξ)] with x hx hpos htop
  rw [← hx, Pi.mul_apply, ENNReal.mul_div_cancel_right hpos.ne' htop.ne]

/-- For a measure `ξ` dominating `ν` and a function `f` that is `ξ`-almost everywhere at least the
density of `ν` with respect to `ξ`, the density of `μ` with respect to `ξ` divided by `f` is
`ν`-almost everywhere at most the Radon–Nikodym derivative of `μ` with respect to `ν`. -/
theorem rnDeriv_div_ae_le_rnDeriv [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ξ] (hν : ν ≪ ξ)
    {f : α → ℝ≥0∞} (hf : ν.rnDeriv ξ ≤ᵐ[ξ] f) :
    (fun x ↦ μ.rnDeriv ξ x / f x) ≤ᵐ[ν] μ.rnDeriv ν := by
  filter_upwards [hν.ae_le hf, rnDeriv_eq_div' (μ := μ) hν] with x h1 h2
  rw [h2]
  exact ENNReal.div_le_div_left h1 _

/-- A measure below `ν.withDensity f` has a Radon–Nikodym derivative with respect to `ν` that is
`ν`-almost everywhere at most `f`. Mathlib's `MeasureTheory.Measure.rnDeriv_le_one_of_le` is the
case `f = 1`. -/
theorem rnDeriv_le_of_le_withDensity [SigmaFinite ν] {f : α → ℝ≥0∞} (h : μ ≤ ν.withDensity f) :
    μ.rnDeriv ν ≤ᵐ[ν] f :=
  ae_le_of_forall_setLIntegral_le_of_sigmaFinite (μ.measurable_rnDeriv ν) fun s hs _ ↦
    (setLIntegral_rnDeriv_le s).trans ((h s).trans_eq (withDensity_apply _ hs))

/-- The density with respect to `ξ` is monotone in the measure: a measure below a finite
measure `ν` has, `ξ`-almost everywhere, a density below that of `ν`. -/
theorem rnDeriv_le_rnDeriv_of_le [SigmaFinite ξ] [IsFiniteMeasure ν] (h : μ ≤ ν) :
    μ.rnDeriv ξ ≤ᵐ[ξ] ν.rnDeriv ξ := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν h
  have : IsFiniteMeasure (ν - μ) := isFiniteMeasure_of_le ν sub_le
  filter_upwards [rnDeriv_add (ν - μ) μ ξ] with x hx
  rw [sub_add_cancel_of_le h] at hx
  rw [hx, Pi.add_apply]
  exact le_add_self

/-- For a measure `ν = μ.withDensity f` with an almost everywhere finite density and `a < 1`, the
integral `∫⁻ (dμ/dν) ^ a dν`, the affinity of order `a` between `μ` and `ν`, is
`∫⁻ f ^ (1 - a) dμ`. Where `f` vanishes, `ν` charges nothing and `f ^ (1 - a) = 0`. -/
theorem lintegral_rpow_rnDeriv_withDensity [SigmaFinite μ] {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ∞) {a : ℝ} (ha : a < 1) :
    ∫⁻ x, μ.rnDeriv (μ.withDensity f) x ^ a ∂(μ.withDensity f) = ∫⁻ x, f x ^ (1 - a) ∂μ := by
  have : SigmaFinite (μ.withDensity f) := SigmaFinite.withDensity_of_ne_top hf_top
  have hac : μ.withDensity f ≪ μ := withDensity_absolutelyContinuous _ _
  calc ∫⁻ x, μ.rnDeriv (μ.withDensity f) x ^ a ∂(μ.withDensity f)
  _ = ∫⁻ x, ((μ.withDensity f).rnDeriv μ x)⁻¹ ^ a ∂(μ.withDensity f) := by
    refine lintegral_congr_ae ?_
    filter_upwards [inv_rnDeriv hac] with x hx
    rw [← hx, Pi.inv_apply]
  _ = ∫⁻ x, (μ.withDensity f).rnDeriv μ x * ((μ.withDensity f).rnDeriv μ x)⁻¹ ^ a ∂μ :=
    (lintegral_rnDeriv_mul hac (by fun_prop)).symm
  _ = ∫⁻ x, f x ^ (1 - a) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [rnDeriv_withDensity₀ μ hf, hf_top] with x hx hx_top
    rw [hx]
    rcases eq_or_ne (f x) 0 with h0 | h0
    · rw [h0, zero_mul, ENNReal.zero_rpow_of_pos (by linarith)]
    rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, sub_eq_neg_add, ENNReal.rpow_add_one h0 hx_top,
      mul_comm]

end MeasureTheory.Measure
