/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Probability.Distributions.Laplace.Basic

/-!
# Translates of the Laplace law

The Laplace density `(2 b)⁻¹ exp (-|x - μ| / b)` is log-Lipschitz with constant `b⁻¹`: moving the
location by `u` multiplies it by at most `exp (|u| / b)`. Hence every translate of Tau Ceti's
Laplace law `TauCeti.Probability.laplaceMeasure μ b` by `u` is at most `exp (b⁻¹ |u|)` times the
law. This is the hypothesis of `MeasureTheory.Measure.lintegral_smul_le_conv_of_forall_map_add_le`,
under which a prior on a location parameter is compared with its mixtures.

## Main statements

* `TauCeti.Probability.laplaceMeasure_map_add_le`:
  `(laplaceMeasure μ b).map (· + u) ≤ exp (b⁻¹ |u|) • laplaceMeasure μ b`.

## Implementation notes

This bound is adapted from `laplace_density_sub_le` and `map_add_laplaceMeasure_le` in
`EValuesResearch/Results/TTestGrowAux.lean` (commit `562b62e`) of the paper project
`RemyDegenne/evalues_research`, which use a Laplace prior of their own, of rate
`b` and centred at `0`; it is stated here for Tau Ceti's Laplace law of any location and scale.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

/-- Every translate of the Laplace law of scale `b` by `u` is at most `exp (b⁻¹ |u|)` times the
law. For `b ≤ 0` both sides vanish. -/
theorem laplaceMeasure_map_add_le (μ b u : ℝ) :
    (laplaceMeasure μ b).map (· + u) ≤
      ENNReal.ofReal (Real.exp (b⁻¹ * |u|)) • laplaceMeasure μ b := by
  rw [laplaceMeasure_map_add_const, laplaceMeasure_eq_withDensity, laplaceMeasure_eq_withDensity,
    ← withDensity_smul _ (measurable_laplacePDF μ b)]
  refine withDensity_mono (ae_of_all _ fun x ↦ ?_)
  rcases le_or_gt b 0 with hb | hb
  · simp [laplacePDF_of_nonpos hb]
  rw [Pi.smul_apply, smul_eq_mul, laplacePDF_of_pos hb, laplacePDF_of_pos hb,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_left_comm, ← Real.exp_add]
  gcongr
  have h := abs_sub_abs_le_abs_sub (x - μ) (x - (μ + u))
  rw [show x - μ - (x - (μ + u)) = u by ring] at h
  rw [div_eq_inv_mul, div_eq_inv_mul]
  have hb' : 0 < b⁻¹ := inv_pos.mpr hb
  nlinarith

end TauCeti.Probability
