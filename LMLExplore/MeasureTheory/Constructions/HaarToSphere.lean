/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import TauCeti.Analysis.Normed.Module.Normalize.Measurable
import TauCeti.MeasureTheory.Constructions.HaarToSphere

/-!
# Polar coordinates over a cone

Tau Ceti's `TauCeti.lintegral_eq_lintegral_toSphere_lintegral_Ioi` integrates a nonnegative
function on a finite-dimensional real normed space in polar coordinates. This file restricts it to
the cone `NormedSpace.normalize ⁻¹' s` of the vectors whose direction lies in a set `s`: the
integral is then the integral over the directions in `s` only. This computes the law of the
direction `x / ‖x‖` of a measure with a density, as for the direction of a shifted Gaussian vector
in `LMLExplore.Probability.Distributions.Gaussian.Polar`.
-/

public section

open MeasureTheory TauCeti
open scoped ENNReal

namespace LMLExplore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Integration in polar coordinates over a cone.** The integral of `f` over the vectors whose
direction lies in `s` is the integral over the directions `u ∈ s`, against `μ.toSphere`, of the
radial integral `∫_0^∞ r^(d-1) f(r u) dr`. -/
theorem lintegral_indicator_normalize_preimage {f : E → ℝ≥0∞} (hf : Measurable f) {s : Set E}
    (hs : MeasurableSet s) :
    ∫⁻ y, (NormedSpace.normalize ⁻¹' s).indicator f y ∂μ =
      ∫⁻ u : Metric.sphere (0 : E) 1, s.indicator 1 (u : E) *
        (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * f (r • (u : E)))
        ∂μ.toSphere := by
  rw [lintegral_eq_lintegral_toSphere_lintegral_Ioi (hf.indicator (measurable_normalize hs))]
  refine lintegral_congr fun u ↦ ?_
  have h_dir (r : ℝ) (hr : r ∈ Set.Ioi (0 : ℝ)) : NormedSpace.normalize (r • (u : E)) = u := by
    rw [NormedSpace.normalize_smul_of_pos hr,
      NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere u)]
  by_cases hus : (u : E) ∈ s
  · rw [Set.indicator_of_mem hus, Pi.one_apply, one_mul]
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    simp [h_dir r hr, hus]
  · rw [Set.indicator_of_notMem hus, zero_mul]
    refine (setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_).trans lintegral_zero
    simp [h_dir r hr, hus]

end LMLExplore
