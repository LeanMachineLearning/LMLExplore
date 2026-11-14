/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Fatou's lemma for setwise convergence of measures

A family of measures `μs i` converges setwise to `μ` along a filter `l` when `μs i s` tends to
`μ s` for every measurable set `s`. Under setwise convergence the lower Lebesgue integral is lower
semicontinuous: `∫⁻ f ∂μ ≤ liminf (fun i ↦ ∫⁻ f ∂μs i) l` for every function `f : α → ℝ≥0∞`,
with no measurability, finiteness or integrability assumption. This is Fatou's lemma with the
measures, rather than the functions, varying. It shows, for instance, that a set of measures
defined by upper bounds on the integrals of a family of functions is closed under setwise
convergence.

## Main statements

* `MeasureTheory.lintegral_le_liminf_of_tendsto_measure`: the lower Lebesgue integral is lower
  semicontinuous under setwise convergence.
* `MeasureTheory.lintegral_le_of_frequently_of_tendsto_measure`: if `∫⁻ f ∂μs i ≤ c` frequently
  along `l`, then `∫⁻ f ∂μ ≤ c`.
-/

public section

open Filter Topology
open scoped ENNReal NNReal

namespace MeasureTheory

variable {α ι : Type*} {mα : MeasurableSpace α} {l : Filter ι} {μs : ι → Measure α}
  {μ : Measure α}

/-- **Fatou's lemma for setwise convergence**: if `μs i s` tends to `μ s` along `l` for every
measurable set `s`, then the lower Lebesgue integral of any function under `μ` is at most the
inferior limit of its integrals under `μs i`. -/
theorem lintegral_le_liminf_of_tendsto_measure
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ ≤ liminf (fun i ↦ ∫⁻ x, f x ∂μs i) l := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  rw [lintegral_eq_nnreal]
  refine iSup₂_le fun φ hφ ↦ ?_
  -- The integral of a simple function with finite values is a finite combination of the
  -- measures of measurable sets, hence converges.
  have hφ_tendsto : Tendsto (fun i ↦ (φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral (μs i)) l
      (𝓝 ((φ.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral μ)) := by
    simp only [SimpleFunc.map_lintegral]
    exact tendsto_finsetSum _ fun c _ ↦ ENNReal.Tendsto.const_mul
      (h _ (φ.measurableSet_preimage _)) (.inr ENNReal.coe_ne_top)
  rw [← hφ_tendsto.liminf_eq]
  refine liminf_le_liminf (.of_forall fun i ↦ ?_)
  rw [← SimpleFunc.lintegral_eq_lintegral]
  exact lintegral_mono fun x ↦ by simpa using hφ x

/-- If `μs i` converges setwise to `μ` along `l` and `∫⁻ f ∂μs i ≤ c` frequently along `l`, then
`∫⁻ f ∂μ ≤ c`. -/
theorem lintegral_le_of_frequently_of_tendsto_measure
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) {f : α → ℝ≥0∞}
    {c : ℝ≥0∞} (hc : ∃ᶠ i in l, ∫⁻ x, f x ∂μs i ≤ c) :
    ∫⁻ x, f x ∂μ ≤ c :=
  (lintegral_le_liminf_of_tendsto_measure h f).trans (liminf_le_of_frequently_le' hc)

end MeasureTheory
