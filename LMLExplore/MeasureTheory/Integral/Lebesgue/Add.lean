/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Lebesgue integral of finite sums and lower semicontinuity under setwise convergence

## Main statements

* `MeasureTheory.lintegral_finsetSum_indicator_one`: the Lebesgue integral of a finite sum of
  indicators of measurable sets is the sum of their measures, and
  `MeasureTheory.lintegral_finsetSum_indicator_one₀`, its version for null measurable sets.
* `MeasureTheory.SimpleFunc.tendsto_lintegral_of_tendsto_measure`: the integral of a simple function
  with finite values is continuous for the setwise convergence of measures.
* `MeasureTheory.lintegral_le_liminf_lintegral_of_tendsto_measure`: the Lebesgue integral of a
  measurable function is lower semicontinuous for the setwise convergence of measures, along any
  filter. This is the setwise counterpart of the portmanteau inequality
  `MeasureTheory.lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure`.
-/

public section

open Filter

open scoped ENNReal Topology

namespace MeasureTheory

variable {α ι : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Finset ι} {S : ι → Set α}

/-- The Lebesgue integral of a finite sum of indicators of null measurable sets is the sum of their
measures. -/
lemma lintegral_finsetSum_indicator_one₀ (hS : ∀ i ∈ s, NullMeasurableSet (S i) μ) :
    ∫⁻ a, ∑ i ∈ s, (S i).indicator 1 a ∂μ = ∑ i ∈ s, μ (S i) := by
  rw [lintegral_finsetSum' (f := fun i ↦ (S i).indicator 1) _
    fun i hi ↦ measurable_one.aemeasurable.indicator₀ (hS i hi)]
  exact Finset.sum_congr rfl fun i hi ↦ lintegral_indicator_one₀ (hS i hi)

/-- The Lebesgue integral of a finite sum of indicators of measurable sets is the sum of their
measures. -/
lemma lintegral_finsetSum_indicator_one (hS : ∀ i ∈ s, MeasurableSet (S i)) :
    ∫⁻ a, ∑ i ∈ s, (S i).indicator 1 a ∂μ = ∑ i ∈ s, μ (S i) :=
  lintegral_finsetSum_indicator_one₀ fun i hi ↦ (hS i hi).nullMeasurableSet

section Setwise

variable {ι : Type*} {l : Filter ι} {μs : ι → Measure α}

/-- The integral of a simple function with finite values is continuous for the setwise convergence
of measures. -/
theorem SimpleFunc.tendsto_lintegral_of_tendsto_measure (f : SimpleFunc α ℝ≥0∞)
    (hf : ∀ y ∈ f.range, y ≠ ∞)
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) :
    Tendsto (fun i ↦ f.lintegral (μs i)) l (𝓝 (f.lintegral μ)) :=
  tendsto_finsetSum _ fun y hy ↦
    ENNReal.Tendsto.const_mul (h _ (f.measurableSet_preimage _)) (.inr (hf y hy))

/-- **Lower semicontinuity of the Lebesgue integral under setwise convergence.** If `μs i s`
tends to `μ s` along a filter for every measurable set `s`, then
`∫⁻ f ∂μ ≤ liminf (∫⁻ f ∂μs i)` for every measurable `f`. The filter is arbitrary, so this holds
for nets of measures and not only for sequences. -/
theorem lintegral_le_liminf_lintegral_of_tendsto_measure [l.NeBot] {f : α → ℝ≥0∞}
    (hf : Measurable f) (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) :
    ∫⁻ x, f x ∂μ ≤ liminf (fun i ↦ ∫⁻ x, f x ∂μs i) l := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  refine iSup_le fun n ↦ ?_
  have h_tendsto := (SimpleFunc.eapprox f n).tendsto_lintegral_of_tendsto_measure
    (fun y hy ↦ by
      obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.mp hy
      exact (SimpleFunc.eapprox_lt_top f n x).ne) h
  rw [← h_tendsto.liminf_eq]
  refine liminf_le_liminf (.of_forall fun i ↦ ?_)
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  exact le_iSup (fun n ↦ (SimpleFunc.eapprox f n).lintegral (μs i)) n

end Setwise

end MeasureTheory
