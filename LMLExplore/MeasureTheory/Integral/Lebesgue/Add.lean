/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Order.Filter.ENNReal
public import TauCeti.Topology.Instances.ENNReal

/-!
# Lebesgue integral of finite sums and lower semicontinuity under setwise convergence

## Main statements

* `MeasureTheory.lintegral_finsetSum_indicator_one`: the Lebesgue integral of a finite sum of
  indicators of measurable sets is the sum of their measures, and
  `MeasureTheory.lintegral_finsetSum_indicator_one₀`, its version for null measurable sets.
* `MeasureTheory.lintegral_comp_eq_sum_measure_preimage_singleton`: the integral of `g ∘ φ`, for a
  map `φ` to a finite type, is `∑ i, g i * μ (φ ⁻¹' {i})`.
* `MeasureTheory.SimpleFunc.tendsto_lintegral_of_tendsto_measure`: the integral of a simple function
  with finite values is continuous for the setwise convergence of measures.
* `MeasureTheory.SimpleFunc.lintegral_le_liminf_lintegral`: the integral of a simple function with
  finite values is lower semicontinuous when the measures of measurable sets are.
* `MeasureTheory.lintegral_le_liminf_lintegral_of_forall_measurableSet_measure_le_liminf_measure`:
  if `μ s ≤ liminf (μs i s)` along a filter for every measurable set `s`, then
  `∫⁻ f ∂μ ≤ liminf (∫⁻ f ∂μs i)` for every measurable `f`; in particular the Lebesgue integral
  is lower semicontinuous for the setwise convergence of measures. This is the measurable-set
  counterpart of the portmanteau inequality
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

/-- The integral of a function of a map `φ` with values in a finite type is the sum, over the
values `i`, of the value at `i` times the mass of the fibre of `i`. -/
lemma lintegral_comp_eq_sum_measure_preimage_singleton {κ : Type*} [Fintype κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] {φ : α → κ} (hφ : AEMeasurable φ μ)
    (g : κ → ℝ≥0∞) :
    ∫⁻ x, g (φ x) ∂μ = ∑ i, g i * μ (φ ⁻¹' {i}) := by
  rw [← lintegral_map' (measurable_of_finite g).aemeasurable hφ, lintegral_fintype]
  simp_rw [Measure.map_apply_of_aemeasurable hφ (measurableSet_singleton _)]

section Setwise

variable {ι : Type*} {l : Filter ι} {μs : ι → Measure α}

/-- The integral of a simple function with finite values is continuous for the setwise convergence
of measures. -/
theorem SimpleFunc.tendsto_lintegral_of_tendsto_measure (f : SimpleFunc α ℝ≥0∞)
    (hf : ∀ y ∈ f.range, y ≠ ∞)
    (h : ∀ s, MeasurableSet s → Tendsto (fun i ↦ μs i s) l (𝓝 (μ s))) :
    Tendsto (fun i ↦ f.lintegral (μs i)) l (𝓝 (f.lintegral μ)) := by
  unfold SimpleFunc.lintegral
  exact tendsto_finsetSum _ fun y hy ↦
    ENNReal.Tendsto.const_mul (h _ (f.measurableSet_preimage _)) (.inr (hf y hy))

/-- The integral of a simple function with finite values is lower semicontinuous along a filter
when the measures of measurable sets are: if `μ s ≤ liminf (μs i s)` for every measurable set
`s`, then `f.lintegral μ ≤ liminf (f.lintegral (μs i))`. -/
theorem SimpleFunc.lintegral_le_liminf_lintegral [l.NeBot] (f : SimpleFunc α ℝ≥0∞)
    (hf : ∀ y ∈ f.range, y ≠ ∞) (h : ∀ s, MeasurableSet s → μ s ≤ liminf (fun i ↦ μs i s) l) :
    f.lintegral μ ≤ liminf (fun i ↦ f.lintegral (μs i)) l := by
  unfold SimpleFunc.lintegral
  refine (Finset.sum_le_sum fun y hy ↦ ?_).trans (ENNReal.sum_liminf_le_liminf_sum _ _)
  rw [ENNReal.liminf_const_mul_of_ne_top (hf y hy)]
  gcongr
  exact h _ (f.measurableSet_preimage _)

/-- **Lower semicontinuity of the Lebesgue integral.** If `μ s ≤ liminf (μs i s)` along a filter
for every measurable set `s`, then `∫⁻ f ∂μ ≤ liminf (∫⁻ f ∂μs i)` for every measurable `f`. This
covers the setwise convergence of measures along any filter, so it holds for nets of measures and
not only for sequences. -/
theorem lintegral_le_liminf_lintegral_of_forall_measurableSet_measure_le_liminf_measure [l.NeBot]
    {f : α → ℝ≥0∞} (hf : Measurable f)
    (h : ∀ s, MeasurableSet s → μ s ≤ liminf (fun i ↦ μs i s) l) :
    ∫⁻ x, f x ∂μ ≤ liminf (fun i ↦ ∫⁻ x, f x ∂μs i) l := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  refine iSup_le fun n ↦ ?_
  refine ((SimpleFunc.eapprox f n).lintegral_le_liminf_lintegral (fun y hy ↦ ?_) h).trans
    (liminf_le_liminf (.of_forall fun i ↦ ?_))
  · obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.mp hy
    exact (SimpleFunc.eapprox_lt_top f n x).ne
  · rw [lintegral_eq_iSup_eapprox_lintegral hf]
    exact le_iSup (fun n ↦ (SimpleFunc.eapprox f n).lintegral (μs i)) n

end Setwise

end MeasureTheory
