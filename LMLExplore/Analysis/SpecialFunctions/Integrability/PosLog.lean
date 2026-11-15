/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrability of `log (1 + ∑ i, |f i|)`

Finitely many real functions whose positive logarithms `log⁺ (f i)` are integrable under a finite
measure have an integrable `log (1 + ∑ i, |f i|)`, and damping the sum by a factor in `[0, 1]`
keeps the integrability. As the damping factor tends to `0`, so does the integral of the damped
logarithm, by dominated convergence.

## Main statements

* `Real.abs_log_one_add_mul_le`: `|log (1 + δ t)| ≤ log (1 + t)` for `t ≥ 0` and `δ ∈ [0, 1]`.
* `MeasureTheory.integrable_log_one_add_sum_abs`: if every `log⁺ (f i)` is integrable under a
  finite measure, so is `log (1 + ∑ i, |f i|)`.
* `MeasureTheory.Integrable.log_one_add_const_mul`: if `log (1 + f)` is integrable for a
  nonnegative `f`, so is `log (1 + δ f)` for `δ ∈ [0, 1]`.
* `MeasureTheory.Integrable.tendsto_integral_log_one_add_mul`: if `log (1 + f)` is integrable for
  a nonnegative `f`, then `∫ log (1 + δ f)` tends to `0` as `δ ≥ 0` tends to `0`.
-/

public section

open MeasureTheory Filter Topology

namespace Real

/-- Damping by a factor `δ ∈ [0, 1]` decreases `log (1 + t)`, for `t ≥ 0`, and keeps it
nonnegative. -/
theorem abs_log_one_add_mul_le {δ t : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (ht : 0 ≤ t) :
    |log (1 + δ * t)| ≤ log (1 + t) := by
  have h0 : 0 ≤ δ * t := mul_nonneg hδ ht
  rw [abs_of_nonneg (log_nonneg (by linarith))]
  exact log_le_log (by linarith) (by nlinarith)

end Real

namespace MeasureTheory

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If every `log⁺ (f i)` is integrable under a finite measure, so is `log (1 + ∑ i, |f i|)`. -/
theorem integrable_log_one_add_sum_abs [Fintype ι] [IsFiniteMeasure μ] {f : ι → α → ℝ}
    (hf : ∀ i, AEMeasurable (f i) μ) (h : ∀ i, Integrable (fun x ↦ Real.posLog (f i x)) μ) :
    Integrable (fun x ↦ Real.log (1 + ∑ i, |f i x|)) μ := by
  have hint : Integrable
      (fun x ↦ Real.log (Fintype.card ι) + ∑ i, Real.posLog (f i x) + Real.log 2) μ :=
    ((integrable_const _).add (integrable_finsetSum _ fun i _ ↦ h i)).add (integrable_const _)
  have hm : AEMeasurable (fun x ↦ Real.log (1 + ∑ i, |f i x|)) μ := by fun_prop
  refine hint.mono' hm.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hsum : 0 ≤ ∑ i, |f i x| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith))]
  refine Real.log_one_add_le_posLog.trans ?_
  gcongr
  simpa using Real.posLog_sum Finset.univ fun i ↦ |f i x|

/-- If `log (1 + f)` is integrable for a nonnegative `f`, so is `log (1 + δ f)` for
`δ ∈ [0, 1]`. -/
theorem Integrable.log_one_add_const_mul {f : α → ℝ}
    (h : Integrable (fun x ↦ Real.log (1 + f x)) μ) (hfm : AEMeasurable f μ) (hf : ∀ x, 0 ≤ f x)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    Integrable (fun x ↦ Real.log (1 + δ * f x)) μ := by
  have hm : AEMeasurable (fun x ↦ Real.log (1 + δ * f x)) μ := by fun_prop
  refine h.mono' hm.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  exact Real.abs_log_one_add_mul_le hδ hδ1 (hf x)

/-- If `log (1 + f)` is integrable for a nonnegative `f`, then `∫ log (1 + δ f)` tends to `0` as
the damping factor `δ ≥ 0` tends to `0`, by dominated convergence. -/
theorem Integrable.tendsto_integral_log_one_add_mul {f : α → ℝ}
    (h : Integrable (fun x ↦ Real.log (1 + f x)) μ) (hfm : AEMeasurable f μ) (hf : ∀ x, 0 ≤ f x)
    {β : Type*} {l : Filter β} [l.IsCountablyGenerated] {δ : β → ℝ} (hδ : Tendsto δ l (𝓝 0))
    (hδ0 : ∀ᶠ n in l, 0 ≤ δ n) :
    Tendsto (fun n ↦ ∫ x, Real.log (1 + δ n * f x) ∂μ) l (𝓝 0) := by
  rw [← integral_zero α ℝ (μ := μ)]
  refine tendsto_integral_filter_of_dominated_convergence _
    (.of_forall fun n ↦ (by fun_prop : AEMeasurable (fun x ↦ Real.log (1 + δ n * f x)) μ)
      |>.aestronglyMeasurable)
    ((hδ0.and (hδ.eventually (ge_mem_nhds one_pos))).mono fun n hn ↦ ae_of_all _ fun x ↦ ?_) h
    (ae_of_all _ fun x ↦ ?_)
  · rw [Real.norm_eq_abs]
    exact Real.abs_log_one_add_mul_le hn.1 hn.2 (hf x)
  · have : Tendsto (fun n ↦ 1 + δ n * f x) l (𝓝 1) := by
      simpa using (hδ.mul_const (f x)).const_add 1
    simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp this

end MeasureTheory
