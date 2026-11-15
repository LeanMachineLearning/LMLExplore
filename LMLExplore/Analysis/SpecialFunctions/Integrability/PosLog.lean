/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Integrability of `log (1 + ∑ i, |f i|)`

Finitely many real functions whose positive logarithms `log⁺ (f i)` are integrable under a finite
measure have an integrable `log (1 + ∑ i, |f i|)`, and damping the sum by a factor in `[0, 1]`
keeps the integrability.

## Main statements

* `Real.abs_log_one_add_mul_le`: `|log (1 + δ t)| ≤ log (1 + t)` for `t ≥ 0` and `δ ∈ [0, 1]`.
* `MeasureTheory.integrable_log_one_add_sum_abs`: if every `log⁺ (f i)` is integrable under a
  finite measure, so is `log (1 + ∑ i, |f i|)`.
* `MeasureTheory.Integrable.log_one_add_const_mul`: if `log (1 + f)` is integrable for a
  nonnegative `f`, so is `log (1 + δ f)` for `δ ∈ [0, 1]`.
-/

public section

open MeasureTheory

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

end MeasureTheory
