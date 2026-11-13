/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MeasureTheory.Measure.Weighted
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Hoeffding's lemma for probability vectors

For a probability vector `w` on a finite type and values `ℓ a` in an interval `[lo, hi]`, the
logarithm of the weighted exponential sum `∑ a, w a exp (t ℓ a)` is at most
`t ⟨w, ℓ⟩ + t ^ 2 (hi - lo) ^ 2 / 8`. This is Hoeffding's lemma
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) for the measure `weightedMeasure w`.

## Main statements

* `LMLExplore.log_sum_mul_exp_le`: Hoeffding's lemma for a probability vector.
-/

public section

open Finset Real MeasureTheory ProbabilityTheory

namespace LMLExplore

variable {α : Type*} [Fintype α]

/-- **Hoeffding's lemma** for a probability vector. If `w` is a probability vector and the values
`ℓ a` lie in `[lo, hi]`, then `log ∑ a, w a exp (t ℓ a) ≤ t ⟨w, ℓ⟩ + t ^ 2 (hi - lo) ^ 2 / 8`. -/
theorem log_sum_mul_exp_le {w : α → ℝ} (hw : w ∈ simplex α) {ℓ : α → ℝ} {lo hi : ℝ}
    (hℓ : ∀ a, ℓ a ∈ Set.Icc lo hi) (t : ℝ) :
    log (∑ a, w a * exp (t * ℓ a)) ≤ t * ∑ a, w a * ℓ a + t ^ 2 * (hi - lo) ^ 2 / 8 := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ ↦ trivial⟩
  have _ := isProbabilityMeasure_weightedMeasure hw
  have hint (f : α → ℝ) : ∫ a, f a ∂(weightedMeasure w) = ∑ a, w a * f a := by
    simp [integral_weightedMeasure_eq_sum (mem_simplex_iff.1 hw).1]
  have hpos : 0 < ∑ a, w a * exp (t * ℓ a) := by
    simpa only [mgf, hint] using
      mgf_pos (X := ℓ) (μ := weightedMeasure w) (t := t) Integrable.of_finite
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := weightedMeasure w)
    (measurable_of_countable ℓ).aemeasurable (ae_of_all _ hℓ)).mgf_le t
  simp only [mgf, hint] at h
  set m := ∑ a, w a * ℓ a
  have hsplit : ∑ a, w a * exp (t * (ℓ a - m)) = exp (-(t * m)) * ∑ a, w a * exp (t * ℓ a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [mul_sub, sub_eq_add_neg, exp_add]
    ring
  rw [hsplit, ← le_div_iff₀' (exp_pos _), ← exp_sub] at h
  rw [log_le_iff_le_exp hpos]
  refine h.trans_eq (congrArg exp ?_)
  simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat,
    div_pow, sq_abs]
  ring

end LMLExplore
