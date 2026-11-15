/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Term-by-term integration of weighted series of bounded functions, and reverse Fatou

If `c` is a summable family of real numbers and the functions `X i` are bounded almost
everywhere by a common constant, then against a finite measure the series `∑' i, c i • X i` can
be integrated term by term. This is the form in which discounted sums of bounded rewards, such as
`∑' n, γ ^ n * r n` with `γ < 1`, are integrated.

Against a finite measure, Fatou's lemma applied to negative parts shows that integrable functions
bounded above by a constant, converging almost everywhere to a function whose negative part has an
infinite integral, include one with a negative integral.

## Main statements

* `MeasureTheory.integral_tsum_smul_of_norm_le`:
  `∫ a, ∑' i, c i • X i a ∂μ = ∑' i, c i • ∫ a, X i a ∂μ`.
* `MeasureTheory.integral_neg_iff_lintegral_ofReal_lt`: an integrable real function has a
  negative integral if and only if its positive part has a smaller integral than its negative
  part.
* `MeasureTheory.exists_integral_neg_of_tendsto`: if integrable functions bounded above by a
  constant converge almost everywhere to a function whose negative part has an infinite integral
  against a finite measure, one of them has a negative integral.
-/

public section

open Set

namespace MeasureTheory

variable {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [Countable ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A series `∑' i, c i • X i` with summable real weights `c` and functions `X i` bounded almost
everywhere by a common constant can be integrated term by term against a finite measure. -/
theorem integral_tsum_smul_of_norm_le [IsFiniteMeasure μ] {c : ι → ℝ} (hc : Summable c)
    {X : ι → α → E} {C : ℝ} (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hXC : ∀ i, ∀ᵐ a ∂μ, ‖X i a‖ ≤ C) :
    ∫ a, ∑' i, c i • X i a ∂μ = ∑' i, c i • ∫ a, X i a ∂μ := by
  have h_int i : Integrable (fun a ↦ c i • X i a) μ := (Integrable.of_bound (hX i) C (hXC i)).smul _
  -- each term has `∫ ‖c i • X i‖ ≤ |c i| * (C * μ univ)`, a summable bound
  have h_le i : ∫ a, ‖c i • X i a‖ ∂μ ≤ |c i| * (C * μ.real univ) := by
    simp_rw [norm_smul, Real.norm_eq_abs, integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le_const <| (hXC i).mono fun a ha ↦ by rwa [norm_norm]
  have h_sum : Summable fun i ↦ ∫ a, ‖c i • X i a‖ ∂μ :=
    .of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) h_le
      (hc.abs.mul_right _)
  rw [← integral_tsum_of_summable_integral_norm h_int h_sum]
  simp_rw [integral_smul]

/-- An integrable real function has a negative integral if and only if its positive part has a
smaller integral than its negative part. -/
theorem integral_neg_iff_lintegral_ofReal_lt {f : α → ℝ} (hf : Integrable f μ) :
    ∫ a, f a ∂μ < 0 ↔ ∫⁻ a, ENNReal.ofReal (f a) ∂μ < ∫⁻ a, ENNReal.ofReal (-f a) ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, sub_neg]
  exact ENNReal.toReal_lt_toReal hf.lintegral_lt_top.ne hf.neg.lintegral_lt_top.ne

open Filter Topology in
/-- **A reverse Fatou argument.** If integrable functions bounded above by a constant converge
almost everywhere to a function whose negative part has an infinite integral against a finite
measure, one of them has a negative integral. -/
theorem exists_integral_neg_of_tendsto [IsFiniteMeasure μ] {f : ℕ → α → ℝ} {F : α → ℝ} {C : ℝ}
    (hf : ∀ k, Integrable (f k) μ) (hfC : ∀ k, ∀ᵐ a ∂μ, f k a ≤ C)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun k ↦ f k a) atTop (𝓝 (F a)))
    (hF : ∫⁻ a, ENNReal.ofReal (-F a) ∂μ = ⊤) : ∃ k, ∫ a, f k a ∂μ < 0 := by
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (f := fun k a ↦ ENNReal.ofReal (-f k a))
    (fun k ↦ (hf k).1.aemeasurable.neg.ennreal_ofReal)
  have hlhs : ∫⁻ a, liminf (fun k ↦ ENNReal.ofReal (-f k a)) atTop ∂μ = ⊤ := by
    rw [← hF]
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with a ha
    exact ((ENNReal.continuous_ofReal.tendsto _).comp ha.neg).liminf_eq
  rw [hlhs, top_le_iff] at hfatou
  have hB : ENNReal.ofReal C * μ univ < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  rw [← hfatou] at hB
  obtain ⟨k, hk⟩ := (eventually_lt_of_lt_liminf hB).exists
  refine ⟨k, (integral_neg_iff_lintegral_ofReal_lt (hf k)).2 (lt_of_le_of_lt ?_ hk)⟩
  rw [← lintegral_const]
  exact lintegral_mono_ae ((hfC k).mono fun a ha ↦ ENNReal.ofReal_le_ofReal ha)

end MeasureTheory
