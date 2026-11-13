/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Term-by-term integration of weighted series of bounded functions

If `c` is a summable family of real numbers and the functions `X i` are bounded almost
everywhere by a common constant, then against a finite measure the series `∑' i, c i • X i` can
be integrated term by term. This is the form in which discounted sums of bounded rewards, such as
`∑' n, γ ^ n * r n` with `γ < 1`, are integrated.

## Main statements

* `MeasureTheory.integral_tsum_smul_of_norm_le`:
  `∫ a, ∑' i, c i • X i a ∂μ = ∑' i, c i • ∫ a, X i a ∂μ`.
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

end MeasureTheory
