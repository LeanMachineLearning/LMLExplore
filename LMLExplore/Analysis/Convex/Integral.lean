/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The mean of a function with values in an interval, and Jensen's inequality for the square root

## Main statements

* `MeasureTheory.integral_mem_Icc_of_ae_mem_Icc`: the mean of a function with values in `[l, u]`
  almost everywhere under a probability measure lies in `[l, u]`, by `Convex.integral_mem`.
* `MeasureTheory.integral_id_mem_Icc_of_ae_mem_Icc`: the mean of a probability measure on `ℝ`
  concentrated on `[l, u]` lies in `[l, u]`.
* `MeasureTheory.integral_sqrt_le_sqrt_measureReal_mul_integral`: Jensen's inequality for the
  square root, `∫ √g ∂μ ≤ √(μ(univ) ∫ g ∂μ)` for a finite measure `μ` and an integrable `g ≥ 0`,
  by `ConcaveOn.le_map_average`.
-/

public section

namespace MeasureTheory

/-- The mean of a real function with values in `[l, u]` almost everywhere under a probability
measure lies in `[l, u]`. -/
theorem integral_mem_Icc_of_ae_mem_Icc {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {l u : ℝ} (hf : AEMeasurable f μ)
    (h : ∀ᵐ x ∂μ, f x ∈ Set.Icc l u) : ∫ x, f x ∂μ ∈ Set.Icc l u :=
  (convex_Icc l u).integral_mem isClosed_Icc h (Integrable.of_mem_Icc l u hf h)

/-- The mean of a probability measure on `ℝ` concentrated on `[l, u]` lies in `[l, u]`. -/
theorem integral_id_mem_Icc_of_ae_mem_Icc {μ : Measure ℝ} [IsProbabilityMeasure μ] {l u : ℝ}
    (h : ∀ᵐ x ∂μ, x ∈ Set.Icc l u) : ∫ x, id x ∂μ ∈ Set.Icc l u :=
  integral_mem_Icc_of_ae_mem_Icc aemeasurable_id h

/-- **Jensen's inequality for the square root**: for a finite measure `μ` and an integrable
function `g ≥ 0`, `∫ √g ∂μ ≤ √(μ(univ) ∫ g ∂μ)`. For a probability measure, this is
`∫ √g ∂μ ≤ √(∫ g ∂μ)`. -/
theorem integral_sqrt_le_sqrt_measureReal_mul_integral {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → ℝ} (hg : 0 ≤ᵐ[μ] g) (hgi : Integrable g μ) :
    ∫ x, √(g x) ∂μ ≤ √(μ.real Set.univ * ∫ x, g x ∂μ) := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  have hm : 0 < μ.real Set.univ := measureReal_univ_pos
  -- `√g ≤ g + 1` makes `√g` integrable.
  have hsqrt : Integrable (fun x ↦ √(g x)) μ := by
    refine (hgi.add (integrable_const 1)).mono'
      (Real.continuous_sqrt.comp_aestronglyMeasurable hgi.aestronglyMeasurable) ?_
    filter_upwards [hg] with x (hx : 0 ≤ g x)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Pi.add_apply]
    exact Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have h := Real.strictConcaveOn_sqrt.concaveOn.le_map_average Real.continuous_sqrt.continuousOn
    isClosed_Ici hg hgi hsqrt
  simp only [average_eq, smul_eq_mul] at h
  calc ∫ x, √(g x) ∂μ = μ.real Set.univ * ((μ.real Set.univ)⁻¹ * ∫ x, √(g x) ∂μ) := by
        field_simp
    _ ≤ μ.real Set.univ * √((μ.real Set.univ)⁻¹ * ∫ x, g x ∂μ) := by gcongr
    _ = √(μ.real Set.univ * ∫ x, g x ∂μ) := by
        rw [← Real.sqrt_sq hm.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm.le]
        congr 1
        field_simp

end MeasureTheory
