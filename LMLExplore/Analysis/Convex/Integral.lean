/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# The mean of a function with values in an interval, and Jensen's inequality for the square root
and the exponential

## Main statements

* `MeasureTheory.integral_mem_Icc_of_ae_mem_Icc`: the mean of a function with values in `[l, u]`
  almost everywhere under a probability measure lies in `[l, u]`, by `Convex.integral_mem`.
* `MeasureTheory.integral_id_mem_Icc_of_ae_mem_Icc`: the mean of a probability measure on `ℝ`
  concentrated on `[l, u]` lies in `[l, u]`.
* `MeasureTheory.integral_sqrt_le_sqrt_measureReal_mul_integral`: Jensen's inequality for the
  square root, `∫ √g ∂μ ≤ √(μ(univ) ∫ g ∂μ)` for a finite measure `μ` and an integrable `g ≥ 0`,
  by `ConcaveOn.le_map_average`.
* `MeasureTheory.ofReal_measureReal_mul_exp_average_le_lintegral`: Jensen's inequality for the
  exponential, `μ(univ) exp (⨍ f ∂μ) ≤ ∫⁻ exp f ∂μ` for a finite measure `μ` and an integrable
  `f`, with no integrability assumption on `exp f`, by `exp t ≥ exp a (1 + t - a)`.
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

/-- **Jensen's inequality for the exponential**, in the form of a lower integral: for a finite
measure `μ` and an integrable function `f`, `μ(univ) exp (⨍ f ∂μ) ≤ ∫⁻ exp f ∂μ`. The function
`exp f` need not be integrable. The proof integrates `exp a (1 + (f - a)) ≤ exp f` for the mean
`a` of `f`. -/
theorem ofReal_measureReal_mul_exp_average_le_lintegral {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (μ.real Set.univ * Real.exp (⨍ x, f x ∂μ)) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  have hc : 0 < μ.real Set.univ := measureReal_univ_pos
  set a := ⨍ x, f x ∂μ
  have ha : ∫ x, f x ∂μ = μ.real Set.univ * a := by
    simp only [a, average_eq, smul_eq_mul]
    field_simp
  calc ENNReal.ofReal (μ.real Set.univ * Real.exp a)
  _ = ENNReal.ofReal (∫ x, Real.exp a * (1 + (f x - a)) ∂μ) := by
    have h : ∫ x, (1 + (f x - a)) ∂μ = μ.real Set.univ := by
      have h' : ∫ x, (1 + (f x - a)) ∂μ = ∫ _, (1 - a) ∂μ + ∫ x, f x ∂μ := by
        rw [← integral_add (integrable_const _) hf]
        exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
      rw [h', integral_const, ha, smul_eq_mul]
      ring
    rw [integral_const_mul, h, mul_comm]
  _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp a * (1 + (f x - a))) ∂μ :=
    TauCeti.MeasureTheory.ofReal_integral_le_lintegral_ofReal
  _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ := lintegral_mono fun x ↦ by
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp a * (1 + (f x - a)) ≤ Real.exp a * Real.exp (f x - a) := by
          gcongr
          linarith [Real.add_one_le_exp (f x - a)]
    _ = Real.exp (f x) := by rw [← Real.exp_add, add_sub_cancel]

end MeasureTheory
