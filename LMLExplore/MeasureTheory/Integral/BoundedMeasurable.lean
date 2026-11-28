/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Normed.Lp.Measurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.Floor

/-!
# Integrals of bounded measurable functions

A bounded measurable function `f : LMLExplore.boundedMeasurable β` is integrable against every
finite measure `μ`, and its integral is bounded in absolute value by `‖f‖ * μ univ`.

## Main statements

* `LMLExplore.boundedMeasurable.integrable`: a bounded measurable function is integrable for every
  finite measure.
* `LMLExplore.boundedMeasurable.abs_integral_le`: `|∫ y, f y ∂μ| ≤ ‖f‖ * μ.real univ`.
* `LMLExplore.integrable_of_abs_le`, `LMLExplore.abs_integral_le_of_abs_le`: the same statements
  for a function `f : β → ℝ` with `|f| ≤ B`, the second one against a probability measure.
* `LMLExplore.integrable_exp_of_abs_le`: for a measurable `f : β → ℝ` with `|f| ≤ B`, `exp ∘ f` is
  integrable for every finite measure.
* `LMLExplore.abs_integral_mixture_sub_le`: mixing a measure `F` with `Q`, with weights `1 - ε`
  and `ε`, brings its integral of `f` closer to that of `Q`.
* `LMLExplore.integrable_integral_kernel_of_abs_le`: for a Markov kernel `κ`, the integral
  `a ↦ ∫ f d(κ a)` of a measurable `f` with `|f| ≤ B` is integrable for every finite measure.
* `LMLExplore.integral_comp_eq_sum`: the integral of a function of a finite measurable partition
  `π : β → Fin k` is the sum over the cells of its values times their masses.
* `LMLExplore.exists_measurable_fin_step_le`: a measurable `g` with `|g| ≤ N` is, within `δ > 0`,
  approximated from below by a step function on a finite measurable partition.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal lp

namespace LMLExplore

variable {β : Type*} [MeasurableSpace β]

/-- A measurable function bounded by `B` in absolute value is integrable for every finite
measure. -/
lemma integrable_of_abs_le {f : β → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B)
    (μ : Measure β) [IsFiniteMeasure μ] : Integrable f μ :=
  .of_bound hf.aestronglyMeasurable B (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hfB x))

/-- The exponential of a measurable function bounded by `B` in absolute value is integrable for
every finite measure. -/
lemma integrable_exp_of_abs_le {f : β → ℝ} {B : ℝ} (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B)
    (μ : Measure β) [IsFiniteMeasure μ] : Integrable (fun x ↦ Real.exp (f x)) μ :=
  .of_bound hf.exp.aestronglyMeasurable (Real.exp B) (.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_of_abs_le (hfB x)))

/-- The integral against a probability measure of a function bounded by `B` in absolute value is
bounded by `B` in absolute value. -/
lemma abs_integral_le_of_abs_le {f : β → ℝ} {B : ℝ} {μ : Measure β} [IsProbabilityMeasure μ]
    (hfB : ∀ x, |f x| ≤ B) : |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f)
      (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hfB x))

/-- Mixing a measure `F` with `Q`, with weights `1 - ε` and `ε` for `ε ≤ 1`, brings its integral
of `f` closer to that of `Q`: if `|∫ f ∂F - ∫ f ∂Q| ≤ δ`, then
`|∫ f ∂((1 - ε) F + ε Q) - ∫ f ∂Q| ≤ δ`. -/
lemma abs_integral_mixture_sub_le {F Q : Measure β} {ε : ℝ≥0∞} (hε : ε ≤ 1) {f : β → ℝ}
    (hfF : Integrable f F) (hfQ : Integrable f Q) {δ : ℝ} (h : |∫ x, f x ∂F - ∫ x, f x ∂Q| ≤ δ) :
    |∫ x, f x ∂((1 - ε) • F + ε • Q) - ∫ x, f x ∂Q| ≤ δ := by
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε
  rw [integral_add_measure (hfF.smul_measure (by simp)) (hfQ.smul_measure hεt),
    integral_smul_measure, integral_smul_measure]
  have hsum : (1 - ε).toReal + ε.toReal = 1 := by
    rw [← ENNReal.toReal_add (by simp) hεt, tsub_add_cancel_of_le hε, ENNReal.toReal_one]
  have h1 : 0 ≤ (1 - ε).toReal := ENNReal.toReal_nonneg
  have h1' : (1 - ε).toReal ≤ 1 := by linarith [ENNReal.toReal_nonneg (a := ε)]
  have heq : (1 - ε).toReal • (∫ x, f x ∂F) + ε.toReal • (∫ x, f x ∂Q) - ∫ x, f x ∂Q =
      (1 - ε).toReal * (∫ x, f x ∂F - ∫ x, f x ∂Q) := by
    rw [smul_eq_mul, smul_eq_mul]
    linear_combination (∫ x, f x ∂Q) * hsum
  rw [heq, abs_mul, abs_of_nonneg h1]
  calc (1 - ε).toReal * |∫ x, f x ∂F - ∫ x, f x ∂Q|
  _ ≤ 1 * δ := mul_le_mul h1' h (abs_nonneg _) zero_le_one
  _ = δ := one_mul δ

/-- For a Markov kernel `κ` and a measurable function `f` bounded by `B` in absolute value, the
integral `a ↦ ∫ f d(κ a)` is integrable for every finite measure. -/
lemma integrable_integral_kernel_of_abs_le {α : Type*} [MeasurableSpace α] {f : β → ℝ} {B : ℝ}
    (hf : Measurable f) (hfB : ∀ x, |f x| ≤ B) (κ : Kernel α β) [IsMarkovKernel κ]
    (μ : Measure α) [IsFiniteMeasure μ] : Integrable (fun a ↦ ∫ x, f x ∂(κ a)) μ :=
  integrable_of_abs_le (hf.stronglyMeasurable.integral_kernel (κ := κ)).measurable
    (fun _ ↦ abs_integral_le_of_abs_le hfB) μ

/-! ### Finite measurable partitions -/

/-- The integral of a function of a finite measurable partition `π` is the sum over the cells of
its values times their masses. -/
lemma integral_comp_eq_sum (μ : Measure β) [IsFiniteMeasure μ] {k : ℕ} {π : β → Fin k}
    (hπ : Measurable π) (F : Fin k → ℝ) :
    ∫ x, F (π x) ∂μ = ∑ j, F j * μ.real (π ⁻¹' {j}) := by
  rw [← integral_map hπ.aemeasurable (measurable_of_finite F).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_measureReal_apply hπ (measurableSet_singleton j), smul_eq_mul, mul_comm]

/-- A measurable function `g` with `|g| ≤ N` is, up to `δ > 0`, a step function on a finite
measurable partition: there are a measurable `π : β → Fin n` and values `h` with
`g - δ ≤ h ∘ π ≤ g` and `|h| ≤ N + δ`. -/
lemma exists_measurable_fin_step_le {g : β → ℝ} (hg : Measurable g) {N : ℝ}
    (hgN : ∀ x, |g x| ≤ N) {δ : ℝ} (hδ0 : 0 < δ) :
    ∃ (n : ℕ) (π : β → Fin n) (h : Fin n → ℝ), Measurable π ∧
      (∀ x, g x - δ ≤ h (π x) ∧ h (π x) ≤ g x) ∧ ∀ j, |h j| ≤ N + δ := by
  -- the step function `g'` below `g`, at distance at most `δ`
  set g' : β → ℝ := fun x ↦ δ * ⌊g x / δ⌋ with hg'
  have hgf (x : β) : g' x ≤ g x := by
    have h := Int.floor_le (g x / δ)
    calc g' x = δ * ⌊g x / δ⌋ := rfl
      _ ≤ δ * (g x / δ) := by gcongr
      _ = g x := by field_simp
  have hfg (x : β) : g x - δ ≤ g' x := by
    have h := Int.lt_floor_add_one (g x / δ)
    have h' : g x / δ - 1 ≤ ⌊g x / δ⌋ := by linarith
    calc g x - δ = δ * (g x / δ - 1) := by field_simp
      _ ≤ δ * ⌊g x / δ⌋ := by gcongr
      _ = g' x := rfl
  have hg'm : Measurable g' := measurable_const.mul
    (measurable_from_top.comp (Int.measurable_floor.comp (hg.div_const δ)))
  have hg'N (x : β) : |g' x| ≤ N + δ := by
    rw [abs_le]
    have := abs_le.1 (hgN x)
    exact ⟨by linarith [hfg x], by linarith [hgf x]⟩
  -- the range of `g'` is finite
  have hrange : (Set.range g').Finite := by
    have hsub : Set.range g' ⊆ (fun z : ℤ ↦ δ * z) '' Set.Icc ⌊-N / δ⌋ ⌊N / δ⌋ := by
      rintro _ ⟨x, rfl⟩
      refine ⟨⌊g x / δ⌋, ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, rfl⟩
      · exact div_le_div_of_nonneg_right (abs_le.1 (hgN x)).1 hδ0.le
      · exact div_le_div_of_nonneg_right (abs_le.1 (hgN x)).2 hδ0.le
    exact ((Set.finite_Icc _ _).image _).subset hsub
  -- `g'` is a function of a finite measurable partition `π`
  have := hrange.fintype
  set e := Fintype.equivFin (Set.range g')
  set π : β → Fin (Fintype.card (Set.range g')) := fun x ↦ e ⟨g' x, x, rfl⟩ with hπ
  set h : Fin (Fintype.card (Set.range g')) → ℝ := fun j ↦ (e.symm j : Set.range g') with hh
  have hgπ (x : β) : h (π x) = g' x := by simp [hh, hπ]
  have hπm : Measurable π := by
    refine measurable_to_countable' fun i ↦ ?_
    have hi : π ⁻¹' {i} = g' ⁻¹' {((e.symm i : Set.range g') : ℝ)} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro rfl
        exact (hgπ x).symm
      · intro hx
        rw [hπ, ← e.eq_symm_apply]
        exact Subtype.ext hx
    rw [hi]
    exact hg'm (measurableSet_singleton _)
  refine ⟨_, π, h, hπm, fun x ↦ hgπ x ▸ ⟨hfg x, hgf x⟩, fun j ↦ ?_⟩
  obtain ⟨x, hx⟩ := (e.symm j).property
  rw [show h j = g' x from hx.symm]
  exact hg'N x

namespace boundedMeasurable

/-- A bounded measurable function is integrable for every finite measure. -/
lemma integrable (f : boundedMeasurable β) (μ : Measure β) [IsFiniteMeasure μ] :
    Integrable (⇑(f : ℓ^∞(β, ℝ))) μ :=
  integrable_of_abs_le (measurable f) (abs_apply_le_norm f) μ

/-- The integral of a bounded measurable function `f` against a finite measure `μ` is at most
`‖f‖ * μ univ` in absolute value. -/
lemma abs_integral_le (f : boundedMeasurable β) {μ : Measure β} [IsFiniteMeasure μ] :
    |∫ y, (f : ℓ^∞(β, ℝ)) y ∂μ| ≤ ‖f‖ * μ.real univ := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const <| .of_forall fun y ↦
    (Real.norm_eq_abs _).trans_le (abs_apply_le_norm f y)

end boundedMeasurable

end LMLExplore
