/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import Mathlib.MeasureTheory.Function.Floor

/-!
# Uniform approximation of bounded measurable functions through a map with finite range

Finitely many bounded measurable real functions `g i` on a measurable space `Ω` are uniformly
approximated, within any `δ > 0`, by their compositions `g i ∘ s` with a single measurable map
`s : Ω → Ω` with finite range. The map `s` sends each point to a chosen point of its cell, where
the cells are the level sets of `x ↦ (⌊g i x / δ⌋)ᵢ`, a measurable map with finitely many values.

For a finite measure `μ`, the image measure `μ.map s` is then carried by the finite range of `s`,
and its integrals of the `g i` are within `δ * μ univ` of those of `μ`. This is how
`LMLExplore.EValues.Examples.BipolarRate.Envelope` and
`LMLExplore.EValues.Examples.BipolarRate.InverseSquare` find laws carried by finite sets in the
basic neighbourhoods of a probability measure for the topology of the integrals of the bounded
measurable functions.

## Main statements

* `MeasureTheory.exists_measurable_finite_range_forall_abs_comp_sub_lt`: the uniform
  approximation of finitely many bounded measurable real functions through a measurable map with
  finite range.
* `MeasureTheory.exists_measurable_finite_range_forall_abs_integral_map_sub_le`: the image of a
  finite measure `μ` by such a map has integrals of the `g i` within `δ * μ univ` of those of `μ`.
-/

public section

open Set

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Uniform approximation through a map with finite range.** For finitely many bounded
measurable real functions `g i` and `δ > 0`, some measurable map `s : Ω → Ω` with finite range has
`|g i (s x) - g i x| < δ` for every `i` and every `x`. -/
theorem exists_measurable_finite_range_forall_abs_comp_sub_lt {ι : Type*} [Finite ι]
    {g : ι → Ω → ℝ} (hg : ∀ i, Measurable (g i)) (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ s : Ω → Ω, Measurable s ∧ (range s).Finite ∧ ∀ i x, |g i (s x) - g i x| < δ := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨id, measurable_id, finite_range _, fun _ x ↦ isEmptyElim x⟩
  choose C hC using hgb
  -- the cell of a point: the integer parts of the `g i / δ`
  set φ : Ω → ι → ℤ := fun x i ↦ ⌊g i x / δ⌋ with hφ_def
  have hφ : Measurable φ := .of_eval fun i ↦ ((hg i).div_const δ).floor
  have hφr : (range φ).Finite := by
    refine (Finite.pi (t := fun i ↦ Icc ⌊-C i / δ⌋ ⌊C i / δ⌋) fun i ↦ finite_Icc _ _).subset ?_
    rintro _ ⟨x, rfl⟩ i -
    obtain ⟨h1, h2⟩ := abs_le.1 (hC i x)
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right h1 hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right h2 hδ.le)⟩
  refine ⟨Function.invFun φ ∘ φ, (measurable_of_countable _).comp hφ,
    by rw [range_comp]; exact hφr.image _, fun i x ↦ ?_⟩
  -- a point and the chosen point of its cell have the same integer parts
  have h := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun (Function.invFun_eq ⟨x, rfl⟩ :
    φ (Function.invFun φ (φ x)) = φ x) i)
  rwa [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at h

/-- **Image measures with finite support close to a finite measure.** For finitely many bounded
measurable real functions `g i`, `δ > 0` and a finite measure `μ`, some measurable map
`s : Ω → Ω` with finite range has `|∫ g i ∂(μ.map s) - ∫ g i ∂μ| ≤ δ * μ univ` for every `i`. -/
theorem exists_measurable_finite_range_forall_abs_integral_map_sub_le {ι : Type*} [Finite ι]
    {g : ι → Ω → ℝ} (hg : ∀ i, Measurable (g i)) (hgb : ∀ i, ∃ C, ∀ x, |g i x| ≤ C) {δ : ℝ}
    (hδ : 0 < δ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    ∃ s : Ω → Ω, Measurable s ∧ (range s).Finite ∧
      ∀ i, |∫ x, g i x ∂μ.map s - ∫ x, g i x ∂μ| ≤ δ * μ.real univ := by
  obtain ⟨s, hs, hsf, hsg⟩ := exists_measurable_finite_range_forall_abs_comp_sub_lt hg hgb hδ
  refine ⟨s, hs, hsf, fun i ↦ ?_⟩
  obtain ⟨C, hC⟩ := hgb i
  rw [integral_map hs.aemeasurable (hg i).aestronglyMeasurable,
    ← integral_sub (LMLExplore.integrable_of_abs_le (f := fun x ↦ g i (s x)) ((hg i).comp hs)
      (fun x ↦ hC (s x)) μ) (LMLExplore.integrable_of_abs_le (hg i) hC μ), ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const
    (.of_forall fun x ↦ (Real.norm_eq_abs _).trans_le (hsg i x).le)

end MeasureTheory
