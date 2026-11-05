/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.VectorMeasure.Integral
import TauCeti.MeasureTheory.Measure.TotalVariation

/-!
# Integrals against measures close in total variation

The total variation distance `tvDist μ ν` of two finite measures (with values in `[0, 2]` for
probability measures) controls the difference of the integrals of bounded functions: if
`‖f‖ ≤ C`, then `‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν`. When `μ` and `ν` have the same mass, the
bound depends only on the oscillation of `f`: if `f` takes values in `[a, b]`, then
`|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`. For measures of the same mass, the total
variation distance is also controlled by events: `|μ s - ν s| ≤ tvDist μ ν / 2` for every
measurable `s`, and conversely `tvDist μ ν ≤ 2 * c` as soon as `μ s ≤ ν s + c` for every
measurable `s`. Adding a common finite measure and scaling both measures by `t` multiplies the
distance by `t`, so the distance from a mixture `(1 - α) • μ + α • ν` to `μ` is
`α * tvDist ν μ`, at most `2 * α` for probability measures.

These are the bounds through which errors in transition kernels, measured in total variation,
propagate to expected values, as in the simulation lemma for Markov decision processes and in the
contraction of the oscillation of functions by a Markov kernel (Dobrushin's coefficient).

## Main statements

* `MeasureTheory.tvDist_eq_measureReal_variation_sub_toSignedMeasure`: `tvDist μ ν` is the total
  mass of the variation of the signed measure `μ - ν`.
* `MeasureTheory.norm_integral_sub_integral_le_mul_tvDist`:
  `‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν` for `‖f‖ ≤ C` almost everywhere, `f` with values in a
  normed space.
* `MeasureTheory.abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc`: for measures of the same
  mass and `f` with values in `[a, b]` almost everywhere,
  `|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`, and
  `MeasureTheory.abs_integral_sub_integral_le_mul_tvDist_of_forall_sub_le` its form for `f` whose
  values differ by at most `c`.
* `MeasureTheory.abs_measureReal_sub_measureReal_le_tvDist_div_two`,
  `MeasureTheory.tvDist_le_two_mul_of_forall_measureReal_le_add`: for measures of the same mass,
  the total variation distance bounds the difference of the masses of every event, and eventwise
  bounds bound the total variation distance.
* `MeasureTheory.tvDist_add_smul_add_smul`: `tvDist (ξ + t • μ) (ξ + t • ν) = t * tvDist μ ν`.
* `MeasureTheory.tvDist_one_sub_smul_add_smul`, `MeasureTheory.tvDist_one_sub_smul_add_smul_le`:
  the mixture `(1 - α) • μ + α • ν` is at distance `α * tvDist ν μ` from `μ`, at most `2 * α`
  for probability measures.

## Implementation notes

The first bound is the bound `MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const` on
integrals against the signed measure `μ - ν`, whose variation has mass `tvDist μ ν`. The eventwise
characterization is Tau Ceti's `MeasureTheory.etvDist_le_two_mul_iff`, transferred to the real
distance `tvDist`. The behaviour under sums and scalings is read off the supremum over finite
measurable partitions, `MeasureTheory.tvDist_eq_iSup_finPartition_abs`, so it needs no assumption
on the masses.
-/

public section

open Set
open scoped NNReal

namespace MeasureTheory

variable {𝓧 E : Type*} {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ ν : Measure 𝓧} {C : ℝ}

/-- The total variation distance of two finite measures is the total mass of the variation of the
difference of the associated signed measures. -/
theorem tvDist_eq_measureReal_variation_sub_toSignedMeasure [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν = (μ.toSignedMeasure - ν.toSignedMeasure).variation.real univ := by
  rw [tvDist, etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist, measureReal_def]

/-- **Integrals against measures close in total variation**: for finite measures `μ` and `ν` and
a function `f` with values in a normed space, bounded in norm by `C` almost everywhere for both,
`‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν`. -/
theorem norm_integral_sub_integral_le_mul_tvDist [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : 𝓧 → E} (hfμ : AEStronglyMeasurable f μ) (hfν : AEStronglyMeasurable f ν)
    (hfCμ : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) (hfCν : ∀ᵐ x ∂ν, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂μ - ∫ x, f x ∂ν‖ ≤ C * tvDist μ ν := by
  have hint (ρ : Measure 𝓧) [IsFiniteMeasure ρ] (hf : AEStronglyMeasurable f ρ)
      (hC : ∀ᵐ x ∂ρ, ‖f x‖ ≤ C) : ρ.toSignedMeasure.Integrable f := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    exact Integrable.of_bound hf C hC
  -- write `∫ f dμ - ∫ f dν` as the integral of `f` against the signed measure `μ - ν`
  rw [← VectorMeasure.integral_toSignedMeasure, ← VectorMeasure.integral_toSignedMeasure (μ := ν),
    ← VectorMeasure.integral_sub_vectorMeasure (hint μ hfμ hfCμ) (hint ν hfν hfCν),
    tvDist_eq_measureReal_variation_sub_toSignedMeasure]
  -- the variation of `μ - ν` is dominated by `μ + ν`, so `‖f‖ ≤ C` almost everywhere for it
  have hle : (μ.toSignedMeasure - ν.toSignedMeasure).variation ≤ μ + ν := by
    simpa using VectorMeasure.variation_sub_le (μ := μ.toSignedMeasure) (ν := ν.toSignedMeasure)
  have := isFiniteMeasure_of_le _ hle
  have hae : ∀ᵐ x ∂(μ.toSignedMeasure - ν.toSignedMeasure).variation, ‖f x‖ ≤ C :=
    ae_mono hle (ae_add_measure_iff.2 ⟨hfCμ, hfCν⟩)
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) hae
  -- `C` is nonnegative unless the variation of `μ - ν` vanishes
  rcases eq_or_ne (μ.toSignedMeasure - ν.toSignedMeasure).variation 0 with h0 | h0
  · simpa [h0] using h
  have := ae_neBot.2 h0
  obtain ⟨x, hx⟩ := hae.exists
  refine h.trans (mul_le_mul_of_nonneg_right ?_ measureReal_nonneg)
  rw [ContinuousLinearMap.opNorm_flip]
  exact mul_le_of_le_one_right ((norm_nonneg _).trans hx) ContinuousLinearMap.opNorm_lsmul_le

/-- **Integrals against measures of the same mass close in total variation**: for finite measures
`μ` and `ν` of the same mass and a function `f` with values in `[a, b]` almost everywhere for
both, `|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`. -/
theorem abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) {f : 𝓧 → ℝ} {a b : ℝ}
    (hfμ : AEStronglyMeasurable f μ) (hfν : AEStronglyMeasurable f ν)
    (hfμ' : ∀ᵐ x ∂μ, f x ∈ Icc a b) (hfν' : ∀ᵐ x ∂ν, f x ∈ Icc a b) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (b - a) / 2 * tvDist μ ν := by
  -- center `f` at the midpoint of `[a, b]`
  have hc {x : 𝓧} (hx : f x ∈ Icc a b) : ‖f x - (a + b) / 2‖ ≤ (b - a) / 2 :=
    abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hB {x : 𝓧} (hx : f x ∈ Icc a b) : ‖f x‖ ≤ max |a| |b| :=
    abs_le_max_abs_abs hx.1 hx.2
  have h := norm_integral_sub_integral_le_mul_tvDist (f := fun x ↦ f x - (a + b) / 2)
    (hfμ.sub aestronglyMeasurable_const) (hfν.sub aestronglyMeasurable_const)
    (hfμ'.mono fun _ ↦ hc) (hfν'.mono fun _ ↦ hc)
  rw [integral_sub (Integrable.of_bound hfμ _ (hfμ'.mono fun _ ↦ hB)) (integrable_const _),
    integral_sub (Integrable.of_bound hfν _ (hfν'.mono fun _ ↦ hB)) (integrable_const _)] at h
  simpa [measureReal_def, hμν] using h

/-- **Integrals against measures of the same mass close in total variation**, oscillation form:
for finite measures `μ` and `ν` of the same mass and a real function `f` whose values differ by at
most `c`, `|∫ f dμ - ∫ f dν| ≤ c / 2 * tvDist μ ν`. -/
theorem abs_integral_sub_integral_le_mul_tvDist_of_forall_sub_le [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) {f : 𝓧 → ℝ} {c : ℝ}
    (hfμ : AEStronglyMeasurable f μ) (hfν : AEStronglyMeasurable f ν)
    (hf : ∀ x y, f x - f y ≤ c) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ c / 2 * tvDist μ ν := by
  rcases isEmpty_or_nonempty 𝓧 with h𝓧 | h𝓧
  · simp [Measure.eq_zero_of_isEmpty μ, Measure.eq_zero_of_isEmpty ν]
  obtain ⟨x₀⟩ := id h𝓧
  -- `f` takes values in `[a, a + c]` with `a` its infimum
  have hbdd : BddBelow (range f) := ⟨f x₀ - c, by rintro _ ⟨y, rfl⟩; linarith [hf x₀ y]⟩
  have hmem (x : 𝓧) : f x ∈ Icc (⨅ y, f y) ((⨅ y, f y) + c) :=
    ⟨ciInf_le hbdd x, by rw [← sub_le_iff_le_add]; exact le_ciInf fun y ↦ by linarith [hf x y]⟩
  simpa using abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc hμν hfμ hfν
    (ae_of_all _ hmem) (ae_of_all _ hmem)

/-! ### Eventwise bounds -/

/-- **Events of measures of the same mass close in total variation**: for finite measures `μ`
and `ν` of the same mass, every measurable event `s` satisfies
`|μ s - ν s| ≤ tvDist μ ν / 2`. -/
theorem abs_measureReal_sub_measureReal_le_tvDist_div_two [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) {s : Set 𝓧} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| ≤ tvDist μ ν / 2 := by
  have h := abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc hμν (f := s.indicator 1)
    (a := 0) (b := 1) (by fun_prop (disch := exact hs)) (by fun_prop (disch := exact hs))
    (ae_of_all _ fun x ↦ by by_cases hx : x ∈ s <;> simp [hx])
    (ae_of_all _ fun x ↦ by by_cases hx : x ∈ s <;> simp [hx])
  rw [integral_indicator_one hs, integral_indicator_one hs] at h
  exact h.trans_eq (by ring)

/-- **Total variation from eventwise bounds**: for finite measures `μ` and `ν` of the same mass,
if every measurable event `s` satisfies `μ s ≤ ν s + c`, then `tvDist μ ν ≤ 2 * c`. -/
theorem tvDist_le_two_mul_of_forall_measureReal_le_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ univ = ν univ) {c : ℝ} (h : ∀ s, MeasurableSet s → μ.real s ≤ ν.real s + c) :
    tvDist μ ν ≤ 2 * c := by
  have hc : 0 ≤ c := by simpa using h ∅ MeasurableSet.empty
  have he : etvDist μ ν ≤ 2 * ENNReal.ofReal c := by
    refine (etvDist_le_two_mul_iff hμν).2 fun s hs ↦ ?_
    rw [← ofReal_measureReal (μ := μ), ← ofReal_measureReal (μ := ν),
      ← ENNReal.ofReal_add measureReal_nonneg hc]
    exact ENNReal.ofReal_le_ofReal (h s hs)
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_tvDist,
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
  exact he

/-! ### Sums and mixtures -/

/-- Adding a common finite measure to two finite measures `μ` and `ν`, after scaling both by
`t`, multiplies their total variation distance by `t`:
`tvDist (ξ + t • μ) (ξ + t • ν) = t * tvDist μ ν`. -/
theorem tvDist_add_smul_add_smul {ξ : Measure 𝓧} [IsFiniteMeasure ξ] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (t : ℝ≥0) :
    tvDist (ξ + t • μ) (ξ + t • ν) = t * tvDist μ ν := by
  rw [tvDist_eq_iSup_finPartition_abs, tvDist_eq_iSup_finPartition_abs,
    Real.mul_iSup_of_nonneg t.coe_nonneg]
  -- on every event, the differences of masses are scaled by `t`
  refine iSup_congr fun P ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [measureReal_add_apply, measureReal_add_apply]
  simp [← mul_sub, abs_mul]

/-- **Total variation of a mixture**: for finite measures `μ` and `ν` and `α ≤ 1`, the mixture
`(1 - α) • μ + α • ν` is at distance `α * tvDist ν μ` from `μ`. -/
theorem tvDist_one_sub_smul_add_smul [IsFiniteMeasure μ] [IsFiniteMeasure ν] {α : ℝ≥0}
    (hα : α ≤ 1) :
    tvDist ((1 - α) • μ + α • ν) μ = α * tvDist ν μ := by
  conv_lhs => enter [2]; rw [← one_smul ℝ≥0 μ, ← tsub_add_cancel_of_le hα, add_smul]
  exact tvDist_add_smul_add_smul α

/-- **Total variation of a mixture of probability measures**: for probability measures `μ` and
`ν` and `α ≤ 1`, the mixture `(1 - α) • μ + α • ν` is within `2 * α` of `μ`. -/
theorem tvDist_one_sub_smul_add_smul_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {α : ℝ≥0} (hα : α ≤ 1) :
    tvDist ((1 - α) • μ + α • ν) μ ≤ 2 * α := by
  rw [tvDist_one_sub_smul_add_smul hα, mul_comm]
  gcongr
  simpa [one_add_one_eq_two] using tvDist_le_add (μ := ν) (ν := μ)

end MeasureTheory
