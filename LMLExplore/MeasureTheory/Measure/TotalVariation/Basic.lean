/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.MeasureTheory.VectorMeasure.Integral
import LMLExplore.Order.ConditionallyCompleteLattice.Group
import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
import TauCeti.MeasureTheory.Measure.TotalVariation.Countable

/-!
# Integrals against measures close in total variation

The total variation distance `tvDist μ ν` of two finite measures (with values in `[0, 2]` for
probability measures) controls the difference of the integrals of bounded functions: if
`‖f‖ ≤ C`, then `‖∫ f dμ - ∫ f dν‖ ≤ C * tvDist μ ν`. When `μ` and `ν` have the same mass, the
bound depends only on the oscillation of `f`: if `f` takes values in `[a, b]`, then
`|∫ f dμ - ∫ f dν| ≤ (b - a) / 2 * tvDist μ ν`. For measures of the same mass, the total
variation distance is also controlled by events: `|μ s - ν s| ≤ tvDist μ ν / 2` for every
measurable `s`, and conversely `tvDist μ ν ≤ 2 * c` as soon as `μ s ≤ ν s + c` for every
measurable `s`. On a finite type, the total variation distance of two
finite measures is `μ univ + ν univ - 2 * ∑ x, min (μ {x}) (ν {x})`, and for probability measures
half of it is the mass `1 - ∑ x, min (μ {x}) (ν {x})` that they do not share.
Adding a common finite measure and scaling both measures by `t` multiplies the
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
* `MeasureTheory.mul_sub_tvDist_div_two_le_integral_add_integral`: for measures of the same mass
  and nonnegative `f`, `g` with `c ≤ f + g`, `c * (μ univ - tvDist μ ν / 2) ≤ ∫ f dμ + ∫ g dν`.
* `MeasureTheory.measure_le_add_etvDist`: `μ s ≤ ν s + etvDist μ ν` for every measurable `s`, and
  `MeasureTheory.measure_le_add_of_etvDist_le` its form `μ s ≤ ν s + ε` when `etvDist ν μ ≤ ε`.
* `MeasureTheory.isProbabilityMeasure_of_forall_exists_etvDist_lt`: a limit in total variation of
  probability measures is a probability measure.
* `MeasureTheory.exists_le_le_add_etvDist`: two finite measures have a common minorant `ρ` with
  `μ univ + ν univ = 2 * ρ univ + etvDist μ ν`.
* `MeasureTheory.abs_measureReal_sub_measureReal_le_tvDist_div_two`,
  `MeasureTheory.tvDist_le_two_mul_of_forall_measureReal_le_add`: for measures of the same mass,
  the total variation distance bounds the difference of the masses of every event, and eventwise
  bounds bound the total variation distance.
* `MeasureTheory.tvDist_eq_measureReal_univ_add_sub_two_mul_sum_min`,
  `MeasureTheory.tvDist_div_two_eq_one_sub_sum_min`: on a finite type, the overlap form
  `tvDist μ ν = μ univ + ν univ - 2 * ∑ x, min (μ {x}) (ν {x})`.
* `MeasureTheory.tvDist_add_smul_add_smul`: `tvDist (ξ + t • μ) (ξ + t • ν) = t * tvDist μ ν`.
* `MeasureTheory.tvDist_one_sub_smul_add_smul`, `MeasureTheory.tvDist_one_sub_smul_add_smul_le`:
  the mixture `(1 - α) • μ + α • ν` is at distance `α * tvDist ν μ` from `μ`, at most `2 * α`
  for probability measures.

## Implementation notes

The first bound is the bound `MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const` on
integrals against the signed measure `μ - ν`, whose variation has mass `tvDist μ ν`. The eventwise
characterization is Tau Ceti's `MeasureTheory.etvDist_le_two_mul_iff`, transferred to the real
distance `tvDist`. The overlap form on a finite type is read off Tau Ceti's `ℓ¹` formula
`MeasureTheory.tvDist_eq_tsum_abs_singleton`, `tvDist μ ν = ∑' x, |μ {x} - ν {x}|` on a countable
type. The behaviour under sums and scalings is read off the supremum over finite
measurable partitions, `MeasureTheory.tvDist_eq_iSup_finPartition_abs`, so it needs no assumption
on the masses.
-/

public section

open Set
open scoped ENNReal NNReal

namespace MeasureTheory

variable {𝓧 E : Type*} {m𝓧 : MeasurableSpace 𝓧} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ ν : Measure 𝓧} {C : ℝ}

/-- The total variation distance of two finite measures is the total mass of the variation of the
difference of the associated signed measures. -/
theorem tvDist_eq_measureReal_variation_sub_toSignedMeasure [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    tvDist μ ν = (μ.toSignedMeasure - ν.toSignedMeasure).variation.real univ := by
  rw [tvDist, etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist, measureReal_def]

/-- The total variation distance between two probability measures is at most two. -/
lemma tvDist_le_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : tvDist μ ν ≤ 2 := by
  simpa [one_add_one_eq_two] using tvDist_le_add (μ := μ) (ν := ν)

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
  -- `f` takes values in `[a, a + c]` with `a` its infimum
  have hmem := mem_Icc_ciInf_of_forall_sub_le hf
  simpa using abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc hμν hfμ hfν
    (ae_of_all _ hmem) (ae_of_all _ hmem)

/-- **Two losses against measures close in total variation**: for finite measures `μ` and `ν` of
the same mass and nonnegative functions `f` and `g` with `c ≤ f x + g x` everywhere,
`c * (μ univ - tvDist μ ν / 2) ≤ ∫ f dμ + ∫ g dν`. For probability measures and the indicators
`f = 1_s` and `g = 1_{sᶜ}` this is `μ s + ν sᶜ ≥ 1 - tvDist μ ν / 2`; for general losses it bounds
from below the sum of the expected losses of any decision made from a sample of `μ` or of `ν`,
when the losses of the two hypotheses add up to at least `c` at every decision. -/
theorem mul_sub_tvDist_div_two_le_integral_add_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ univ = ν univ) {f g : 𝓧 → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g ν) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) {c : ℝ}
    (hc : ∀ x, c ≤ f x + g x) :
    c * (μ.real univ - tvDist μ ν / 2) ≤ ∫ x, f x ∂μ + ∫ x, g x ∂ν := by
  have hreal : ν.real univ = μ.real univ := by simp [measureReal_def, hμν]
  have hint0 : 0 ≤ ∫ x, f x ∂μ + ∫ x, g x ∂ν :=
    add_nonneg (integral_nonneg hf0) (integral_nonneg hg0)
  rcases le_or_gt c 0 with hc0 | hc0
  · have htv : 0 ≤ μ.real univ - tvDist μ ν / 2 := by
      linarith [tvDist_le_add (μ := μ) (ν := ν)]
    exact (mul_nonpos_of_nonpos_of_nonneg hc0 htv).trans hint0
  -- the weight `u = f / (f + g)`, with values in `[0, 1]`, splits `c` between `f` and `g`
  have hpos (x : 𝓧) : 0 < f x + g x := hc0.trans_le (hc x)
  set u : 𝓧 → ℝ := fun x ↦ f x / (f x + g x) with hu_def
  have hu (x : 𝓧) : u x ∈ Icc 0 1 :=
    ⟨div_nonneg (hf0 x) (hpos x).le, div_le_one_of_le₀ (le_add_of_nonneg_right (hg0 x))
      (hpos x).le⟩
  have hum : Measurable u := hfm.div (hfm.add hgm)
  have hint (ρ : Measure 𝓧) [IsFiniteMeasure ρ] : Integrable u ρ :=
    Integrable.of_bound hum.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hu x).1]
      exact (hu x).2)
  have hfu : c * ∫ x, u x ∂μ ≤ ∫ x, f x ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono ((hint μ).const_mul c) hf fun x ↦ ?_
    calc c * u x ≤ (f x + g x) * u x := mul_le_mul_of_nonneg_right (hc x) (hu x).1
      _ = f x := by rw [hu_def]; field_simp [(hpos x).ne']
  have hgu : c * (μ.real univ - ∫ x, u x ∂ν) ≤ ∫ x, g x ∂ν := by
    have h1 : ∫ x, c * (1 - u x) ∂ν = c * (μ.real univ - ∫ x, u x ∂ν) := by
      rw [integral_const_mul, integral_sub (integrable_const 1) (hint ν), integral_const,
        smul_eq_mul, mul_one, hreal]
    rw [← h1]
    refine integral_mono (((integrable_const 1).sub (hint ν)).const_mul c) hg fun x ↦ ?_
    calc c * (1 - u x) ≤ (f x + g x) * (1 - u x) :=
          mul_le_mul_of_nonneg_right (hc x) (sub_nonneg.2 (hu x).2)
      _ = g x := by rw [hu_def]; field_simp [(hpos x).ne']; ring
  have hdiff := abs_integral_sub_integral_le_mul_tvDist_of_mem_Icc hμν hum.aestronglyMeasurable
    hum.aestronglyMeasurable (ae_of_all _ hu) (ae_of_all _ hu)
  have hle : ∫ x, u x ∂ν - ∫ x, u x ∂μ ≤ tvDist μ ν / 2 := by
    have := (abs_le.1 hdiff).1
    linarith
  nlinarith

/-! ### Eventwise bounds -/

/-- **Events of measures close in total variation**, in `ℝ≥0∞`: every measurable event `s`
satisfies `μ s ≤ ν s + etvDist μ ν`. No finiteness is assumed: the distance is `∞` unless both
measures are finite. -/
theorem measure_le_add_etvDist (μ ν : Measure 𝓧) {s : Set 𝓧} (hs : MeasurableSet s) :
    μ s ≤ ν s + etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [etvDist_eq_iSup_sub_add_iSup_sub]
    calc μ s ≤ ν s + (μ s - ν s) := le_add_tsub
    _ ≤ _ := by
      gcongr
      exact le_add_right (le_iSup₂ (f := fun A (_ : MeasurableSet A) ↦ μ A - ν A) s hs)
  · simp [etvDist_of_not_isFiniteMeasure h]

/-- **Events of measures within `ε` in total variation**: if `etvDist ν μ ≤ ε`, every measurable
event `s` satisfies `μ s ≤ ν s + ε`. -/
theorem measure_le_add_of_etvDist_le {μ ν : Measure 𝓧} {s : Set 𝓧} {ε : ℝ≥0∞}
    (hs : MeasurableSet s) (h : etvDist ν μ ≤ ε) : μ s ≤ ν s + ε :=
  (measure_le_add_etvDist μ ν hs).trans (add_le_add le_rfl ((etvDist_comm μ ν).trans_le h))

/-- A limit in total variation of probability measures is a probability measure. -/
theorem isProbabilityMeasure_of_forall_exists_etvDist_lt {S : Set (Measure 𝓧)} {Q : Measure 𝓧}
    (hS : ∀ P ∈ S, IsProbabilityMeasure P) (hQ : ∀ ε > 0, ∃ P ∈ S, etvDist P Q < ε) :
    IsProbabilityMeasure Q := by
  have h (ε : ℝ≥0) (hε : 0 < ε) : Q univ ≤ 1 + ε ∧ 1 ≤ Q univ + ε := by
    obtain ⟨P, hP, hPQ⟩ := hQ ε (ENNReal.coe_pos.2 hε)
    have := hS P hP
    constructor
    · simpa using measure_le_add_of_etvDist_le .univ hPQ.le
    · simpa using measure_le_add_of_etvDist_le (μ := P) .univ ((etvDist_comm Q P).trans_le hPQ.le)
  exact ⟨le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ (h ε hε).1)
    (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ (h ε hε).2)⟩

/-- **A common minorant of two finite measures.** On a Hahn decomposition `s`, the measure
`μ.restrict s + ν.restrict sᶜ` is below `μ` and `ν`, and its mass is the mean of the masses of `μ`
and `ν` minus half their total variation distance. -/
theorem exists_le_le_add_etvDist (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ ρ : Measure 𝓧, ρ ≤ μ ∧ ρ ≤ ν ∧ μ univ + ν univ = 2 * ρ univ + etvDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine ⟨μ.restrict s + ν.restrict sᶜ, ?_, ?_, ?_⟩
  · calc μ.restrict s + ν.restrict sᶜ ≤ μ.restrict s + μ.restrict sᶜ :=
          add_le_add le_rfl hs.ge_on_compl
    _ = μ := Measure.restrict_add_restrict_compl hs.measurableSet
  · calc μ.restrict s + ν.restrict sᶜ ≤ ν.restrict s + ν.restrict sᶜ :=
          add_le_add hs.le_on le_rfl
    _ = ν := Measure.restrict_add_restrict_compl hs.measurableSet
  · have h₁ : μ s ≤ ν s := by simpa using hs.le_on univ
    have h₂ : ν sᶜ ≤ μ sᶜ := by simpa using hs.ge_on_compl univ
    calc μ univ + ν univ = (μ s + μ sᶜ) + (ν s + ν sᶜ) := by
          rw [measure_add_measure_compl hs.measurableSet,
            measure_add_measure_compl hs.measurableSet]
    _ = (μ s + (ν sᶜ + (μ sᶜ - ν sᶜ))) + ((μ s + (ν s - μ s)) + ν sᶜ) := by
          rw [add_tsub_cancel_of_le h₁, add_tsub_cancel_of_le h₂]
    _ = 2 * (μ s + ν sᶜ) + ((ν s - μ s) + (μ sᶜ - ν sᶜ)) := by ring
    _ = 2 * (μ.restrict s + ν.restrict sᶜ) univ + etvDist μ ν := by simp [hs.etvDist_eq]

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

/-- **Total variation and overlap on a finite type**: for finite measures `μ` and `ν` on a finite
type with measurable singletons,
`tvDist μ ν = μ univ + ν univ - 2 * ∑ x, min (μ {x}) (ν {x})`. -/
theorem tvDist_eq_measureReal_univ_add_sub_two_mul_sum_min [Fintype 𝓧]
    [MeasurableSingletonClass 𝓧] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = μ.real univ + ν.real univ - 2 * ∑ x, min (μ.real {x}) (ν.real {x}) := by
  have h (a b : ℝ) : |a - b| = a + b - 2 * min a b := by
    rcases le_total a b with hab | hab
    · rw [abs_of_nonpos (sub_nonpos.2 hab), min_eq_left hab]; ring
    · rw [abs_of_nonneg (sub_nonneg.2 hab), min_eq_right hab]; ring
  simp only [tvDist_eq_tsum_abs_singleton, tsum_fintype, h, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_measureReal_singleton, Finset.coe_univ]

/-- **Total variation and overlap on a finite type**: for probability measures `μ` and `ν` on a
finite type with measurable singletons, `tvDist μ ν / 2 = 1 - ∑ x, min (μ {x}) (ν {x})`: half
the total variation distance is the mass that `μ` and `ν` do not have in common. -/
theorem tvDist_div_two_eq_one_sub_sum_min [Fintype 𝓧] [MeasurableSingletonClass 𝓧]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν / 2 = 1 - ∑ x, min (μ.real {x}) (ν.real {x}) := by
  rw [tvDist_eq_measureReal_univ_add_sub_two_mul_sum_min, probReal_univ, probReal_univ]
  ring

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
  exact tvDist_le_two

end MeasureTheory
