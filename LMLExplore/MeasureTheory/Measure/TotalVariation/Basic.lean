/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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
half of it is the mass `1 - ∑ x, min (μ {x}) (ν {x})` that they do not share; in particular,
convergence of the masses of all points implies convergence in total variation.
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
* `MeasureTheory.limsup_measure_le_of_tendsto_etvDist`: if `μs i` tends to `ν` in total
  variation, then `limsup μs i s ≤ ν s` for every measurable `s`.
* `MeasureTheory.isProbabilityMeasure_of_forall_exists_etvDist_lt`: a limit in total variation of
  probability measures is a probability measure.
* `MeasureTheory.exists_le_le_add_etvDist`: two finite measures have a common minorant `ρ` with
  `μ univ + ν univ = 2 * ρ univ + etvDist μ ν`.
* `MeasureTheory.tvDist_le_two_mul_iff`: for measures of the same mass and any real `c`,
  `tvDist μ ν ≤ 2 * c` if and only if `μ s ≤ ν s + c` for every measurable `s`.
* `MeasureTheory.abs_measureReal_sub_measureReal_le_tvDist_div_two`,
  `MeasureTheory.tvDist_le_two_mul_of_forall_measureReal_le_add`: for measures of the same mass,
  the total variation distance bounds the difference of the masses of every event, and eventwise
  bounds bound the total variation distance.
* `MeasureTheory.tvDist_eq_measureReal_univ_add_sub_two_mul_sum_min`,
  `MeasureTheory.tvDist_div_two_eq_one_sub_sum_min`: on a finite type, the overlap form
  `tvDist μ ν = μ univ + ν univ - 2 * ∑ x, min (μ {x}) (ν {x})`;
  `MeasureTheory.tendsto_tvDist_of_tendsto_measureReal_singleton`: on a finite type, convergence
  of the masses of all points implies convergence in total variation.
* `MeasureTheory.tvDist_add_smul_add_smul`: `tvDist (ξ + t • μ) (ξ + t • ν) = t * tvDist μ ν`.
* `MeasureTheory.tvDist_one_sub_smul_add_smul`, `MeasureTheory.tvDist_one_sub_smul_add_smul_le`:
  the mixture `(1 - α) • μ + α • ν` is at distance `α * tvDist ν μ` from `μ`, at most `2 * α`
  for probability measures.
* `MeasureTheory.tendsto_tvDist_one_sub_smul_add_smul`: mixtures `(1 - α i) • μ + α i • ν i` of
  probability measures with weights `α i → 0` tend to `μ` in total variation.
* `MeasureTheory.lintegral_eNorm_toReal_rnDeriv_sub_le_etvDist`: for every σ-finite `ξ`, the
  `L¹(ξ)` distance of the densities of `μ` and `ν` with respect to `ξ` is at most
  `etvDist μ ν`.
* `MeasureTheory.exists_seq_tendsto_ae_rnDeriv_of_tendsto_etvDist`: along a subsequence of a
  sequence converging in total variation, the densities with respect to any σ-finite measure
  converge almost everywhere.

## Implementation notes

The first bound is the bound `MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const` on
integrals against the signed measure `μ - ν`, whose variation has mass `tvDist μ ν`. The eventwise
characterization `MeasureTheory.tvDist_le_two_mul_iff` is Tau Ceti's
`MeasureTheory.etvDist_le_two_mul_iff`, transferred to the real distance `tvDist`, and both
eventwise bounds are its two directions. The overlap form on a finite type is read off Tau
Ceti's `ℓ¹` formula `MeasureTheory.tvDist_eq_tsum_abs_singleton`,
`tvDist μ ν = ∑' x, |μ {x} - ν {x}|` on a countable type. The behaviour under sums and scalings is
read off the supremum over finite measurable partitions,
`MeasureTheory.tvDist_eq_iSup_finPartition_abs`, so it needs no assumption on the masses.
The `L¹` bound on the densities splits the space where the density of `μ` dominates that of `ν`,
removes from it a `ξ`-null set carrying the part of `ν` singular with respect to `ξ`, and
compares the result with Tau Ceti's `MeasureTheory.etvDist_eq_iSup_sub_add_iSup_sub`. Neither
measure need be absolutely continuous with respect to `ξ`.
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

/-- **Events of measures converging in total variation**: if `μs i` tends to `ν` in total
variation, then `limsup μs i s ≤ ν s` for every measurable event `s`. No finiteness is assumed. -/
theorem limsup_measure_le_of_tendsto_etvDist {ι : Type*} {l : Filter ι} {μs : ι → Measure 𝓧}
    (h : Filter.Tendsto (fun i ↦ etvDist (μs i) ν) l (nhds 0)) {s : Set 𝓧} (hs : MeasurableSet s) :
    Filter.limsup (fun i ↦ μs i s) l ≤ ν s := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have htend : Filter.Tendsto (fun i ↦ ν s + etvDist (μs i) ν) l (nhds (ν s)) := by
    simpa using tendsto_const_nhds.add h
  calc Filter.limsup (fun i ↦ μs i s) l
      ≤ Filter.limsup (fun i ↦ ν s + etvDist (μs i) ν) l :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall fun i ↦ measure_le_add_etvDist _ _ hs)
    _ = ν s := htend.limsup_eq

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

/-- **Eventwise characterization of total variation**: for finite measures `μ` and `ν` of the
same mass and any real `c`, `tvDist μ ν ≤ 2 * c` if and only if every measurable event `s`
satisfies `μ s ≤ ν s + c`. This is Tau Ceti's `etvDist_le_two_mul_iff` for the real distance
`tvDist`. -/
theorem tvDist_le_two_mul_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ univ = ν univ) {c : ℝ} :
    tvDist μ ν ≤ 2 * c ↔ ∀ s, MeasurableSet s → μ.real s ≤ ν.real s + c := by
  by_cases hc : 0 ≤ c
  swap
  -- for `c < 0` both sides fail: `tvDist` is nonnegative and the empty event forces `0 ≤ c`
  · refine iff_of_false (fun h ↦ hc ?_) fun h ↦ hc ?_
    · linarith [tvDist_nonneg (μ := μ) (ν := ν)]
    · simpa using h ∅ MeasurableSet.empty
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ofReal_tvDist,
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, etvDist_le_two_mul_iff hμν]
  refine forall₂_congr fun s _ ↦ ?_
  rw [← ofReal_measureReal (μ := μ), ← ofReal_measureReal (μ := ν),
    ← ENNReal.ofReal_add measureReal_nonneg hc,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg measureReal_nonneg hc)]

/-- **Events of measures of the same mass close in total variation**: for finite measures `μ`
and `ν` of the same mass, every measurable event `s` satisfies
`|μ s - ν s| ≤ tvDist μ ν / 2`. -/
theorem abs_measureReal_sub_measureReal_le_tvDist_div_two [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμν : μ univ = ν univ) {s : Set 𝓧} (hs : MeasurableSet s) :
    |μ.real s - ν.real s| ≤ tvDist μ ν / 2 := by
  -- the eventwise characterization at `c = tvDist μ ν / 2`, in either order
  have h (μ ν : Measure 𝓧) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ univ = ν univ) :
      μ.real s ≤ ν.real s + tvDist μ ν / 2 :=
    (tvDist_le_two_mul_iff hμν).1
      (mul_div_cancel₀ _ two_ne_zero).ge s hs
  have h₁ := h μ ν hμν
  have h₂ := h ν μ hμν.symm
  rw [tvDist_comm ν μ] at h₂
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- **Total variation from eventwise bounds**: for finite measures `μ` and `ν` of the same mass,
if every measurable event `s` satisfies `μ s ≤ ν s + c`, then `tvDist μ ν ≤ 2 * c`. -/
theorem tvDist_le_two_mul_of_forall_measureReal_le_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ univ = ν univ) {c : ℝ} (h : ∀ s, MeasurableSet s → μ.real s ≤ ν.real s + c) :
    tvDist μ ν ≤ 2 * c :=
  (tvDist_le_two_mul_iff hμν).2 h

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

/-- **Convergence in total variation on a finite type**: on a finite type with measurable
singletons, finite measures `ρ i` converge to the finite measure `ν` in total variation along a
filter as soon as the mass `ρ i {x}` of every point converges to `ν {x}`. -/
theorem tendsto_tvDist_of_tendsto_measureReal_singleton [Finite 𝓧] [MeasurableSingletonClass 𝓧]
    [IsFiniteMeasure ν] {ι : Type*} {l : Filter ι} {ρ : ι → Measure 𝓧}
    [∀ i, IsFiniteMeasure (ρ i)]
    (h : ∀ x, Filter.Tendsto (fun i ↦ (ρ i).real {x}) l (nhds (ν.real {x}))) :
    Filter.Tendsto (fun i ↦ tvDist (ρ i) ν) l (nhds 0) := by
  have := Fintype.ofFinite 𝓧
  simp_rw [tvDist_eq_tsum_abs_singleton, tsum_fintype]
  simpa using tendsto_finsetSum Finset.univ fun x _ ↦ ((h x).sub_const (ν.real {x})).abs

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

/-- **Mixtures with vanishing weights tend to the base measure**: for probability measures `μ`
and `ν i` and weights `α i ≤ 1` tending to `0`, the mixtures `(1 - α i) • μ + α i • ν i` tend to
`μ` in total variation. It suffices that the hypotheses hold eventually. -/
theorem tendsto_tvDist_one_sub_smul_add_smul {ι : Type*} {l : Filter ι} [IsProbabilityMeasure μ]
    {ν : ι → Measure 𝓧} {α : ι → ℝ≥0} (hα : Filter.Tendsto α l (nhds 0))
    (hα1 : ∀ᶠ i in l, α i ≤ 1) (hν : ∀ᶠ i in l, IsProbabilityMeasure (ν i)) :
    Filter.Tendsto (fun i ↦ tvDist ((1 - α i) • μ + α i • ν i) μ) l (nhds 0) := by
  have hlim : Filter.Tendsto (fun i ↦ 2 * (α i : ℝ)) l (nhds 0) := by
    simpa using (NNReal.tendsto_coe.2 hα).const_mul (2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ tvDist_nonneg) ?_
  filter_upwards [hα1, hν] with i hi _
  exact tvDist_one_sub_smul_add_smul_le hi

/-! ### Densities of measures close in total variation -/

/-- On a measurable set where the density of `μ` with respect to `ξ` dominates that of `ν`, the
integral of the difference of the densities is at most the largest excess `μ B - ν B` over
measurable events. -/
private theorem setLIntegral_tsub_rnDeriv_le_iSup (μ ν ξ : Measure 𝓧) [IsFiniteMeasure ν]
    [SigmaFinite ξ] {A : Set 𝓧} (hA : MeasurableSet A)
    (hle : ∀ x ∈ A, ν.rnDeriv ξ x ≤ μ.rnDeriv ξ x) :
    ∫⁻ x in A, μ.rnDeriv ξ x - ν.rnDeriv ξ x ∂ξ ≤
      ⨆ (B : Set 𝓧) (_ : MeasurableSet B), μ B - ν B := by
  -- remove from `A` a `ξ`-null set carrying the singular part of `ν`
  set h := ν.mutuallySingular_singularPart ξ
  set B := A ∩ h.nullSet
  have hB : MeasurableSet B := hA.inter h.measurableSet_nullSet
  have hAB : ξ.restrict B = ξ.restrict A :=
    Measure.restrict_congr_set (inter_ae_eq_left_of_ae_eq_univ
      (ae_eq_univ.2 h.measure_compl_nullSet))
  have hν : ν B = ∫⁻ x in B, ν.rnDeriv ξ x ∂ξ := by
    conv_lhs => rw [← ν.rnDeriv_add_singularPart ξ]
    rw [add_apply, withDensity_apply _ hB,
      measure_mono_null inter_subset_right h.measure_nullSet, add_zero]
  refine le_trans ?_ (le_iSup₂ (f := fun B (_ : MeasurableSet B) ↦ μ B - ν B) B hB)
  rw [← hAB, lintegral_sub (ν.measurable_rnDeriv ξ) ?_ ?_, hν]
  · exact tsub_le_tsub_right (Measure.setLIntegral_rnDeriv_le B) _
  · exact (hν.symm.trans_lt (measure_lt_top ν B)).ne
  · exact (ae_restrict_iff' hB).2 (Filter.Eventually.of_forall fun x hx ↦ hle x hx.1)

/-- **Densities of measures close in total variation**: for every σ-finite measure `ξ`, the
`L¹(ξ)` distance of the densities of `μ` and `ν` with respect to `ξ` is at most their total
variation distance. Neither measure need be absolutely continuous with respect to `ξ`, and no
finiteness is assumed: the total variation distance is `∞` unless both measures are finite.
When both are finite and absolutely continuous with respect to `ξ` the two sides are equal. -/
theorem lintegral_eNorm_toReal_rnDeriv_sub_le_etvDist (μ ν ξ : Measure 𝓧) [SigmaFinite ξ] :
    ∫⁻ x, ‖(μ.rnDeriv ξ x).toReal - (ν.rnDeriv ξ x).toReal‖ₑ ∂ξ ≤ etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  swap
  · simp [etvDist_of_not_isFiniteMeasure h]
  obtain ⟨_, _⟩ := h
  set f := μ.rnDeriv ξ
  set g := ν.rnDeriv ξ
  set A := {x | g x ≤ f x}
  have hA : MeasurableSet A := measurableSet_le (ν.measurable_rnDeriv ξ) (μ.measurable_rnDeriv ξ)
  rw [etvDist_eq_iSup_sub_add_iSup_sub, ← lintegral_add_compl _ hA]
  gcongr ?_ + ?_
  · calc ∫⁻ x in A, ‖(f x).toReal - (g x).toReal‖ₑ ∂ξ = ∫⁻ x in A, f x - g x ∂ξ := by
          refine setLIntegral_congr_fun_ae hA ?_
          filter_upwards [μ.rnDeriv_ne_top ξ, ν.rnDeriv_ne_top ξ] with x hf hg hx
          rw [← ENNReal.toReal_sub_of_le hx hf, Real.eNorm_of_nonneg ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (by finiteness)]
      _ ≤ _ := setLIntegral_tsub_rnDeriv_le_iSup μ ν ξ hA fun x hx ↦ hx
  · calc ∫⁻ x in Aᶜ, ‖(f x).toReal - (g x).toReal‖ₑ ∂ξ = ∫⁻ x in Aᶜ, g x - f x ∂ξ := by
          refine setLIntegral_congr_fun_ae hA.compl ?_
          filter_upwards [μ.rnDeriv_ne_top ξ, ν.rnDeriv_ne_top ξ] with x hf hg hx
          rw [eNorm_sub_rev, ← ENNReal.toReal_sub_of_le (not_le.1 hx).le hg,
            Real.eNorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (by finiteness)]
      _ ≤ _ := setLIntegral_tsub_rnDeriv_le_iSup ν μ ξ hA.compl fun x hx ↦ (not_le.1 hx).le

/-- **Almost everywhere convergence of the densities along a subsequence**: if `μs n` tends to
`ν` in total variation, then for every σ-finite measure `ξ` some subsequence of the densities of
`μs n` with respect to `ξ` converges `ξ`-almost everywhere to the density of `ν`. -/
theorem exists_seq_tendsto_ae_rnDeriv_of_tendsto_etvDist {ξ : Measure 𝓧} [SigmaFinite ξ]
    {μs : ℕ → Measure 𝓧} (h : Filter.Tendsto (fun n ↦ etvDist (μs n) ν) Filter.atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂ξ,
      Filter.Tendsto (fun i ↦ (μs (ns i)).rnDeriv ξ x) Filter.atTop (nhds (ν.rnDeriv ξ x)) := by
  -- eventually, the measures are finite
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (h.eventually (gt_mem_nhds ENNReal.zero_lt_top))
  have hfin (n : ℕ) (hn : N ≤ n) : IsFiniteMeasure (μs n) ∧ IsFiniteMeasure ν :=
    etvDist_lt_top_iff.1 (hN n hn)
  have : IsFiniteMeasure ν := (hfin N le_rfl).2
  -- the real densities converge in `ξ`-measure
  have hmeas : TendstoInMeasure ξ (fun n x ↦ ((μs n).rnDeriv ξ x).toReal) Filter.atTop
      (fun x ↦ (ν.rnDeriv ξ x).toReal) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le)
      fun n ↦ ?_
    rw [eLpNorm_one_eq_lintegral_eNorm (by fun_prop)]
    exact lintegral_eNorm_toReal_rnDeriv_sub_le_etvDist (μs n) ν ξ
  obtain ⟨ns, hns, hns_ae⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hfin_ae : ∀ᵐ x ∂ξ, ∀ n, N ≤ n → (μs n).rnDeriv ξ x ≠ ∞ :=
    ae_all_iff.2 fun n ↦ by
      by_cases hn : N ≤ n
      · have := (hfin n hn).1
        filter_upwards [Measure.rnDeriv_ne_top (μs n) ξ] with x hx _ using hx
      · exact Filter.Eventually.of_forall fun _ hn' ↦ absurd hn' hn
  filter_upwards [hns_ae, hfin_ae, Measure.rnDeriv_ne_top ν ξ] with x hx hxfin hν
  have hlim := ENNReal.tendsto_ofReal hx
  rw [ENNReal.ofReal_toReal hν] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  exact ENNReal.ofReal_toReal (hxfin _ (hi.trans (hns.id_le i)))

end MeasureTheory
