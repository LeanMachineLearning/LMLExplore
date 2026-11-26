/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import LMLExplore.MeasureTheory.Measure.WithDensity

/-!
# Hölder's inequality with exponents summing to one

Mathlib states Hölder's inequality with two exponents `p, q ≥ 0` such that `p + q = 1` for
lower Lebesgue integrals (`ENNReal.lintegral_mul_norm_pow_le`). We record its form for Bochner
integrals of nonnegative integrable real functions. Applied to `f = exp F` and `g = exp G`, it is
the log-convexity of `θ ↦ ∫ exp θ`, hence the convexity of log-partition functions.

Mathlib's form with finitely many exponents (`ENNReal.lintegral_prod_norm_pow_le`) bounds the
integrals against a geometric mixture `μ.withDensity (∏ i ∈ s, f i ^ w i)` of measures with
densities, for weights `w i ≥ 0` summing to one, by the weighted geometric mean of the integrals
against the measures `μ.withDensity (f i)`. In particular a geometric mixture of finite measures
is finite. These two lemmas are extracted from the proof of
`EValuesResearch.mem_iidSaturation_withDensity_prod_rpow` in
`EValuesResearch/Results/Saturation.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`.

## Main statements

* `MeasureTheory.integral_rpow_mul_rpow_le`: for `f, g ≥ 0` integrable and `p, q ≥ 0` with
  `p + q = 1`, `∫ f ^ p * g ^ q ≤ (∫ f) ^ p * (∫ g) ^ q`.
* `MeasureTheory.lintegral_withDensity_prod_rpow_le`: Hölder's inequality for geometric mixtures
  of measures,
  `∫⁻ g ∂μ.withDensity (∏ i ∈ s, f i ^ w i) ≤ ∏ i ∈ s, (∫⁻ g ∂μ.withDensity (f i)) ^ w i`.
* `MeasureTheory.isFiniteMeasure_withDensity_prod_rpow`: a geometric mixture of finite measures is
  finite.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- **Hölder's inequality** for nonnegative integrable real functions, with two exponents `p, q ≥ 0`
such that `p + q = 1`: `∫ f ^ p * g ^ q ≤ (∫ f) ^ p * (∫ g) ^ q`. -/
lemma integral_rpow_mul_rpow_le {f g : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf : Integrable f μ) (hg : Integrable g μ) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p + q = 1) :
    ∫ x, f x ^ p * g x ^ q ∂μ ≤ (∫ x, f x ∂μ) ^ p * (∫ x, g x ∂μ) ^ q := by
  have h_holder := ENNReal.lintegral_mul_norm_pow_le hf.1.aemeasurable.ennreal_ofReal
    hg.1.aemeasurable.ennreal_ofReal hp hq hpq
  have h_meas : AEStronglyMeasurable (fun x ↦ f x ^ p * g x ^ q) μ :=
    ((hf.1.aemeasurable.pow_const p).mul (hg.1.aemeasurable.pow_const q)).aestronglyMeasurable
  have h_nonneg : 0 ≤ᵐ[μ] fun x ↦ f x ^ p * g x ^ q := by
    filter_upwards [hf_nonneg, hg_nonneg] with x hfx hgx
    exact mul_nonneg (Real.rpow_nonneg hfx p) (Real.rpow_nonneg hgx q)
  rw [integral_eq_lintegral_of_nonneg_ae h_nonneg h_meas,
    integral_eq_lintegral_of_nonneg_ae hf_nonneg hf.1,
    integral_eq_lintegral_of_nonneg_ae hg_nonneg hg.1, ENNReal.toReal_rpow, ENNReal.toReal_rpow,
    ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono ?_ ((lintegral_congr_ae ?_).trans_le h_holder)
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp hf.lintegral_lt_top.ne)
      (ENNReal.rpow_ne_top_of_nonneg hq hg.lintegral_lt_top.ne)
  · filter_upwards [hf_nonneg, hg_nonneg] with x hfx hgx
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hfx p), ENNReal.ofReal_rpow_of_nonneg hfx hp,
      ENNReal.ofReal_rpow_of_nonneg hgx hq]

/-- **Hölder's inequality for geometric mixtures of measures.** For weights `w i ≥ 0` summing to
one over `s`, the integral of `g` against the measure with density `∏ i ∈ s, f i ^ w i` with
respect to `μ` is at most the weighted geometric mean `∏ i ∈ s, (∫⁻ g ∂μ.withDensity (f i)) ^ w i`
of its integrals against the measures with densities `f i`. This is
`ENNReal.lintegral_prod_norm_pow_le` for the measure `μ.withDensity g`. -/
theorem lintegral_withDensity_prod_rpow_le {ι : Type*} (s : Finset ι) {f : ι → α → ℝ≥0∞}
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) {w : ι → ℝ} (hw : ∑ i ∈ s, w i = 1)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ x, g x ∂μ.withDensity (fun x ↦ ∏ i ∈ s, f i x ^ w i) ≤
      ∏ i ∈ s, (∫⁻ x, g x ∂μ.withDensity (f i)) ^ w i := by
  rw [lintegral_withDensity_comm hg
    (Finset.aemeasurable_fun_prod _ fun i hi ↦ (hf i hi).pow_const _)]
  refine (ENNReal.lintegral_prod_norm_pow_le s
    (fun i hi ↦ (hf i hi).mono_ac (withDensity_absolutelyContinuous μ g)) hw hw0).trans_eq ?_
  exact Finset.prod_congr rfl fun i hi ↦ by rw [lintegral_withDensity_comm (hf i hi) hg]

/-- A geometric mixture of finite measures is finite: for weights `w i ≥ 0` summing to one over
`s`, if the measures `μ.withDensity (f i)`, `i ∈ s`, are finite, so is
`μ.withDensity (∏ i ∈ s, f i ^ w i)`, by Hölder's inequality. -/
theorem isFiniteMeasure_withDensity_prod_rpow {ι : Type*} (s : Finset ι) {f : ι → α → ℝ≥0∞}
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) {w : ι → ℝ} (hw : ∑ i ∈ s, w i = 1)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hfin : ∀ i ∈ s, IsFiniteMeasure (μ.withDensity (f i))) :
    IsFiniteMeasure (μ.withDensity fun x ↦ ∏ i ∈ s, f i x ^ w i) := by
  refine ⟨?_⟩
  have h := lintegral_withDensity_prod_rpow_le s hf hw hw0 aemeasurable_const (g := 1)
  simp only [Pi.one_apply, lintegral_one] at h
  refine h.trans_lt (ENNReal.prod_lt_top fun i hi ↦ ?_)
  have := hfin i hi
  exact ENNReal.rpow_lt_top_of_nonneg (hw0 i hi) (measure_ne_top _ _)

end MeasureTheory
