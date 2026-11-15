/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hölder's inequality for real integrals with exponents summing to one

Mathlib states Hölder's inequality with two exponents `p, q ≥ 0` such that `p + q = 1` for
lower Lebesgue integrals (`ENNReal.lintegral_mul_norm_pow_le`). We record its form for Bochner
integrals of nonnegative integrable real functions. Applied to `f = exp F` and `g = exp G`, it is
the log-convexity of `θ ↦ ∫ exp θ`, hence the convexity of log-partition functions.

## Main statements

* `MeasureTheory.integral_rpow_mul_rpow_le`: for `f, g ≥ 0` integrable and `p, q ≥ 0` with
  `p + q = 1`, `∫ f ^ p * g ^ q ≤ (∫ f) ^ p * (∫ g) ^ q`.
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

end MeasureTheory
