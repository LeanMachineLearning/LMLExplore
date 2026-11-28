/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.StrongLaw
import TauCeti.Probability.Independence.InfinitePi
import TauCeti.Probability.StrongLaw

/-!
# The strong law with an infinite mean along the coordinates of an infinite product

Under `Measure.infinitePi (fun _ : ℕ ↦ μ)`, the coordinates are i.i.d. of law `μ`, so Tau Ceti's
strong laws `TauCeti.Probability.strong_law_ae_infinitePi` (finite mean) and
`TauCeti.Probability.strong_law_ae_real_of_lintegral_eq_top` (infinite mean) apply to functions of
them. Combined, they give that the averages of `ψ + χ` along the coordinates tend to `+∞` when `ψ`
is integrable and `χ` has a positive part of infinite mean and a negative part of finite mean.

The file also complements Mathlib's truncations `ProbabilityTheory.truncation f A`, which zero
out the values of `f` outside `(-A, A]` in the proof of the strong law: an integrable function is
the limit of its truncations in `L¹`.

## Main statements

* `ProbabilityTheory.ae_tendsto_average_add_atTop_infinitePi`: if `ψ` is integrable and `χ` is
  measurable, with a negative part of finite mean and a positive part of infinite mean, then
  almost surely the averages of `ψ (x i) + χ (x i)` tend to `+∞`.
* `ProbabilityTheory.tendsto_integral_abs_sub_truncation`: for an integrable `f`,
  `∫ |f - truncation f A| → 0` as `A → ∞`.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

/-- **The strong law of large numbers with an infinite mean along the coordinates of `μ^ℕ`.** If
`ψ` is integrable, and `χ` has a negative part of finite mean and a positive part of infinite mean,
the averages of `ψ + χ` along the coordinates tend to `+∞` almost surely. -/
theorem ae_tendsto_average_add_atTop_infinitePi {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {ψ χ : α → ℝ} (hψ : Integrable ψ μ) (hχ : Measurable χ)
    (hneg : ∫⁻ e, ENNReal.ofReal (-χ e) ∂μ ≠ ⊤) (hpos : ∫⁻ e, ENNReal.ofReal (χ e) ∂μ = ⊤) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ ↦ μ),
      Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, (ψ (x i) + χ (x i))) atTop
        atTop := by
  have h0 := measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0
  filter_upwards [TauCeti.Probability.strong_law_ae_infinitePi μ hψ,
    TauCeti.Probability.strong_law_ae_real_of_lintegral_eq_top
      (fun i (x : ℕ → α) ↦ χ (x i))
      (fun i j hij ↦ ((TauCeti.Probability.iIndepFun_eval_infinitePi _).comp (fun _ ↦ χ)
        (fun _ ↦ hχ)).indepFun hij)
      (fun i ↦ (μ.identDistrib_eval_infinitePi i 0).comp hχ)
      (by simpa only [h0.lintegral_comp (f := fun e ↦ ENNReal.ofReal (-χ e)) (by fun_prop)]
        using hneg)
      (by simpa only [h0.lintegral_comp (f := fun e ↦ ENNReal.ofReal (χ e)) (by fun_prop)]
        using hpos)] with x hψx hχx
  simp_rw [smul_eq_mul] at hψx
  simp_rw [Finset.sum_add_distrib, mul_add]
  exact hψx.add_atTop (by simpa only [div_eq_inv_mul] using hχx)

/-- The truncations of an integrable function tend to it in `L¹`: `∫ |f - truncation f A| → 0`
as `A → ∞`, by dominated convergence (compare `tendsto_integral_truncation`). -/
theorem tendsto_integral_abs_sub_truncation {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    Tendsto (fun A ↦ ∫ x, |f x - truncation f A x| ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (l := atTop) (μ := μ)
    (F := fun A x ↦ |f x - truncation f A x|) (f := fun _ ↦ 0) (fun x ↦ 2 * |f x|)
    (Eventually.of_forall fun A ↦ (hf.aestronglyMeasurable.sub
      hf.aestronglyMeasurable.truncation).norm)
    (Eventually.of_forall fun A ↦ ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_abs, two_mul]
      exact (abs_sub _ _).trans (add_le_add_right (abs_truncation_le_abs_self f A x) _))
    (hf.abs.const_mul 2) (ae_of_all _ fun x ↦ tendsto_const_nhds.congr'
      ((eventually_gt_atTop |f x|).mono fun A hA ↦ by simp [truncation_eq_self hA]))
  simpa using h

end ProbabilityTheory
