/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.InnerProductSpace.LeastSquares
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Confidence bounds of least squares with a fixed design

Let `x 0, …, x (t - 1)` be a fixed design in a finite-dimensional real inner product space, let
`V_t = ∑_{s < t} x s ⊗ x s` be its Gram operator (`designOp 0 x t`), which may be singular, and
let the responses follow the linear model `Y s = ⟪θ, x s⟫ + η s` with independent σ²-sub-Gaussian
noise `η s`. For every nonzero `v` in the span of the design, the unregularized least-squares
estimate `θ̂_t = V_t⁺ ∑_{s < t} Y s • x s` satisfies [LS, (20.2)]
`P(√(2 σ² ‖v‖²_{V_t⁺} log (1 / δ)) ≤ ⟪v, θ̂_t - θ⟫) ≤ δ` for `δ > 0`,
where `‖v‖²_{V_t⁺} = ⟪v, V_t⁺ v⟫`. Indeed `⟪v, θ̂_t - θ⟫ = ∑_{s < t} ⟪V_t⁺ v, x s⟫ η s` is
sub-Gaussian with variance proxy `σ² ∑_{s < t} ⟪V_t⁺ v, x s⟫² = σ² ‖v‖²_{V_t⁺}`, and the bound is
Hoeffding's inequality. The lower deviations follow by applying it to `-v`.

This is the confidence bound of phased elimination with optimal designs, whose designs need not
span the space: the directions `v` outside the span of the design are not estimated.

## Main statements

* `LMLExplore.hasSubgaussianMGF_inner_leastSquaresEstimate_sub`: `⟪v, θ̂_t - θ⟫` is
  sub-Gaussian with variance proxy `σ² ‖v‖²_{V_t⁺}`.
* `LMLExplore.measureReal_sqrt_le_inner_leastSquaresEstimate_sub_le`: [LS, (20.2)].

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 20.1, equation (20.2).
-/

public section

open MeasureTheory ProbabilityTheory Finset Real
open ContinuousLinearMap (isPositive_zero)
open scoped InnerProductSpace NNReal

namespace LMLExplore

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {x : ℕ → E} {t : ℕ} {η : ℕ → Ω → ℝ} {σ2 : ℝ≥0}

/-- In the linear model `Y s = ⟪θ, x s⟫ + η s` with a fixed design `x` and independent
σ²-sub-Gaussian noise, the error `⟪v, θ̂_t - θ⟫` of the unregularized least-squares estimate in a
direction `v` of the span of the design is sub-Gaussian with variance proxy `σ² ‖v‖²_{V_t⁺}`,
where `V_t = designOp 0 x t`. -/
theorem hasSubgaussianMGF_inner_leastSquaresEstimate_sub (h_indep : iIndepFun η P)
    (h_subG : ∀ s < t, HasSubgaussianMGF (η s) σ2 P) (θ : E) {v : E}
    (hv : v ∈ Submodule.span ℝ (x '' Set.Iio t)) :
    HasSubgaussianMGF
      (fun ω ↦ ⟪v, leastSquaresEstimate 0 x (fun s ↦ ⟪θ, x s⟫_ℝ + η s ω) t - θ⟫_ℝ)
      ((⟪v, (designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v⟫_ℝ).toNNReal * σ2) P := by
  set c : ℕ → ℝ := fun s ↦ ⟪(designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v, x s⟫_ℝ
  have h := HasSubgaussianMGF.sum_of_iIndepFun (s := range t)
    (h_indep.comp (fun s r ↦ c s * r) fun s ↦ measurable_const_mul (c s))
    fun s hs ↦ (h_subG s (mem_range.1 hs)).const_mul (c s)
  convert h.congr (ae_of_all _ fun ω ↦
    (inner_leastSquaresEstimate_sub_eq_sum θ (fun _ ↦ rfl) hv).symm) using 1
  -- the variance proxy `σ² ∑_{s < t} c s ^ 2` is `σ² ‖v‖²_{V_t⁺}`
  have hw := (isPositive_designOp isPositive_zero x t).toLinearMap.moorePenroseInverse
    |>.inner_nonneg_right v
  refine NNReal.eq ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hw, NNReal.coe_sum,
    ← sum_inner_moorePenroseInverse_designOp_sq, sum_mul]
  -- `HasSubgaussianMGF.const_mul` writes its constant `r ^ 2` as an element of the subtype
  -- `{r // 0 ≤ r}`, on which `NNReal.coe_mul` does not fire; its coercion is `r ^ 2 * σ2` by
  -- definition
  rfl

/-- **Fixed-design confidence bound of least squares** [LS, (20.2)]: in the linear model
`Y s = ⟪θ, x s⟫ + η s` with a fixed design `x` and independent σ²-sub-Gaussian noise, `σ² ≠ 0`,
for every nonzero `v` in the span of the design and `δ > 0`, the unregularized least-squares
estimate satisfies `P(√(2 σ² ‖v‖²_{V_t⁺} log (1 / δ)) ≤ ⟪v, θ̂_t - θ⟫) ≤ δ`, where
`V_t = designOp 0 x t` and `‖v‖²_{V_t⁺} = ⟪v, V_t⁺ v⟫`. -/
theorem measureReal_sqrt_le_inner_leastSquaresEstimate_sub_le (h_indep : iIndepFun η P)
    (h_subG : ∀ s < t, HasSubgaussianMGF (η s) σ2 P) (hσ2 : σ2 ≠ 0) (θ : E) {v : E}
    (hv : v ∈ Submodule.span ℝ (x '' Set.Iio t)) (hv0 : v ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | √(2 * σ2 * ⟪v, (designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v⟫_ℝ *
        log (1 / δ)) ≤ ⟪v, leastSquaresEstimate 0 x (fun s ↦ ⟪θ, x s⟫_ℝ + η s ω) t - θ⟫_ℝ} ≤ δ := by
  set w := ⟪v, (designOp 0 x t : E →ₗ[ℝ] E).moorePenroseInverse v⟫_ℝ
  have hw : 0 < w := inner_moorePenroseInverse_designOp_pos hv hv0
  have hc : 0 < 2 * σ2 * w := by positivity
  refine ((hasSubgaussianMGF_inner_leastSquaresEstimate_sub h_indep h_subG θ hv).measure_ge_le
    (sqrt_nonneg _)).trans ?_
  rw [NNReal.coe_mul, Real.coe_toNNReal _ hw.le]
  rcases le_or_gt (log (1 / δ)) 0 with hlog | hlog
  · -- for `δ ≥ 1` the bound `1` of Hoeffding's inequality is at most `δ`
    rw [sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos hc.le hlog)]
    simpa using (div_le_one hδ).1 ((log_nonpos_iff (by positivity)).1 hlog)
  · rw [sq_sqrt (by positivity), show -(2 * σ2 * w * log (1 / δ)) / (2 * (w * σ2)) =
      -log (1 / δ) by field_simp, exp_neg, exp_log (by positivity), one_div, inv_inv]

end LMLExplore
