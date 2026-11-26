/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.InnerProductSpace.EllipticalPotential
public import LMLExplore.Analysis.InnerProductSpace.Ridge
public import LMLExplore.OnlineLearning.Learner.Basic

/-!
# The Vovk–Azoury–Warmuth forecaster

In online linear regression with the square loss on a real inner product space `E`, at each round
`t` a feature `z t ∈ E` is revealed, the learner plays `x t ∈ E`, then the label `y t ∈ ℝ` is
revealed and the learner pays `(⟪z t, x t⟫ - y t) ^ 2 / 2`. The **Vovk–Azoury–Warmuth forecaster**
[Ora, Algorithm 7.7] uses the feature of the current round: for a positive definite operator `V₀`,
it plays

  `x t = S_t⁻¹ ∑ s < t, y s • z s`, with `S_t = V₀ + ∑ s ≤ t, z s ⊗ z s = designOp V₀ z (t + 1)`,

the minimizer of the regularized cumulative loss of the past rounds plus the square loss of the
current feature with the label `0`,
`⟪V₀ w, w⟫ / 2 + ∑ s < t, (⟪z s, w⟫ - y s) ^ 2 / 2 + ⟪z t, w⟫ ^ 2 / 2`. For `V₀ = λ • 1` it is
the ridge estimate of the first `t + 1` observations with the label of round `t` replaced by `0`.

Its regret against every `u ∈ E`, with no bound on `u`, on the plays or on the features, is
[Ora, Theorem 7.44]

  `∑ t < n, (⟪z t, x t⟫ - y t) ^ 2 / 2 - ∑ t < n, (⟪z t, u⟫ - y t) ^ 2 / 2 ≤`
  `  ⟪V₀ u, u⟫ / 2 + ∑ t < n, y t ^ 2 ‖z t‖²_{S_t⁻¹} / 2`.

The weighted norms are those of the log-determinant lemma, so for labels `|y t| ≤ Y` the last sum
is at most `Y ^ 2 / 2 * log (det S_{n-1} / det V₀)`, and for `V₀ = λ • 1` and features
`‖z t‖ ≤ R` in dimension `d` the regret is at most
`λ / 2 * ‖u‖ ^ 2 + d Y ^ 2 / 2 * log (1 + n R ^ 2 / (λ d))`: logarithmic in `n`, although the
square losses are neither strongly convex nor exp-concave on `E`.

## Main definitions

* `LMLExplore.OnlineLearning.vovkAzouryWarmuth V₀ z y t`: the play `x t` of the forecaster.
* `LMLExplore.OnlineLearning.OnlineLearner.vovkAzouryWarmuth V₀`: the forecaster as an online
  learner, with the features as contexts and the labels as feedback.

## Main statements

* `isMinOn_vovkAzouryWarmuth`: the play minimizes the regularized cumulative loss with the
  current feature and the label `0` [Ora, Algorithm 7.7].
* `vovkAzouryWarmuth_smul_one_eq_ridgeEstimate`: for `V₀ = λ • 1`, the play is a ridge estimate.
* `regret_vovkAzouryWarmuth_le`: [Ora, Section 7.11] the regret through the weighted norms
  `‖z t‖²_{S_t⁻¹}`.
* `regret_vovkAzouryWarmuth_le_log_det`: its log-determinant form [Ora, Lemma 7.29].
* `regret_vovkAzouryWarmuth_le_log_one_add`: [Ora, Theorem 7.44] the logarithmic regret for
  `V₀ = λ • 1`, bounded features and bounded labels.
* `OnlineLearner.run_vovkAzouryWarmuth`: the runs of the learner are the plays of the forecaster.

## Implementation notes

[Ora] proves the regret bound through FTRL on the linear losses `w ↦ -y t * ⟪z t, w⟫` with the
regularizers `⟪S_t w, w⟫ / 2`. Here the same stability argument is run directly on the regularized
cumulative losses `L_t w = ⟪V₀ w, w⟫ / 2 + ∑ s < t, (⟪z s, w⟫ - y s) ^ 2 / 2`: for every `w`,
`L_t (x t) + (⟪z t, x t⟫ - y t) ^ 2 / 2 - L_{t+1} w ≤ y t ^ 2 ‖z t‖²_{S_t⁻¹} / 2`, and these
inequalities telescope, ending at the comparator.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Section 7.11, Algorithm 7.7, Theorem 7.44.
* K. S. Azoury and M. K. Warmuth, *Relative loss bounds for on-line density estimation with the
  exponential family of distributions*, Machine Learning 43 (2001).
* V. Vovk, *Competitive on-line statistics*, International Statistical Review 69 (2001).
-/
public section

open Finset Real
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V₀ : E →L[ℝ] E}

/-- The play of round `t` of the **Vovk–Azoury–Warmuth forecaster** [Ora, Algorithm 7.7] with the
regularizer `V₀`, on the features `z` and the labels `y`:
`x t = S_t⁻¹ ∑ s < t, y s • z s`, where `S_t = designOp V₀ z (t + 1) = V₀ + ∑ s ≤ t, z s ⊗ z s`
includes the feature `z t` of the current round. -/
noncomputable def vovkAzouryWarmuth (V₀ : E →L[ℝ] E) (z : ℕ → E) (y : ℕ → ℝ) (t : ℕ) : E :=
  Ring.inverse (designOp V₀ z (t + 1)) (∑ s ∈ range t, y s • z s)

/-- The defining equation of `vovkAzouryWarmuth`. -/
theorem vovkAzouryWarmuth_def (V₀ : E →L[ℝ] E) (z : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    vovkAzouryWarmuth V₀ z y t =
      Ring.inverse (designOp V₀ z (t + 1)) (∑ s ∈ range t, y s • z s) :=
  (rfl)

/-- The first play of the Vovk–Azoury–Warmuth forecaster is `0`. -/
@[simp]
theorem vovkAzouryWarmuth_zero (V₀ : E →L[ℝ] E) (z : ℕ → E) (y : ℕ → ℝ) :
    vovkAzouryWarmuth V₀ z y 0 = 0 := by
  simp [vovkAzouryWarmuth_def]

/-- **Causality** of the Vovk–Azoury–Warmuth forecaster: its play of round `t` depends only on the
features `z s` for `s ≤ t` and on the labels `y s` for `s < t`. -/
theorem vovkAzouryWarmuth_congr {z z' : ℕ → E} {y y' : ℕ → ℝ} {t : ℕ} (hz : ∀ s ≤ t, z s = z' s)
    (hy : ∀ s < t, y s = y' s) :
    vovkAzouryWarmuth V₀ z y t = vovkAzouryWarmuth V₀ z' y' t := by
  rw [vovkAzouryWarmuth_def, vovkAzouryWarmuth_def,
    designOp_congr fun s hs ↦ hz s (Nat.lt_succ_iff.mp hs),
    sum_congr rfl fun s hs ↦ by rw [hz s (mem_range.1 hs).le, hy s (mem_range.1 hs)]]

/-- The **normal equations** of the Vovk–Azoury–Warmuth forecaster: for a positive definite `V₀`,
`S_t (x t) = ∑ s < t, y s • z s`, with `S_t = designOp V₀ z (t + 1)`. -/
theorem designOp_vovkAzouryWarmuth (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (z : ℕ → E)
    (y : ℕ → ℝ) (t : ℕ) :
    designOp V₀ z (t + 1) (vovkAzouryWarmuth V₀ z y t) = ∑ s ∈ range t, y s • z s :=
  ContinuousLinearMap.apply_ringInverse_apply (isUnit_designOp hV₀ hV₀u z (t + 1)) _

/-- **The Vovk–Azoury–Warmuth forecaster hallucinates the label `0`** [Ora, Section 7.11]: with
the regularizer `λ • 1`, its play of round `t` is the ridge estimate of the first `t + 1`
observations, with the label of round `t` replaced by `0`. -/
theorem vovkAzouryWarmuth_smul_one_eq_ridgeEstimate (lam : ℝ) (z : ℕ → E) (y : ℕ → ℝ) (t : ℕ) :
    vovkAzouryWarmuth (lam • 1) z y t = ridgeEstimate lam z (Function.update y t 0) (t + 1) := by
  rw [vovkAzouryWarmuth_def, ridgeEstimate_def, sum_range_succ, Function.update_self, zero_smul,
    add_zero]
  congr 1
  exact sum_congr rfl fun s hs ↦ by rw [Function.update_of_ne (mem_range.1 hs).ne]

/-- The objective of the Vovk–Azoury–Warmuth forecaster at round `t` is a quadratic function with
Hessian `S_t = designOp V₀ z (t + 1)`:
`⟪V₀ w, w⟫ / 2 + ∑ s < t, (⟪z s, w⟫ - y s) ^ 2 / 2 + ⟪z t, w⟫ ^ 2 / 2 =
  ⟪w, S_t w⟫ / 2 - ⟪∑ s < t, y s • z s, w⟫ + ∑ s < t, y s ^ 2 / 2`. -/
private lemma vovkAzouryWarmuth_objective_eq (z : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (w : E) :
    ⟪V₀ w, w⟫ / 2 + ∑ s ∈ range t, (⟪z s, w⟫ - y s) ^ 2 / 2 + ⟪z t, w⟫ ^ 2 / 2 =
      ⟪w, designOp V₀ z (t + 1) w⟫ / 2 - ⟪∑ s ∈ range t, y s • z s, w⟫ +
        ∑ s ∈ range t, y s ^ 2 / 2 := by
  have h : ∑ s ∈ range t, (⟪z s, w⟫ - y s) ^ 2 / 2 = (∑ s ∈ range t, ⟪z s, w⟫ ^ 2) / 2 -
      ∑ s ∈ range t, y s * ⟪z s, w⟫ + ∑ s ∈ range t, y s ^ 2 / 2 := by
    rw [sum_div, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun s _ ↦ by ring
  rw [inner_designOp_apply_self, sum_range_succ, sum_inner, real_inner_comm w (V₀ w), h]
  simp only [real_inner_smul_left]
  ring

/-- Around its play `x t`, the objective of the Vovk–Azoury–Warmuth forecaster at round `t` is
`F t w = F t (x t) + ⟪w - x t, S_t (w - x t)⟫ / 2`, with `S_t = designOp V₀ z (t + 1)`. -/
private lemma vovkAzouryWarmuth_objective_eq_add (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀)
    (z : ℕ → E) (y : ℕ → ℝ) (t : ℕ) (w : E) :
    ⟪V₀ w, w⟫ / 2 + ∑ s ∈ range t, (⟪z s, w⟫ - y s) ^ 2 / 2 + ⟪z t, w⟫ ^ 2 / 2 =
      ⟪V₀ (vovkAzouryWarmuth V₀ z y t), vovkAzouryWarmuth V₀ z y t⟫ / 2 +
        ∑ s ∈ range t, (⟪z s, vovkAzouryWarmuth V₀ z y t⟫ - y s) ^ 2 / 2 +
        ⟪z t, vovkAzouryWarmuth V₀ z y t⟫ ^ 2 / 2 +
        ⟪w - vovkAzouryWarmuth V₀ z y t,
          designOp V₀ z (t + 1) (w - vovkAzouryWarmuth V₀ z y t)⟫ / 2 := by
  set x := vovkAzouryWarmuth V₀ z y t
  set S := designOp V₀ z (t + 1)
  have hS : S x = ∑ s ∈ range t, y s • z s := designOp_vovkAzouryWarmuth hV₀ hV₀u z y t
  -- expand the quadratic form of `S` around `x`, by its symmetry
  have h_symm : ⟪x, S w⟫ = ⟪S x, w⟫ :=
    ((isPositive_designOp hV₀ z (t + 1)).inner_left_eq_inner_right x w).symm
  have h_exp : ⟪w - x, S (w - x)⟫ = ⟪w, S w⟫ - 2 * ⟪S x, w⟫ + ⟪x, S x⟫ := by
    simp only [map_sub, inner_sub_left, inner_sub_right, h_symm, real_inner_comm w (S x)]
    ring
  rw [vovkAzouryWarmuth_objective_eq z y t w, vovkAzouryWarmuth_objective_eq z y t x, h_exp, ← hS,
    real_inner_comm x (S x)]
  ring

/-- **The Vovk–Azoury–Warmuth forecaster is FTRL with the current feature** [Ora, Algorithm 7.7]:
for a positive definite `V₀`, its play of round `t` minimizes over `E` the regularized cumulative
loss of the rounds `s < t` plus the square loss of the current feature `z t` with the label `0`,
`⟪V₀ w, w⟫ / 2 + ∑ s < t, (⟪z s, w⟫ - y s) ^ 2 / 2 + ⟪z t, w⟫ ^ 2 / 2`. -/
theorem isMinOn_vovkAzouryWarmuth (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (z : ℕ → E)
    (y : ℕ → ℝ) (t : ℕ) :
    IsMinOn (fun w ↦ ⟪V₀ w, w⟫ / 2 + ∑ s ∈ range t, (⟪z s, w⟫ - y s) ^ 2 / 2 + ⟪z t, w⟫ ^ 2 / 2)
      Set.univ (vovkAzouryWarmuth V₀ z y t) := by
  refine isMinOn_univ_iff.2 fun w ↦ ?_
  rw [vovkAzouryWarmuth_objective_eq_add hV₀ hV₀u z y t w]
  have h := (isPositive_designOp hV₀ z (t + 1)).inner_nonneg_right (w - vovkAzouryWarmuth V₀ z y t)
  linarith

/-- **Stability of the Vovk–Azoury–Warmuth forecaster.** For the regularized cumulative losses
`L t w = ⟪V₀ w, w⟫ / 2 + ∑ s < t, (⟪z s, w⟫ - y s) ^ 2 / 2` and every `w`, the play `x t` satisfies
`L t (x t) + (⟪z t, x t⟫ - y t) ^ 2 / 2 - L (t + 1) w ≤ y t ^ 2 ‖z t‖²_{S_t⁻¹} / 2`. -/
private lemma vovkAzouryWarmuth_stability (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (z : ℕ → E)
    (y : ℕ → ℝ) (t : ℕ) (w : E) :
    ⟪V₀ (vovkAzouryWarmuth V₀ z y t), vovkAzouryWarmuth V₀ z y t⟫ / 2 +
        ∑ s ∈ range t, (⟪z s, vovkAzouryWarmuth V₀ z y t⟫ - y s) ^ 2 / 2 +
        (⟪z t, vovkAzouryWarmuth V₀ z y t⟫ - y t) ^ 2 / 2 -
      (⟪V₀ w, w⟫ / 2 + ∑ s ∈ range (t + 1), (⟪z s, w⟫ - y s) ^ 2 / 2) ≤
      y t ^ 2 * ⟪z t, Ring.inverse (designOp V₀ z (t + 1)) (z t)⟫ / 2 := by
  set x := vovkAzouryWarmuth V₀ z y t
  set S := designOp V₀ z (t + 1)
  have hS := isPositive_designOp hV₀ z (t + 1)
  have h_eq := vovkAzouryWarmuth_objective_eq_add hV₀ hV₀u z y t w
  -- the linear term `y t ⟪z t, w - x⟫` is dominated by the quadratic form of `S` and the weighted
  -- norm of `z t`: `y t ⟪z t, d⟫ ≤ ⟪d, S d⟫ / 2 + y t ^ 2 ‖z t‖²_{S⁻¹} / 2`
  have h_cs := hS.abs_inner_le_sqrt_mul_sqrt_ringInverse (isUnit_designOp hV₀ hV₀u z (t + 1))
    (w - x) (z t)
  have ha := hS.inner_nonneg_right (w - x)
  have hb := hS.ringInverse.inner_nonneg_right (z t)
  have h_lin : y t * ⟪z t, w - x⟫ ≤ ⟪w - x, S (w - x)⟫ / 2 +
      y t ^ 2 * ⟪z t, Ring.inverse S (z t)⟫ / 2 := by
    have h1 : y t * ⟪z t, w - x⟫ ≤
        |y t| * (√⟪w - x, S (w - x)⟫ * √⟪z t, Ring.inverse S (z t)⟫) := by
      rw [real_inner_comm]
      calc _ ≤ |y t * ⟪w - x, z t⟫| := le_abs_self _
        _ = _ := by rw [abs_mul]
        _ ≤ _ := by gcongr
    nlinarith [sq_nonneg (√⟪w - x, S (w - x)⟫ - |y t| * √⟪z t, Ring.inverse S (z t)⟫),
      sq_sqrt ha, sq_sqrt hb, sq_abs (y t)]
  rw [sum_range_succ, inner_sub_right] at *
  nlinarith

/-- **The regret of the Vovk–Azoury–Warmuth forecaster** [Ora, Section 7.11]. For a positive
definite `V₀` (positive and invertible), any features `z`, labels `y` and comparator `u ∈ E`,
the regret of the forecaster for the square losses `(⟪z t, ·⟫ - y t) ^ 2 / 2` is
`regret ≤ ⟪V₀ u, u⟫ / 2 + ∑ t < n, y t ^ 2 ‖z t‖²_{S_t⁻¹} / 2`, for the design operators
`S_t = designOp V₀ z (t + 1) = V₀ + ∑ s ≤ t, z s ⊗ z s`. -/
theorem regret_vovkAzouryWarmuth_le (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (z : ℕ → E)
    (y : ℕ → ℝ) (u : E) (n : ℕ) :
    regret (fun t w ↦ (⟪z t, w⟫ - y t) ^ 2 / 2) (vovkAzouryWarmuth V₀ z y) u n ≤
      ⟪V₀ u, u⟫ / 2 +
        ∑ t ∈ range n, y t ^ 2 * ⟪z t, Ring.inverse (designOp V₀ z (t + 1)) (z t)⟫ / 2 := by
  -- the cumulative loss of the plays exceeds the regularized cumulative loss of any point by at
  -- most the sum of the stability terms, by induction on the horizon
  have key (m : ℕ) (w : E) :
      ∑ t ∈ range m, (⟪z t, vovkAzouryWarmuth V₀ z y t⟫ - y t) ^ 2 / 2 -
          (⟪V₀ w, w⟫ / 2 + ∑ t ∈ range m, (⟪z t, w⟫ - y t) ^ 2 / 2) ≤
        ∑ t ∈ range m, y t ^ 2 * ⟪z t, Ring.inverse (designOp V₀ z (t + 1)) (z t)⟫ / 2 := by
    induction m generalizing w with
    | zero =>
      have h := hV₀.inner_nonneg_left w
      simp only [range_zero, sum_empty]
      linarith
    | succ m ih =>
      have h_ih := ih (vovkAzouryWarmuth V₀ z y m)
      have h_step := vovkAzouryWarmuth_stability hV₀ hV₀u z y m w
      rw [sum_range_succ (fun t ↦ (⟪z t, vovkAzouryWarmuth V₀ z y t⟫ - y t) ^ 2 / 2),
        sum_range_succ (fun t ↦ y t ^ 2 * ⟪z t, Ring.inverse (designOp V₀ z (t + 1)) (z t)⟫ / 2)]
      linarith
  rw [regret_eq_sum_sub_sum]
  linarith [key n u]

/-- **The regret of the Vovk–Azoury–Warmuth forecaster, log-determinant form**
[Ora, Section 7.11, Lemma 7.29]. In finite dimension, for a positive definite `V₀` and labels
`|y t| ≤ Y`,
`regret ≤ ⟪V₀ u, u⟫ / 2 + Y ^ 2 / 2 * log (det S_{n-1} / det V₀)`, where
`S_{n-1} = designOp V₀ z n = V₀ + ∑ t < n, z t ⊗ z t`. -/
theorem regret_vovkAzouryWarmuth_le_log_det [FiniteDimensional ℝ E] (hV₀ : V₀.IsPositive)
    (hV₀u : IsUnit V₀) (z : ℕ → E) (y : ℕ → ℝ) (u : E) {n : ℕ} {Y : ℝ}
    (hy : ∀ t < n, |y t| ≤ Y) :
    regret (fun t w ↦ (⟪z t, w⟫ - y t) ^ 2 / 2) (vovkAzouryWarmuth V₀ z y) u n ≤
      ⟪V₀ u, u⟫ / 2 + Y ^ 2 / 2 *
        log (LinearMap.det (designOp V₀ z n : E →ₗ[ℝ] E) / LinearMap.det (V₀ : E →ₗ[ℝ] E)) := by
  refine (regret_vovkAzouryWarmuth_le hV₀ hV₀u z y u n).trans ?_
  have h_log := sum_inner_ringInverse_designOp_succ_le_log_det hV₀ hV₀u z n
  gcongr
  calc ∑ t ∈ range n, y t ^ 2 * ⟪z t, Ring.inverse (designOp V₀ z (t + 1)) (z t)⟫ / 2
      ≤ ∑ t ∈ range n, Y ^ 2 / 2 * ⟪z t, Ring.inverse (designOp V₀ z (t + 1)) (z t)⟫ := by
        refine sum_le_sum fun t ht ↦ ?_
        have hb := (isPositive_designOp hV₀ z (t + 1)).ringInverse.inner_nonneg_right (z t)
        have hyY : y t ^ 2 ≤ Y ^ 2 := sq_le_sq.mpr ((hy t (mem_range.1 ht)).trans (le_abs_self Y))
        nlinarith
    _ ≤ _ := by
        rw [← mul_sum]
        gcongr

/-- **Logarithmic regret of the Vovk–Azoury–Warmuth forecaster** [Ora, Theorem 7.44]. With the
regularizer `λ • 1`, `λ > 0`, in dimension `d`, for features `‖z t‖ ≤ R` and labels `|y t| ≤ Y`,
the regret against every `u ∈ E` is
`regret ≤ λ / 2 * ‖u‖ ^ 2 + d Y ^ 2 / 2 * log (1 + n R ^ 2 / (λ d))`. -/
theorem regret_vovkAzouryWarmuth_le_log_one_add [FiniteDimensional ℝ E] {lam R Y : ℝ}
    (hlam : 0 < lam) (z : ℕ → E) (y : ℕ → ℝ) (u : E) {n : ℕ} (hz : ∀ t < n, ‖z t‖ ≤ R)
    (hy : ∀ t < n, |y t| ≤ Y) :
    regret (fun t w ↦ (⟪z t, w⟫ - y t) ^ 2 / 2) (vovkAzouryWarmuth (lam • 1) z y) u n ≤
      lam / 2 * ‖u‖ ^ 2 + Module.finrank ℝ E * Y ^ 2 / 2 *
        log (1 + n * R ^ 2 / (lam * Module.finrank ℝ E)) := by
  have h := regret_vovkAzouryWarmuth_le_log_det (ContinuousLinearMap.isPositive_smul_one hlam.le)
    (ContinuousLinearMap.isUnit_smul_one hlam.ne') z y u hy
  rw [ContinuousLinearMap.det_smul_one] at h
  refine h.trans ?_
  have h_det := log_det_designOp_div_pow_le hlam z hz
  have h_reg : ⟪(lam • 1 : E →L[ℝ] E) u, u⟫ / 2 = lam / 2 * ‖u‖ ^ 2 := by
    simp only [smul_apply, one_apply_eq_self, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  rw [h_reg]
  nlinarith [mul_le_mul_of_nonneg_left h_det (by positivity : (0 : ℝ) ≤ Y ^ 2 / 2)]

namespace OnlineLearner

/-- The **Vovk–Azoury–Warmuth forecaster as an online learner** with the regularizer `V₀`: the
context of each round is its feature, revealed before the play, and the feedback is its label. Its
runs are the plays `vovkAzouryWarmuth V₀ z y` (`run_vovkAzouryWarmuth`), to which the regret
bounds apply. -/
noncomputable def vovkAzouryWarmuth (V₀ : E →L[ℝ] E) : OnlineLearner E ℝ E where
  play t h c := OnlineLearning.vovkAzouryWarmuth V₀
    (fun s ↦ if hs : s < t then (h ⟨s, hs⟩).1 else c)
    (fun s ↦ if hs : s < t then (h ⟨s, hs⟩).2 else 0) t

/-- The runs of the Vovk–Azoury–Warmuth learner against the features `z` and the labels `y` are
the plays of the Vovk–Azoury–Warmuth forecaster. -/
@[simp]
theorem run_vovkAzouryWarmuth (V₀ : E →L[ℝ] E) (z : ℕ → E) (y : ℕ → ℝ) :
    (vovkAzouryWarmuth V₀).run z y = OnlineLearning.vovkAzouryWarmuth V₀ z y := by
  funext t
  rw [run_def]
  refine vovkAzouryWarmuth_congr (fun s hs ↦ ?_) fun s hs ↦ by simp [hs]
  rcases hs.lt_or_eq with hs | rfl
  · simp [hs]
  · simp

end OnlineLearner

end LMLExplore.OnlineLearning
