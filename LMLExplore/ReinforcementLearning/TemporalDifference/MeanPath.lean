/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.ProjectedBellman
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Chebyshev

/-!
# Convergence of mean-path temporal-difference learning

Mean-path TD(0) is the deterministic recursion `θ (t + 1) = θ t + α g (θ t)` along the mean-path
TD update `g` of linear temporal-difference learning
(`LMLExplore.ReinforcementLearning.meanTDUpdate`), for a Markov reward process `(P, r)` with an
invariant probability measure `ν`, a discount `γ < 1` and features with `‖φ s‖ ≤ 1`. It is the
expected behaviour of TD(0) with independent observations, and its analysis is the template of
the stochastic analyses.

Let `θ*` be a zero of `g`. The update points towards `θ*`,
`(1 - γ) ‖⟪φ, θ* - θ⟫‖²_ν ≤ ⟪θ* - θ, g θ⟫`, and is bounded by
`‖g θ‖ ≤ (1 + γ) ‖⟪φ, θ* - θ⟫‖_ν` (`one_sub_mul_integral_sq_le_inner_meanTDUpdate`,
`norm_meanTDUpdate_le`). Expanding `‖θ* - θ (t + 1)‖²` with these two bounds shows that each step
of size `(1 - γ) / 4` decreases the squared distance to `θ*` by at least
`(1 - γ)² / 4 ‖⟪φ, θ* - θ t⟫‖²_ν`. Summing gives the `1 / T` rate for the value of the averaged
iterate, and the linear independence `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` of the features gives a linear rate
for the iterates.

## Main statements

* `LMLExplore.ReinforcementLearning.norm_sub_add_smul_meanTDUpdate_sq_le`: one step of size
  `α ≥ 0` decreases `‖θ* - θ‖²` by `α (2 (1 - γ) - α (1 + γ)²) ‖⟪φ, θ* - θ⟫‖²_ν`.
* `LMLExplore.ReinforcementLearning.mul_sum_integral_sq_inner_sub_le`: with step `(1 - γ) / 4`,
  `(1 - γ)² / 4 ∑_{t < T} ‖⟪φ, θ* - θ t⟫‖²_ν ≤ ‖θ* - θ 0‖² - ‖θ* - θ T‖²`.
* `LMLExplore.ReinforcementLearning.integral_sq_inner_sub_average_le`: with step `(1 - γ) / 4`,
  the average `θ_avg` of the first `T` iterates satisfies
  `‖⟪φ, θ* - θ_avg⟫‖²_ν ≤ 4 ‖θ* - θ 0‖² / (T (1 - γ)²)` [BRS18, Theorem 1 (a)].
* `LMLExplore.ReinforcementLearning.norm_sub_sq_le_exp_mul`: with step `(1 - γ) / 4` and
  `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν`, `‖θ* - θ T‖² ≤ exp (-(1 - γ)² ω T / 4) ‖θ* - θ 0‖²`
  [BRS18, Theorem 1 (b)].

## References

* [J. Bhandari, D. Russo and R. Singal, *A finite time analysis of temporal difference learning
  with linear function approximation*, 2018][BRS18], §6.2–6.3
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal InnerProductSpace

namespace LMLExplore.ReinforcementLearning

variable {𝓢 E : Type*} {m𝓢 : MeasurableSpace 𝓢} [Finite 𝓢] [MeasurableSingletonClass 𝓢]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ν : Measure 𝓢} [IsProbabilityMeasure ν] {φ : 𝓢 → E} {P : Kernel 𝓢 𝓢} [IsMarkovKernel P]
  {r : 𝓢 → ℝ} {γ : ℝ≥0} {θ' : E}

/-- **One step of mean-path TD**: if `ν` is invariant, `‖φ s‖ ≤ 1` and `g θ* = 0`, then a step of
size `α ≥ 0` from `θ` satisfies
`‖θ* - (θ + α g θ)‖² ≤ ‖θ* - θ‖² - α (2 (1 - γ) - α (1 + γ)²) ‖⟪φ, θ* - θ⟫‖²_ν`. -/
theorem norm_sub_add_smul_meanTDUpdate_sq_le (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hθ' : meanTDUpdate ν φ P r γ θ' = 0) (θ : E) {α : ℝ} (hα : 0 ≤ α) :
    ‖θ' - (θ + α • meanTDUpdate ν φ P r γ θ)‖ ^ 2 ≤
      ‖θ' - θ‖ ^ 2 - α * (2 * (1 - γ) - α * (1 + γ) ^ 2) * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by
  have h₃ := one_sub_mul_integral_sq_le_inner_meanTDUpdate hP hθ' θ
  have h₄ := norm_meanTDUpdate_le hP hφ hθ' θ
  have hD : 0 ≤ ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  have h₄' : ‖meanTDUpdate ν φ P r γ θ‖ ^ 2 ≤ (1 + γ) ^ 2 * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by
    calc ‖meanTDUpdate ν φ P r γ θ‖ ^ 2
        ≤ ((1 + γ) * √(∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν)) ^ 2 := by gcongr
      _ = (1 + γ) ^ 2 * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by rw [mul_pow, Real.sq_sqrt hD]
  rw [sub_add_eq_sub_sub, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  nlinarith [mul_le_mul_of_nonneg_left h₃ hα, mul_le_mul_of_nonneg_left h₄' (sq_nonneg α)]

/-- One step of mean-path TD with step `(1 - γ) / 4` decreases `‖θ* - θ‖²` by at least
`(1 - γ)² / 4 ‖⟪φ, θ* - θ⟫‖²_ν`. -/
private lemma norm_sub_step_sq_le (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hγ : γ ≤ 1) (hθ' : meanTDUpdate ν φ P r γ θ' = 0) (θ : E) :
    ‖θ' - (θ + ((1 - γ) / 4 : ℝ) • meanTDUpdate ν φ P r γ θ)‖ ^ 2 ≤
      ‖θ' - θ‖ ^ 2 - (1 - γ) ^ 2 / 4 * ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := by
  have hγ₀ : (0 : ℝ) ≤ γ := γ.coe_nonneg
  have hγ₁ : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ
  have hα : (0 : ℝ) ≤ (1 - γ) / 4 := by linarith
  have hD : 0 ≤ ∫ s, ⟪φ s, θ' - θ⟫_ℝ ^ 2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  refine (norm_sub_add_smul_meanTDUpdate_sq_le hP hφ hθ' θ hα).trans ?_
  have hc : (1 - (γ : ℝ)) ^ 2 / 4 ≤
      (1 - (γ : ℝ)) / 4 * (2 * (1 - γ) - (1 - γ) / 4 * (1 + γ) ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hγ₁) (sub_nonneg.2 hγ₁))
      (mul_nonneg (sub_nonneg.2 hγ₁) (by linarith : (0 : ℝ) ≤ 3 + γ))]
  nlinarith [mul_le_mul_of_nonneg_right hc hD]

variable {θ : ℕ → E}

/-- Summing the one-step decrease: with step `(1 - γ) / 4`,
`(1 - γ)² / 4 ∑_{t < T} ‖⟪φ, θ* - θ t⟫‖²_ν ≤ ‖θ* - θ 0‖² - ‖θ* - θ T‖²`. -/
theorem mul_sum_integral_sq_inner_sub_le (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hγ : γ ≤ 1) (hθ' : meanTDUpdate ν φ P r γ θ' = 0)
    (hθ : ∀ t, θ (t + 1) = θ t + ((1 - γ) / 4 : ℝ) • meanTDUpdate ν φ P r γ (θ t)) (T : ℕ) :
    (1 - γ) ^ 2 / 4 * ∑ t ∈ range T, ∫ s, ⟪φ s, θ' - θ t⟫_ℝ ^ 2 ∂ν ≤
      ‖θ' - θ 0‖ ^ 2 - ‖θ' - θ T‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h := norm_sub_step_sq_le hP hφ hγ hθ' (θ T)
    rw [← hθ T] at h
    rw [sum_range_succ, mul_add]
    linarith

/-- **The `1 / T` rate of mean-path TD** [BRS18, Theorem 1 (a)]: if `ν` is invariant, `γ < 1`,
`‖φ s‖ ≤ 1` and `g θ* = 0`, then the average `θ_avg = T⁻¹ ∑_{t < T} θ t` of the first `T ≥ 1`
iterates of mean-path TD with step `(1 - γ) / 4` satisfies
`‖⟪φ, θ* - θ_avg⟫‖²_ν ≤ 4 ‖θ* - θ 0‖² / (T (1 - γ)²)`. -/
theorem integral_sq_inner_sub_average_le (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hγ : γ < 1) (hθ' : meanTDUpdate ν φ P r γ θ' = 0)
    (hθ : ∀ t, θ (t + 1) = θ t + ((1 - γ) / 4 : ℝ) • meanTDUpdate ν φ P r γ (θ t)) {T : ℕ}
    (hT : 0 < T) :
    ∫ s, ⟪φ s, θ' - (T : ℝ)⁻¹ • ∑ t ∈ range T, θ t⟫_ℝ ^ 2 ∂ν ≤
      4 * ‖θ' - θ 0‖ ^ 2 / (T * (1 - γ) ^ 2) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hγ' : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hsum := mul_sum_integral_sq_inner_sub_le hP hφ hγ.le hθ' hθ T
  -- the value of the average is the average of the values
  have havg : ∀ s, ⟪φ s, θ' - (T : ℝ)⁻¹ • ∑ t ∈ range T, θ t⟫_ℝ =
      (T : ℝ)⁻¹ * ∑ t ∈ range T, ⟪φ s, θ' - θ t⟫_ℝ := by
    intro s
    simp only [inner_sub_right, real_inner_smul_right, inner_sum, sum_sub_distrib, sum_const,
      card_range, nsmul_eq_mul]
    field_simp
  -- Jensen's inequality for the average, `(T⁻¹ ∑ a)² ≤ T⁻¹ ∑ a²`
  have hjensen : ∀ s, ((T : ℝ)⁻¹ * ∑ t ∈ range T, ⟪φ s, θ' - θ t⟫_ℝ) ^ 2 ≤
      (T : ℝ)⁻¹ * ∑ t ∈ range T, ⟪φ s, θ' - θ t⟫_ℝ ^ 2 := by
    intro s
    have h := sq_sum_le_card_mul_sum_sq (s := range T) (f := fun t ↦ ⟪φ s, θ' - θ t⟫_ℝ)
    rw [card_range] at h
    rw [mul_pow, inv_pow, sq (T : ℝ), mul_inv, mul_assoc]
    gcongr
    rw [inv_mul_le_iff₀ hT']
    exact h
  calc ∫ s, ⟪φ s, θ' - (T : ℝ)⁻¹ • ∑ t ∈ range T, θ t⟫_ℝ ^ 2 ∂ν
      ≤ ∫ s, (T : ℝ)⁻¹ * ∑ t ∈ range T, ⟪φ s, θ' - θ t⟫_ℝ ^ 2 ∂ν := by
        refine integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ ?_
        simp only [havg]
        exact hjensen s
    _ = (T : ℝ)⁻¹ * ∑ t ∈ range T, ∫ s, ⟪φ s, θ' - θ t⟫_ℝ ^ 2 ∂ν := by
        rw [integral_const_mul, integral_finsetSum _ fun _ _ ↦ Integrable.of_finite]
    _ ≤ 4 * ‖θ' - θ 0‖ ^ 2 / (T * (1 - γ) ^ 2) := by
        rw [inv_mul_le_iff₀ hT', mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖θ' - θ T‖]

/-- **The linear rate of mean-path TD** [BRS18, Theorem 1 (b)]: if `ν` is invariant, `γ ≤ 1`,
`‖φ s‖ ≤ 1`, `g θ* = 0` and `ω ‖θ‖² ≤ ‖⟪φ, θ⟫‖²_ν` for every `θ`, then the iterates of mean-path TD
with step `(1 - γ) / 4` satisfy `‖θ* - θ T‖² ≤ exp (-(1 - γ)² ω T / 4) ‖θ* - θ 0‖²`. -/
theorem norm_sub_sq_le_exp_mul (hP : P.Invariant ν) (hφ : ∀ s, ‖φ s‖ ≤ 1) (hγ : γ ≤ 1)
    (hθ' : meanTDUpdate ν φ P r γ θ' = 0)
    (hθ : ∀ t, θ (t + 1) = θ t + ((1 - γ) / 4 : ℝ) • meanTDUpdate ν φ P r γ (θ t)) {ω : ℝ}
    (hω : ∀ θ, ω * ‖θ‖ ^ 2 ≤ ∫ s, ⟪φ s, θ⟫_ℝ ^ 2 ∂ν) (T : ℕ) :
    ‖θ' - θ T‖ ^ 2 ≤ Real.exp (-((1 - γ) ^ 2 * ω * T / 4)) * ‖θ' - θ 0‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    set c : ℝ := (1 - γ) ^ 2 / 4 with hc
    have hc0 : 0 ≤ c := by positivity
    have h := norm_sub_step_sq_le hP hφ hγ hθ' (θ T)
    rw [← hθ T, ← hc] at h
    have hstep : ‖θ' - θ (T + 1)‖ ^ 2 ≤ Real.exp (-(c * ω)) * ‖θ' - θ T‖ ^ 2 := by
      have hexp := Real.add_one_le_exp (-(c * ω))
      nlinarith [mul_le_mul_of_nonneg_left (hω (θ' - θ T)) hc0,
        mul_le_mul_of_nonneg_right hexp (sq_nonneg ‖θ' - θ T‖)]
    have hsplit : Real.exp (-((1 - γ) ^ 2 * ω * ↑(T + 1) / 4)) =
        Real.exp (-(c * ω)) * Real.exp (-((1 - γ) ^ 2 * ω * T / 4)) := by
      rw [← Real.exp_add, hc]
      push_cast
      ring_nf
    rw [hsplit, mul_assoc]
    exact hstep.trans (mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le)

end LMLExplore.ReinforcementLearning
