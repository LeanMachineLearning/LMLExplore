/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.Synchronous
import LMLExplore.Analysis.Real.Sqrt
import LMLExplore.Analysis.SpecialFunctions.Exp
import LMLExplore.ReinforcementLearning.QLearning.LowerBound
import LMLExplore.ReinforcementLearning.QLearning.UpperBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The sample complexity of synchronous Q-learning and TD learning

Synchronous Q-learning (`LMLExplore.ReinforcementLearning.syncQLearning`) on the generative model,
with rewards in `[0, 1]`, an initial value in `[0, 1 / (1 - γ)]`, `T ≥ 2` iterations and learning
rates in a rescaled linear window

`1 / (1 + (1 - γ) T / κ) ≤ η t ≤ 1 / (1 + (1 - γ) t / κ)`, `1 ≤ t ≤ T`,

is `ε`-accurate in the sup norm with probability at least `1 - δ`, for `ε ∈ (0, 1]`, as soon as
`T` is large enough [LCCWC24, Theorems 1 and 2]:
* with `κ = 64 log³ T`, as soon as
  `T ≥ 2500000 log⁴ T log (S A T / δ) / ((1 - γ) ^ 4 ε ^ 2)`, where `S` and `A` are the numbers
  of states and actions [LCCWC24, Theorem 2];
* with one action (synchronous TD learning) and `κ = 16 log² T`, as soon as
  `T ≥ 50000 log³ T log (S T / δ) / ((1 - γ) ^ 3 ε ^ 2)` [LCCWC24, Theorem 1].
The constant learning rate `1 / (1 + (1 - γ) T / κ)` is in the window. Synchronous TD learning is
synchronous Q-learning with one action, and the two statements share the estimates on the
learning rates of the window and the recursion over the dyadic windows below.

The proofs follow [LCCWC24, Appendices B and C]. With high probability, by Freedman's inequality,
the error of every iterate `t ≥ T / log T` is bounded in terms of the errors of the late
iterations `t / 2 ≤ k < t`:
* from below, along the state-action kernel of a policy greedy for `Q*`
  (`LMLExplore.ReinforcementLearning.measure_exists_mem_exists_lt_optQValue_sub_syncQLearning_le`),
  with the bound on the quadratic variation of the noise in terms of the late errors
  (`LMLExplore.ReinforcementLearning.tdNoiseVarBound_le`);
* from above, by the windowed recursion and the comparison with a common supersolution
  (`LMLExplore.ReinforcementLearning.measure_exists_lt_syncQLearning_sub_optQValue_le`), with
  `J ≈ log T / (1 - γ)` blocks of `L ≈ (1 - γ) T / (32 log² T)` iterations;
* with one action, the lower bound is two-sided
  (`measure_exists_mem_exists_lt_abs_syncQLearning_sub_optQValue_le`).

This gives `‖Δ t‖ ≤ √(r max 1 (max_{t / 2 ≤ k < t} ‖Δ k‖))`, with `r` of order
`log⁴ T log (S A T / δ) / ((1 - γ) ^ 4 T)` for Q-learning and
`log³ T log (S T / δ) / ((1 - γ) ^ 3 T)` for TD learning. On the dyadic windows
`T / 2 ^ (K - j) ≤ t ≤ T`, the bounds `x (j + 1) = √(r max 1 (x j))` from `x 0 = 1 / (1 - γ)`
reach `e √r` after `K ≈ log₂ log T` windows (`Real.le_mul_sqrt_of_le_sqrt_mul_max`
[LCCWC24, Appendix B.4]).

The bounds improve the source in two ways: the factor `1 / γ ^ 2` of [LCCWC24, (101)] is not
needed, since the resolvent of the one-step variances of the optimal value satisfies
`γ ^ 2 (I - γ P)⁻¹ Var_P(V*) ≤ 1 / (1 - γ) ^ 2`
(`LMLExplore.ReinforcementLearning.mul_integral_variance_optValue_le`), so that the statements
hold for every `γ < 1` instead of `γ ∈ [1 / 2, 1)`; and the constants are explicit.

## Main statements

* `measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_cube_window`: the sample complexity
  of synchronous Q-learning [LCCWC24, Theorem 2].
* `measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_window`: the sample complexity of
  synchronous TD learning [LCCWC24, Theorem 1].

## References

* [LCCWC24] G. Li, C. Cai, Y. Chen, Y. Wei and Y. Chi, *Is Q-learning minimax optimal? A tight
  sample complexity analysis*, Operations Research (2024), arXiv:2102.06548.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP Bandits
open scoped NNReal

namespace LMLExplore.ReinforcementLearning

/-! ### The rescaled linear learning rates -/

section Schedule

variable {γ : ℝ≥0} {η : ℕ → ℝ} {T : ℕ} {κ : ℝ}

/-- The learning rates of the window lie in `[0, 1]`. -/
private lemma mem_Icc_of_window (hγ : γ < 1) (hκ : 0 < κ)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {i : ℕ} (hi : i ∈ Ioc 0 T) : η i ∈ Set.Icc (0 : ℝ) 1 := by
  have h1γ : (0 : ℝ) ≤ 1 - γ := sub_nonneg.2 (by exact_mod_cast hγ.le)
  refine ⟨le_trans (by positivity) (hlo i hi), (hhi i hi).trans ?_⟩
  rw [div_le_one (by positivity)]
  exact le_add_of_nonneg_right (by positivity)

/-- The lower end of the window makes every factor `1 - η i (1 - γ)` at most `1 - κ / (2 T)`,
once `κ ≤ (1 - γ) T`. -/
private lemma le_mul_one_sub_of_window (hγ : γ < 1) (hκ : 0 < κ) (hT : κ ≤ (1 - γ) * T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    {i : ℕ} (hi : i ∈ Ioc 0 T) : κ / (2 * T) ≤ η i * (1 - γ) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hT0 : (0 : ℝ) < T := by
    have := (mem_Ioc.1 hi).1
    have := (mem_Ioc.1 hi).2
    exact_mod_cast (show 0 < T by omega)
  set X := (1 - (γ : ℝ)) * T / κ
  have hX : 1 ≤ X := by
    rw [le_div_iff₀ hκ]
    linarith
  have h₁ : 1 / (2 * X) ≤ η i :=
    (one_div_le_one_div_of_le (by positivity) (by linarith)).trans (hlo i hi)
  calc κ / (2 * T) = 1 / (2 * X) * (1 - γ) := by
        simp only [X]
        field_simp
    _ ≤ η i * (1 - γ) := mul_le_mul_of_nonneg_right h₁ h1γ.le

/-- The products `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))` of the window decay geometrically:
`ρ k t ≤ exp (-κ (t - k) / (2 T))`. -/
private lemma prod_le_exp_of_window (hγ : γ < 1) (hκ : 0 < κ) (hT : κ ≤ (1 - γ) * T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {k t : ℕ} (htT : t ≤ T) :
    ∏ i ∈ Ioc k t, (1 - η i * (1 - γ)) ≤ Real.exp (-(κ / (2 * T) * (t - k : ℕ))) := by
  have hsub : Ioc k t ⊆ Ioc 0 T := Ioc_subset_Ioc (Nat.zero_le _) htT
  refine (Real.prod_one_sub_le_exp_neg_sum fun i hi ↦ ?_).trans (Real.exp_le_exp.2 ?_)
  · have hηi := mem_Icc_of_window hγ hκ hlo hhi (hsub hi)
    have h1γ : (0 : ℝ) ≤ 1 - γ := sub_nonneg.2 (by exact_mod_cast hγ.le)
    have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
    nlinarith [hηi.1, hηi.2]
  · rw [neg_le_neg_iff, ← Nat.card_Ioc k t, mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi ↦ le_mul_one_sub_of_window hγ hκ hT hlo (hsub hi)

/-- The early products are small: for `16 log² T ≤ κ`, `T ≤ log T * t` and `t ≤ 4 (t - k)`,
`ρ k t ≤ 1 / T ^ 2`. -/
private lemma prod_le_one_div_sq_of_window (hγ : γ < 1) (h16 : 16 * Real.log T ^ 2 ≤ κ)
    (hT : κ ≤ (1 - γ) * T) (hL : 0 < Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {k t : ℕ} (htT : t ≤ T) (hTt : (T : ℝ) ≤ Real.log T * t) (hkt : t ≤ 4 * (t - k)) :
    ∏ i ∈ Ioc k t, (1 - η i * (1 - γ)) ≤ 1 / (T : ℝ) ^ 2 := by
  have hT0 : (0 : ℝ) < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · simp [h] at hL
    · exact_mod_cast h
  have hκ : 0 < κ := lt_of_lt_of_le (by positivity) h16
  refine (prod_le_exp_of_window hγ hκ hT hlo hhi htT).trans ?_
  have hkt' : (t : ℝ) ≤ 4 * (t - k : ℕ) := by exact_mod_cast hkt
  -- the exponent is at least `κ t / (8 T) ≥ 2 log² T t / T ≥ 2 log T`
  have h₁ : 2 * Real.log T ≤ κ / (2 * T) * (t - k : ℕ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h₂ : 16 * Real.log T ^ 2 * (t - k : ℕ) ≤ κ * (t - k : ℕ) :=
      mul_le_mul_of_nonneg_right h16 (Nat.cast_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hkt' (le_of_lt (mul_pos (mul_pos two_pos hL) hL)),
      mul_le_mul_of_nonneg_left hTt (le_of_lt (mul_pos two_pos hL))]
  calc Real.exp (-(κ / (2 * T) * (t - k : ℕ))) ≤ Real.exp (-(2 * Real.log T)) :=
        Real.exp_le_exp.2 (neg_le_neg h₁)
    _ = 1 / (T : ℝ) ^ 2 := by
        rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log hT0, one_div]
        norm_cast

/-- The late learning rates are small: for `T ≤ 2 log T * i`,
`η i ≤ 2 κ log T / ((1 - γ) T)`. -/
private lemma le_div_of_window (hγ : γ < 1) (hκ : 0 < κ)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ)) {i : ℕ} (hi : i ∈ Ioc 0 T)
    (hTi : (T : ℝ) ≤ 2 * Real.log T * i) :
    η i ≤ 2 * κ * Real.log T / ((1 - γ) * T) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hT0 : (0 : ℝ) < T := by
    have := (mem_Ioc.1 hi).1
    have := (mem_Ioc.1 hi).2
    exact_mod_cast (show 0 < T by omega)
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (mem_Ioc.1 hi).1
  have hY : 0 < (1 - γ) * (i : ℝ) / κ := by positivity
  calc η i ≤ 1 / (1 + (1 - γ) * i / κ) := hhi i hi
    _ ≤ 1 / ((1 - γ) * i / κ) := one_div_le_one_div_of_le hY (by linarith)
    _ = κ / ((1 - γ) * i) := one_div_div _ _
    _ ≤ 2 * κ * Real.log T / ((1 - γ) * T) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hTi (by positivity : (0 : ℝ) ≤ κ * (1 - γ))]

/-- The learning-rate weights `η^i_k = η i ∏_{j = i + 1}^k (1 - η j)` of the late iterations,
`T ≤ 2 log T * i`, are at most `2 κ log T / ((1 - γ) T)`. -/
private lemma learningRateWeight_le_of_window (hγ : γ < 1) (hκ : 0 < κ)
    (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ)) {k i : ℕ} (hi : i ∈ Ioc 0 T)
    (hTi : (T : ℝ) ≤ 2 * Real.log T * i) :
    learningRateWeight η k i ≤ 2 * κ * Real.log T / ((1 - γ) * T) :=
  (learningRateWeight_le (learningRate_mem_Icc_of_mem_Ioc hη hi).1
    fun _ hj ↦ learningRate_mem_Icc_of_mem_Ioc hη hj).trans (le_div_of_window hγ hκ hhi hi hTi)

/-- The late weights are small: for `T ≤ log T * t` and `t ≤ 2 (k + 1)`,
`η (k + 1) ρ (k + 1) t ≤ 2 κ log T / ((1 - γ) T)`. -/
private lemma mul_prod_le_of_window_of_le (hγ : γ < 1) (hκ : 0 < κ) (hL : 0 < Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {k t : ℕ} (htT : t ≤ T) (hkt : k < t) (hTt : (T : ℝ) ≤ Real.log T * t)
    (htk : t ≤ 2 * (k + 1)) :
    η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤
      2 * κ * Real.log T / ((1 - γ) * T) := by
  have hk : k + 1 ∈ Ioc 0 T := mem_Ioc.2 ⟨k.succ_pos, by omega⟩
  have hηk := mem_Icc_of_window hγ hκ hlo hhi hk
  -- the product is at most `1`
  have hρ : ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ 1 := by
    have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
    refine prod_le_one₀ (fun i hi ↦ ?_) fun i hi ↦ ?_
    · have := mem_Icc_of_window hγ hκ hlo hhi (Ioc_subset_Ioc (Nat.zero_le _) htT hi)
      have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
      nlinarith [this.1, this.2]
    · have := mem_Icc_of_window hγ hκ hlo hhi (Ioc_subset_Ioc (Nat.zero_le _) htT hi)
      nlinarith [this.1]
  have hk1 : (T : ℝ) ≤ 2 * Real.log T * ((k + 1 : ℕ) : ℝ) := by
    have : (t : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by exact_mod_cast htk
    nlinarith
  calc η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ η (k + 1) :=
        mul_le_of_le_one_right hηk.1 hρ
    _ ≤ 2 * κ * Real.log T / ((1 - γ) * T) := le_div_of_window hγ hκ hhi hk hk1

/-- All the weights `η (k + 1) ρ (k + 1) t`, `k < t`, are at most `2 κ log T / ((1 - γ) T)`, for
`2 ≤ t ≤ T ≤ log T * t`, once `16 log² T ≤ κ ≤ (1 - γ) T` and `1 ≤ log T`. -/
private lemma mul_prod_le_of_window (hγ : γ < 1) (h16 : 16 * Real.log T ^ 2 ≤ κ)
    (hT : κ ≤ (1 - γ) * T) (hL : 1 ≤ Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {k t : ℕ} (ht : 2 ≤ t) (htT : t ≤ T) (hkt : k < t) (hTt : (T : ℝ) ≤ Real.log T * t) :
    η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤
      2 * κ * Real.log T / ((1 - γ) * T) := by
  have hL0 : 0 < Real.log T := by linarith
  have hκ : 0 < κ := lt_of_lt_of_le (by positivity) h16
  rcases le_or_gt t (2 * (k + 1)) with htk | htk
  · exact mul_prod_le_of_window_of_le hγ hκ hL0 hlo hhi htT hkt hTt htk
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hk := mem_Icc_of_window hγ hκ hlo hhi (i := k + 1) (mem_Ioc.2 ⟨k.succ_pos, by omega⟩)
  have hρ := prod_le_one_div_sq_of_window hγ h16 hT hL0 hlo hhi htT hTt (k := k + 1) (by omega)
  have hρ₀ : 0 ≤ ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) :=
    Real.prod_one_sub_mul_nonneg h1γ.le h1γ' fun _ hi ↦
      mem_Icc_of_window hγ hκ hlo hhi (Ioc_subset_Ioc (Nat.zero_le _) htT hi)
  have hκL : 1 ≤ 2 * κ * Real.log T := by nlinarith
  calc η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ 1 * (1 / (T : ℝ) ^ 2) :=
        mul_le_mul hk.2 hρ hρ₀ zero_le_one
    _ ≤ 2 * κ * Real.log T / ((1 - γ) * T) := by
        rw [one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ T),
          mul_le_mul_of_nonneg_left h1γ' (by positivity : (0 : ℝ) ≤ T),
          mul_le_mul_of_nonneg_right hκL (by positivity : (0 : ℝ) ≤ T ^ 2)]

/-- Over a block of `L` iterations of the window with `2 (1 - γ) T log T ≤ κ L`, the products
`∏ (1 - η j)` are at most `1 / T`. -/
private lemma prod_one_sub_le_one_div_of_window (hγ : γ < 1) (hκ : 0 < κ)
    (hT : κ ≤ (1 - γ) * T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {L k : ℕ} (hLκ : 2 * (1 - γ) * T * Real.log T ≤ κ * L) (hLk : L ≤ k) (hkT : k ≤ T) :
    ∏ j ∈ Ioc (k - L) k, (1 - η j) ≤ 1 / (T : ℝ) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, mul_zero] at hT
    linarith
  have hsub : Ioc (k - L) k ⊆ Ioc 0 T := fun j hj ↦ by
    simp only [mem_Ioc] at hj ⊢
    omega
  refine (Real.prod_one_sub_le_exp_neg_sum fun j hj ↦
    (mem_Icc_of_window hγ hκ hlo hhi (hsub hj)).2).trans ?_
  -- each learning rate of the block is at least `κ / (2 (1 - γ) T)`
  have hηj (j : ℕ) (hj : j ∈ Ioc (k - L) k) : κ / (2 * (1 - γ) * T) ≤ η j := by
    have h := le_mul_one_sub_of_window hγ hκ hT hlo (hsub hj)
    rw [div_le_iff₀ (by positivity)] at h ⊢
    linarith
  have hsum : κ * L / (2 * (1 - γ) * T) ≤ ∑ j ∈ Ioc (k - L) k, η j :=
    calc κ * L / (2 * (1 - γ) * T) = ∑ _j ∈ Ioc (k - L) k, κ / (2 * (1 - γ) * T) := by
          rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, show k - (k - L) = L by omega]
          ring
      _ ≤ _ := sum_le_sum hηj
  have hlog : Real.log T ≤ κ * L / (2 * (1 - γ) * T) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc Real.exp (-∑ j ∈ Ioc (k - L) k, η j) ≤ Real.exp (-Real.log T) :=
        Real.exp_le_exp.2 (neg_le_neg (hlog.trans hsum))
    _ = 1 / (T : ℝ) := by rw [Real.exp_neg, Real.exp_log hT0, one_div]

end Schedule

/-! ### The logarithmic factor -/

/-- The logarithmic factor of Freedman's inequality at an iteration `t ≤ T`, for the confidence
level `δ / (2 S (T + 1))`, is at most `3 log (S T / δ)`, for `T ≥ 8`, `S ≥ 1` and `δ ∈ (0, 1)`. -/
private lemma max_one_log_le {S δ : ℝ} {t T : ℕ} (hS : 1 ≤ S) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hT : 8 ≤ (T : ℝ)) (htT : t ≤ T) :
    max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * S * (T + 1))))) ≤
      3 * Real.log (S * T / δ) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hx : 8 ≤ S * T / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hlog8 : 2 ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9
    push_cast
    linarith
  have hlogx : Real.log 8 ≤ Real.log (S * T / δ) := Real.log_le_log (by norm_num) hx
  -- `⌈log₄ t⌉ + 1 ≤ T + 1`
  have hceil : (⌈Real.logb 4 t⌉₊ : ℝ) ≤ T := by
    have h : Real.logb 4 t ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · simp [h]
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast h
      have hlog4 : 1 ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_gt_d9
        push_cast
        linarith
      rw [Real.logb, div_le_iff₀ (by linarith)]
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < t)
      nlinarith [Real.log_nonneg ht1]
    exact_mod_cast (Nat.ceil_le.2 (h.trans (by exact_mod_cast htT)))
  have hpos : 0 < (⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * S * (T + 1))) := by positivity
  refine max_le (by linarith) ?_
  calc Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * S * (T + 1))))
      ≤ Real.log (8 * (S * T / δ) ^ 2) := by
        refine Real.log_le_log hpos ?_
        rw [div_div_eq_mul_div, div_pow, mul_div_assoc', div_le_div_iff₀ hδ (by positivity)]
        have hS2 : S ≤ S ^ 2 := by nlinarith
        have hδ2 : δ ^ 2 ≤ δ := by nlinarith
        have h1 : (⌈Real.logb 4 t⌉₊ + 1 : ℝ) * (2 * S * (T + 1)) ≤ 8 * S * T ^ 2 :=
          calc (⌈Real.logb 4 t⌉₊ + 1 : ℝ) * (2 * S * (T + 1)) ≤ (T + 1) * (2 * S * (T + 1)) := by
                gcongr
            _ ≤ 8 * S * T ^ 2 := by
                nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ S)
                  (by nlinarith : (0 : ℝ) ≤ 6 * T ^ 2 - 4 * T - 2)]
        calc (⌈Real.logb 4 t⌉₊ + 1 : ℝ) * (2 * S * (T + 1)) * δ ^ 2
            ≤ 8 * S * T ^ 2 * δ := by
              nlinarith [mul_le_mul h1 hδ2 (by positivity) (by positivity)]
          _ ≤ 8 * (S * T) ^ 2 * δ := by
              nlinarith [mul_le_mul_of_nonneg_right hS2 (by positivity : (0 : ℝ) ≤ T ^ 2 * δ)]
    _ = Real.log 8 + 2 * Real.log (S * T / δ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
    _ ≤ 3 * Real.log (S * T / δ) := by linarith

/-! ### The arithmetic of one step of the recursion of the errors -/

/-- The arithmetic of one step of the recursion of the errors [LCCWC24, (121)]: with the bound
`W ≤ β B ^ 2 (2 + 4 D)` on the quadratic variation, the logarithmic factor `ℓ ≤ 3 Λ` and
`β B ^ 2 Λ = 32 s`, the high-probability bound `ρ B + 3 √(W ℓ) + 2 β B ℓ` on the error is at most
`√(5476 s max 1 D)`, as long as `ρ B ≤ √s` and `s ≤ 1 / 36864`. -/
private lemma add_le_sqrt_mul_max {B ρ W ℓ Λ β D s : ℝ} (hB : 1 ≤ B) (hρ : ρ * B ≤ √s)
    (hW : W ≤ β * B ^ 2 * (2 + 4 * D)) (hℓ₀ : 0 ≤ ℓ) (hℓ : ℓ ≤ 3 * Λ) (hβ : 0 ≤ β) (hs₀ : 0 ≤ s)
    (hs : β * B ^ 2 * Λ = 32 * s)
    (hs₁ : s ≤ 1 / 36864) :
    ρ * B + (3 * √(W * ℓ) + 2 * (β * B) * ℓ) ≤ √(5476 * s * max 1 D) := by
  set M := max 1 D
  have hM : 1 ≤ M := le_max_left _ _
  have hDM : D ≤ M := le_max_right _ _
  have hΛ : 0 ≤ Λ := by linarith
  have hsM : √s ≤ √(s * M) := Real.sqrt_le_sqrt (le_mul_of_one_le_right hs₀ hM)
  -- the martingale term
  have h₁ : 3 * √(W * ℓ) ≤ 72 * √(s * M) := by
    have hWℓ : W * ℓ ≤ 576 * (s * M) := by
      calc W * ℓ ≤ (β * B ^ 2 * (6 * M)) * (3 * Λ) :=
            mul_le_mul (hW.trans (by gcongr; linarith)) hℓ hℓ₀ (by positivity)
        _ = 18 * M * (β * B ^ 2 * Λ) := by ring
        _ = 576 * (s * M) := by rw [hs]; ring
    calc 3 * √(W * ℓ) ≤ 3 * √(576 * (s * M)) := by gcongr
      _ = 72 * √(s * M) := by
          rw [Real.sqrt_mul (by norm_num), show (576 : ℝ) = 24 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
          ring
  -- the increment term
  have h₂ : 2 * (β * B) * ℓ ≤ √(s * M) := by
    have hβB : β * B * Λ ≤ 32 * s := by
      rw [← hs]
      have : β * B * Λ * 1 ≤ β * B * Λ * B := by gcongr
      nlinarith
    have hss : 192 * s ≤ √s := by
      have hsq : √s ≤ 1 / 192 := by
        rw [Real.sqrt_le_left (by norm_num)]
        linarith
      calc 192 * s = 192 * (√s * √s) := by rw [Real.mul_self_sqrt hs₀]
        _ ≤ 192 * (1 / 192 * √s) := by gcongr
        _ = √s := by ring
    calc 2 * (β * B) * ℓ ≤ 2 * (β * B) * (3 * Λ) := by gcongr
      _ = 6 * (β * B * Λ) := by ring
      _ ≤ 6 * (32 * s) := by gcongr
      _ ≤ √(s * M) := by linarith
  calc ρ * B + (3 * √(W * ℓ) + 2 * (β * B) * ℓ) ≤ √(s * M) + (72 * √(s * M) + √(s * M)) := by
        gcongr
        exact hρ.trans hsM
    _ = 74 * √(s * M) := by ring
    _ = √(5476 * s * M) := by
        rw [show 5476 * s * M = 74 ^ 2 * (s * M) by ring, Real.sqrt_mul (by norm_num) (s * M),
          Real.sqrt_sq (by norm_num)]

/-! ### Consequences of the sample size condition -/

/-- The consequences of the sample size condition
`T ≥ 50000 log³ T log (S T / δ) / ((1 - γ) ^ 3 ε ^ 2)` used in the proof: `T ≥ 8`, `log T ≥ 2`,
`16 log² T ≤ (1 - γ) T`, `(1 / (1 - γ)) ^ 3 ≤ T`, and, with
`s = log³ T log (S T / δ) / ((1 - γ) ^ 3 T)`, `0 ≤ s ≤ ε ^ 2 / 50000` and
`1 / ((1 - γ) T ^ 2) ≤ √s`. -/
private lemma sample_size_facts {γ : ℝ≥0} (hγ : γ < 1) {ε δ S : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ < 1) (hS : 1 ≤ S) {T : ℕ} (hT : 2 ≤ T)
    (hTε : 50000 * Real.log T ^ 3 * Real.log (S * T / δ) / ((1 - γ) ^ 3 * ε ^ 2) ≤ T) :
    8 ≤ (T : ℝ) ∧ 2 ≤ Real.log T ∧ 16 * Real.log T ^ 2 ≤ (1 - γ) * T ∧
      (1 / (1 - (γ : ℝ))) ^ 3 ≤ T ∧
      0 ≤ Real.log T ^ 3 * Real.log (S * T / δ) / ((1 - γ) ^ 3 * T) ∧
      Real.log T ^ 3 * Real.log (S * T / δ) / ((1 - γ) ^ 3 * T) ≤ ε ^ 2 / 50000 ∧
      1 / (1 - (γ : ℝ)) / (T : ℝ) ^ 2 ≤
        √(Real.log T ^ 3 * Real.log (S * T / δ) / ((1 - γ) ^ 3 * T)) := by
  set L := Real.log T with hL_def
  set Λ := Real.log (S * T / δ) with hΛ_def
  set B : ℝ := 1 / (1 - γ) with hB_def
  set s := L ^ 3 * Λ / ((1 - γ) ^ 3 * T) with hs_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hΛL : L ≤ Λ := Real.log_le_log hT0 (by
    rw [le_div_iff₀ hδ]
    nlinarith)
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ h1γ]
    linarith
  -- the sample size condition: `50000 L ^ 3 Λ ≤ (1 - γ) ^ 3 ε ^ 2 T`
  have hcond : 50000 * L ^ 3 * Λ ≤ (1 - γ) ^ 3 * ε ^ 2 * T := by
    rwa [div_le_iff₀ (by positivity), mul_comm (T : ℝ)] at hTε
  have h1γ3 : (1 - (γ : ℝ)) ^ 3 ≤ 1 := pow_le_one₀ h1γ.le h1γ'
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε₁
  have hcondT : 50000 * L ^ 3 * Λ ≤ (1 - γ) ^ 3 * T :=
    hcond.trans (by nlinarith [mul_le_mul_of_nonneg_left hε2 (by positivity :
      (0 : ℝ) ≤ (1 - γ) ^ 3 * T)])
  have hsε : s ≤ ε ^ 2 / 50000 := by
    rw [hs_def, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hs₀ : 0 ≤ s := div_nonneg (mul_nonneg (by positivity) (hL0.le.trans hΛL)) (by positivity)
  have hs₁ : s ≤ 1 / 50000 := hsε.trans (by gcongr)
  -- `T ≥ 8`, hence `log T ≥ 2`
  have hlog2 := Real.log_two_gt_d9
  have hL2' : (0.6931471803 : ℝ) ≤ L := by
    have := Real.log_le_log (by norm_num) hT2
    linarith
  have hT8 : 8 ≤ (T : ℝ) := by
    have h1 : 50000 * L ^ 4 ≤ T := by
      have := mul_le_mul_of_nonneg_left hΛL (by positivity : (0 : ℝ) ≤ 50000 * L ^ 3)
      nlinarith [mul_le_mul_of_nonneg_right h1γ3 hT0.le]
    have h2 : (0.6931471803 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL2' 4
    nlinarith
  have hL2 : 2 ≤ L := by
    have h8 := Real.log_le_log (by norm_num) hT8
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  -- consequences of the sample size condition
  have h16 : 16 * L ^ 2 ≤ (1 - γ) * T := by
    have : (1 - (γ : ℝ)) ^ 3 * T ≤ (1 - γ) * T := by
      have : (1 - (γ : ℝ)) ^ 3 ≤ 1 - γ := by
        nlinarith [mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 2) h1γ.le h1γ') h1γ.le]
      gcongr
    have hL3 : L ^ 2 ≤ L ^ 3 * Λ := by
      calc L ^ 2 = L ^ 2 * 1 * 1 := by ring
        _ ≤ L ^ 2 * L * Λ := by gcongr
        _ = L ^ 3 * Λ := by ring
    nlinarith
  have hB3 : B ^ 3 ≤ T := by
    rw [hB_def, div_pow, one_pow, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ L ^ 3 * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hΛ1
    nlinarith
  have hBs : B / (T : ℝ) ^ 2 ≤ √s := by
    rw [Real.le_sqrt (by positivity) hs₀]
    have h₁ : (B / (T : ℝ) ^ 2) ^ 2 = 1 / ((1 - γ) ^ 2 * T ^ 4) := by
      rw [hB_def]
      field_simp
    have h₂ : (1 - (γ : ℝ)) ^ 3 * T ≤ (1 - γ) ^ 2 * T ^ 4 :=
      mul_le_mul (pow_le_pow_of_le_one h1γ.le h1γ' (by norm_num))
        (le_self_pow₀ (by linarith) (by norm_num)) hT0.le (by positivity)
    have h₃ : 1 / ((1 - γ) ^ 3 * T) ≤ s := by
      rw [hs_def]
      exact div_le_div_of_nonneg_right
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hΛ1) (by positivity)
    rw [h₁]
    exact (one_div_le_one_div_of_le (by positivity) h₂).trans h₃
  exact ⟨hT8, hL2, h16, hB3, hs₀, hsε, hBs⟩

/-- The dyadic windows: for `log T ≥ 2` and `B ≥ 1` with `3 log B ≤ log T`, the number
`K = log₂ ⌊log T⌋` of windows satisfies `1 ≤ K`, `2 ^ K ≤ log T` and `B ≤ e ^ 2 ^ K`. -/
private lemma dyadic_facts {L B : ℝ} (hL2 : 2 ≤ L) (hB1 : 1 ≤ B) (hB3 : 3 * Real.log B ≤ L) :
    1 ≤ Nat.log 2 ⌊L⌋₊ ∧ ((2 ^ Nat.log 2 ⌊L⌋₊ : ℕ) : ℝ) ≤ L ∧
      B ≤ Real.exp 1 ^ 2 ^ Nat.log 2 ⌊L⌋₊ := by
  set K := Nat.log 2 ⌊L⌋₊ with hK_def
  have hL0 : 0 < L := by linarith
  have hfloor : 2 ≤ ⌊L⌋₊ := Nat.le_floor (by exact_mod_cast hL2)
  have hK1 : 1 ≤ K := Nat.log_pos one_lt_two hfloor
  have hKL : ((2 ^ K : ℕ) : ℝ) ≤ L :=
    (Nat.cast_le.2 (Nat.pow_log_le_self 2 (by omega))).trans (Nat.floor_le hL0.le)
  have hLK : L < 2 * 2 ^ K := by
    have h := Nat.lt_pow_succ_log_self one_lt_two ⌊L⌋₊
    have h₁ : L < ⌊L⌋₊ + 1 := Nat.lt_floor_add_one L
    have h₂ : ((⌊L⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (K + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h₂
    rw [pow_succ] at h₂
    linarith
  refine ⟨hK1, hKL, ?_⟩
  rw [← Real.exp_natCast_mul, mul_one, ← Real.log_le_iff_le_exp (by positivity)]
  push_cast
  linarith [Real.log_nonneg hB1]

/-- An iteration `t` of the dyadic windows, `T ≤ 2 ^ K t` with `2 ^ K ≤ log T` and `T ≥ 8`,
satisfies `2 ≤ t` and `T ≤ log T * t`. -/
private lemma two_le_and_le_log_mul_of_le_two_pow_mul {T K t : ℕ} (hT8 : 8 ≤ (T : ℝ))
    (hKL : ((2 ^ K : ℕ) : ℝ) ≤ Real.log T) (hTt : T ≤ 2 ^ K * t) :
    2 ≤ t ∧ (T : ℝ) ≤ Real.log T * t := by
  have hTt' : (T : ℝ) ≤ Real.log T * t := by
    have : (T : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) * t := by exact_mod_cast hTt
    nlinarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  refine ⟨?_, hTt'⟩
  have hLT : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos (by linarith)
  by_contra h
  interval_cases t
  · rw [Nat.cast_zero, mul_zero] at hTt'
    linarith
  · rw [Nat.cast_one, mul_one] at hTt'
    linarith

/-- The bounds on the errors in the dyadic windows [LCCWC24, Appendix C]: `windowBound B r 0 = B`
and `windowBound B r (j + 1) = √(r max 1 (windowBound B r j))`. -/
private noncomputable def windowBound (B r : ℝ) : ℕ → ℝ
  | 0 => B
  | j + 1 => √(r * max 1 (windowBound B r j))

/-- The final accuracy: if `0 ≤ r` and `7.39 r ≤ ε ^ 2`, then `e √r ≤ ε`. -/
private lemma exp_one_mul_sqrt_le {r ε : ℝ} (hε : 0 < ε) (hr₀ : 0 ≤ r)
    (hrε : 7.39 * r ≤ ε ^ 2) : Real.exp 1 * √r ≤ ε := by
  have he := Real.exp_one_lt_d9
  have he₀ := Real.exp_pos 1
  rw [show Real.exp 1 * √r = √(Real.exp 1 ^ 2 * r) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he₀.le], Real.sqrt_le_left hε.le]
  have he2 : Real.exp 1 ^ 2 ≤ 7.39 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right he2 hr₀]

/-! ### The arithmetic of the sample complexity of Q-learning -/

/-- The consequences of the sample size condition of Q-learning
`T ≥ 2500000 log⁴ T log (S T / δ) / ((1 - γ) ^ 4 ε ^ 2)` used in the proof: `T ≥ 8`,
`log T ≥ 2`, `64 log³ T ≤ (1 - γ) T`, `(1 / (1 - γ)) ^ 3 ≤ T` and
`log⁴ T log (S T / δ) / ((1 - γ) ^ 4 T) ≤ ε ^ 2 / 2500000`. -/
private lemma sample_size_facts_of_cube {γ : ℝ≥0} (hγ : γ < 1) {ε δ S : ℝ} (hε : 0 < ε)
    (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) (hS : 1 ≤ S) {T : ℕ} (hT : 2 ≤ T)
    (hTε : 2500000 * Real.log T ^ 4 * Real.log (S * T / δ) / ((1 - γ) ^ 4 * ε ^ 2) ≤ T) :
    8 ≤ (T : ℝ) ∧ 2 ≤ Real.log T ∧ 64 * Real.log T ^ 3 ≤ (1 - γ) * T ∧
      (1 / (1 - (γ : ℝ))) ^ 3 ≤ T ∧
      Real.log T ^ 4 * Real.log (S * T / δ) / ((1 - γ) ^ 4 * T) ≤ ε ^ 2 / 2500000 := by
  set L := Real.log T with hL_def
  set Λ := Real.log (S * T / δ) with hΛ_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hΛL : L ≤ Λ := Real.log_le_log hT0 (by
    rw [le_div_iff₀ hδ]
    nlinarith)
  -- the sample size condition: `2500000 L ^ 4 Λ ≤ (1 - γ) ^ 4 ε ^ 2 T`
  have hcond : 2500000 * L ^ 4 * Λ ≤ (1 - γ) ^ 4 * ε ^ 2 * T := by
    rwa [div_le_iff₀ (by positivity), mul_comm (T : ℝ)] at hTε
  have h1γ4 : (1 - (γ : ℝ)) ^ 4 ≤ 1 := pow_le_one₀ h1γ.le h1γ'
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε₁
  have hcondT : 2500000 * L ^ 4 * Λ ≤ (1 - γ) ^ 4 * T :=
    hcond.trans (by nlinarith [mul_le_mul_of_nonneg_left hε2 (by positivity :
      (0 : ℝ) ≤ (1 - γ) ^ 4 * T)])
  have hsε : L ^ 4 * Λ / ((1 - γ) ^ 4 * T) ≤ ε ^ 2 / 2500000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- `T ≥ 8`, hence `log T ≥ 2`
  have hlog2 := Real.log_two_gt_d9
  have hL2' : (0.6931471803 : ℝ) ≤ L := by
    have := Real.log_le_log (by norm_num) hT2
    linarith
  have hT8 : 8 ≤ (T : ℝ) := by
    have h1 : 2500000 * L ^ 5 ≤ T := by
      have := mul_le_mul_of_nonneg_left hΛL (by positivity : (0 : ℝ) ≤ 2500000 * L ^ 4)
      nlinarith [mul_le_mul_of_nonneg_right h1γ4 hT0.le]
    have h2 : (0.6931471803 : ℝ) ^ 5 ≤ L ^ 5 := pow_le_pow_left₀ (by norm_num) hL2' 5
    nlinarith
  have hL2 : 2 ≤ L := by
    have h8 := Real.log_le_log (by norm_num) hT8
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hLΛ : (1 : ℝ) ≤ L ^ 4 * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hΛ1
  have h64 : 64 * L ^ 3 ≤ (1 - γ) * T := by
    have h4 : (1 - (γ : ℝ)) ^ 4 ≤ 1 - γ := by
      have := pow_le_pow_of_le_one h1γ.le h1γ' (show 1 ≤ 4 by norm_num)
      rwa [pow_one] at this
    have hL3 : L ^ 3 ≤ L ^ 4 * Λ := by
      calc L ^ 3 = L ^ 3 * 1 * 1 := by ring
        _ ≤ L ^ 3 * L * Λ := by gcongr
        _ = L ^ 4 * Λ := by ring
    nlinarith [mul_le_mul_of_nonneg_right h4 hT0.le]
  have hB3 : (1 / (1 - (γ : ℝ))) ^ 3 ≤ T := by
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
    have h3 : (1 - (γ : ℝ)) ^ 4 ≤ (1 - γ) ^ 3 := pow_le_pow_of_le_one h1γ.le h1γ' (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right h3 hT0.le]
  exact ⟨hT8, hL2, h64, hB3, hsε⟩

/-- The logarithmic factor of the union bound over the dyadic windows and the iterations:
`log (S (T + 1) ^ 2 T / δ) ≤ 4 log (S T / δ)`, for `T ≥ 8`, `S ≥ 1` and `δ ∈ (0, 1)`. -/
private lemma log_mul_sq_le {S δ : ℝ} {T : ℕ} (hS : 1 ≤ S) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (hT : 8 ≤ (T : ℝ)) :
    Real.log (S * (T + 1) ^ 2 * T / δ) ≤ 4 * Real.log (S * T / δ) := by
  have hT0 : (0 : ℝ) < T := by linarith
  set X := S * T / δ with hX
  have hTX : (T : ℝ) ≤ X := by
    rw [hX, le_div_iff₀ hδ]
    nlinarith
  have hT3 : ((T : ℝ) + 1) ^ 2 ≤ T ^ 3 := by nlinarith
  calc Real.log (S * (T + 1) ^ 2 * T / δ) ≤ Real.log (X ^ 4) := by
        refine Real.log_le_log (by positivity) ?_
        calc S * (T + 1) ^ 2 * T / δ = X * (T + 1) ^ 2 := by rw [hX]; ring
          _ ≤ X * X ^ 3 := by gcongr; exact hT3.trans (by gcongr)
          _ = X ^ 4 := by ring
    _ = 4 * Real.log X := by rw [Real.log_pow]; norm_num

/-- The blocks of the windowed recursion of Q-learning, for `log T ≥ 2` and
`64 log³ T ≤ (1 - γ) T`: the block length `L = ⌈(1 - γ) T / (32 log² T)⌉` is positive and
satisfies `2 (1 - γ) T log T ≤ 64 log³ T L`, the number of blocks `J = ⌈log T / (1 - γ)⌉`
satisfies `γ ^ J ≤ 1 / T`, and `J` blocks fit in the late iterations of every iteration
`t ≥ T / log T`: `(t + 1) / 2 + J L ≤ t`. -/
private lemma block_facts {γ : ℝ≥0} (hγ : γ < 1) {T : ℕ} (hL2 : 2 ≤ Real.log T)
    (h64 : 64 * Real.log T ^ 3 ≤ (1 - γ) * T) :
    0 < ⌈(1 - γ) * T / (32 * Real.log T ^ 2)⌉₊ ∧
      2 * (1 - γ) * T * Real.log T ≤
        64 * Real.log T ^ 3 * ⌈(1 - γ) * T / (32 * Real.log T ^ 2)⌉₊ ∧
      (γ : ℝ) ^ ⌈Real.log T / (1 - γ)⌉₊ ≤ 1 / T ∧
      ∀ t : ℕ, (T : ℝ) ≤ Real.log T * t →
        (t + 1) / 2 + ⌈Real.log T / (1 - γ)⌉₊ * ⌈(1 - γ) * T / (32 * Real.log T ^ 2)⌉₊ ≤ t := by
  set L := Real.log T with hL_def
  set x := (1 - (γ : ℝ)) * T / (32 * L ^ 2) with hx_def
  set a := L / (1 - (γ : ℝ)) with ha_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hL0 : 0 < L := by linarith
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, mul_zero] at h64
    linarith [pow_pos hL0 3]
  have hx0 : 0 < x := by positivity
  have ha0 : 0 < a := by positivity
  have hLx' : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hJa' : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0.le
  refine ⟨Nat.ceil_pos.2 hx0, ?_, ?_, fun t ht ↦ ?_⟩
  · calc 2 * (1 - γ) * T * L = 64 * L ^ 3 * x := by
          rw [hx_def]
          field_simp
          ring
      _ ≤ 64 * L ^ 3 * ⌈x⌉₊ := by gcongr; exact Nat.le_ceil x
  · -- `γ ≤ exp (-(1 - γ))`
    have hγe : (γ : ℝ) ≤ Real.exp (-(1 - γ)) := by
      linarith [Real.one_sub_le_exp_neg (1 - (γ : ℝ))]
    have haL : L ≤ ⌈a⌉₊ * (1 - γ) :=
      calc L = a * (1 - γ) := by rw [ha_def]; field_simp
        _ ≤ ⌈a⌉₊ * (1 - γ) := by gcongr; exact Nat.le_ceil a
    calc (γ : ℝ) ^ ⌈a⌉₊ ≤ Real.exp (-(1 - γ)) ^ ⌈a⌉₊ := pow_le_pow_left₀ γ.coe_nonneg hγe _
      _ = Real.exp (-(⌈a⌉₊ * (1 - γ))) := by rw [← Real.exp_natCast_mul]; ring_nf
      _ ≤ Real.exp (-L) := Real.exp_le_exp.2 (neg_le_neg haL)
      _ = 1 / T := by rw [Real.exp_neg, Real.exp_log hT0, one_div]
  · -- `L (2 J L + 1) ≤ 11 T / 64 ≤ T ≤ L t`
    have h1 : L * (a * x) = T / 32 := by
      rw [ha_def, hx_def]
      field_simp
    have h2 : L * a ≤ T / 64 := by
      rw [ha_def, ← mul_div_assoc, div_le_div_iff₀ h1γ (by norm_num)]
      nlinarith
    have h3 : L * x ≤ T / 64 := by
      rw [hx_def, show L * ((1 - γ) * T / (32 * L ^ 2)) = (1 - γ) * T / (32 * L) by
        field_simp, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h4 : L ≤ T / 64 := by nlinarith
    have hJL : (⌈a⌉₊ : ℝ) * ⌈x⌉₊ ≤ (a + 1) * (x + 1) :=
      mul_le_mul hJa'.le hLx'.le (by positivity) (by positivity)
    have hmain : L * (2 * ((⌈a⌉₊ * ⌈x⌉₊ : ℕ) : ℝ) + 1) ≤ L * t := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hJL hL0.le]
    have : 2 * (⌈a⌉₊ * ⌈x⌉₊) + 1 ≤ t := by exact_mod_cast le_of_mul_le_mul_left hmain hL0
    omega

/-- The arithmetic of the upper bound of one step of the recursion of the errors of Q-learning
[LCCWC24, (40)]: with `B = 1 / c`, a contraction `a ≤ ρ` of the initial error with
`ρ / c ^ 2 ≤ √s`, a logarithmic factor `ℓ ≤ 3 Λ` and `β Λ = 128 c ^ 3 s`, the bound
`a B + √(2 (ρ B + 2 β B ℓ) ^ 2 + 36 β ℓ B (1 + 4 g ^ 2 D)) / c` on the error is at most
`√(69696 s max 1 D)`, as long as `s ≤ 1 / 589824`. -/
private lemma add_sqrt_div_le_sqrt_mul_max {c g a ρ β ℓ Λ D s : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (hg : g ^ 2 ≤ 1) (ha₀ : 0 ≤ a) (ha : a ≤ ρ) (hρ : ρ / c ^ 2 ≤ √s) (hβ₀ : 0 ≤ β)
    (hℓ₀ : 0 ≤ ℓ) (hℓ : ℓ ≤ 3 * Λ) (hs : β * Λ = 128 * c ^ 3 * s) (hs₁ : s ≤ 1 / 589824)
    (hD₀ : 0 ≤ D) :
    a * (1 / c) + √(2 * (ρ * (1 / c) + 2 * (β * (1 / c)) * ℓ) ^ 2 +
        36 * β * ℓ * (1 / c) * (1 + 4 * g ^ 2 * D)) / c ≤ √(69696 * s * max 1 D) := by
  set M := max 1 D
  have hM : 1 ≤ M := le_max_left _ _
  have hDM : D ≤ M := le_max_right _ _
  have hc3 : 0 < c ^ 3 := by positivity
  have hs₀ : 0 ≤ s := by
    have h := mul_nonneg hβ₀ (by linarith : (0 : ℝ) ≤ Λ)
    rw [hs] at h
    nlinarith
  have hsM : √s ≤ √(s * M) := Real.sqrt_le_sqrt (le_mul_of_one_le_right hs₀ hM)
  have hρ₀ : 0 ≤ ρ := ha₀.trans ha
  -- the increment term `y = β ℓ / c ^ 2` is at most `384 c s`
  set y := β * ℓ / c ^ 2 with hy_def
  have hy₀ : 0 ≤ y := by positivity
  have hy : y ≤ 384 * c * s := by
    rw [hy_def, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hℓ hβ₀]
  have hss : 768 * s ≤ √s := by
    have hsq : √s ≤ 1 / 768 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    calc 768 * s = 768 * (√s * √s) := by rw [Real.mul_self_sqrt hs₀]
      _ ≤ 768 * (1 / 768 * √s) := by gcongr
      _ = √s := by ring
  have h2y : 2 * y ≤ √s := by nlinarith
  -- the bound under the square root, divided by `c ^ 2`
  have hid : (2 * (ρ * (1 / c) + 2 * (β * (1 / c)) * ℓ) ^ 2 +
      36 * β * ℓ * (1 / c) * (1 + 4 * g ^ 2 * D)) / c ^ 2 =
      2 * (ρ / c ^ 2 + 2 * y) ^ 2 + 36 * (y / c) * (1 + 4 * g ^ 2 * D) := by
    rw [hy_def]
    field_simp
  have hyc : y / c ≤ 384 * s := by
    rw [div_le_iff₀ hc]
    nlinarith
  have hX : (2 * (ρ * (1 / c) + 2 * (β * (1 / c)) * ℓ) ^ 2 +
      36 * β * ℓ * (1 / c) * (1 + 4 * g ^ 2 * D)) / c ^ 2 ≤ 263 ^ 2 * (s * M) := by
    rw [hid]
    have h₁ : (ρ / c ^ 2 + 2 * y) ^ 2 ≤ 4 * s := by
      calc (ρ / c ^ 2 + 2 * y) ^ 2 ≤ (2 * √s) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
        _ = 4 * s := by rw [mul_pow, Real.sq_sqrt hs₀]; ring
    have h4 : 1 + 4 * g ^ 2 * D ≤ 5 * M := by nlinarith
    have h₂ : 36 * (y / c) * (1 + 4 * g ^ 2 * D) ≤ 36 * (384 * s) * (5 * M) :=
      mul_le_mul (by linarith) h4 (by positivity) (by positivity)
    nlinarith
  have hsq : √(2 * (ρ * (1 / c) + 2 * (β * (1 / c)) * ℓ) ^ 2 +
      36 * β * ℓ * (1 / c) * (1 + 4 * g ^ 2 * D)) / c ≤ 263 * √(s * M) :=
    calc _ = √((2 * (ρ * (1 / c) + 2 * (β * (1 / c)) * ℓ) ^ 2 +
          36 * β * ℓ * (1 / c) * (1 + 4 * g ^ 2 * D)) / c ^ 2) := by
          rw [Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le]
      _ ≤ √(263 ^ 2 * (s * M)) := Real.sqrt_le_sqrt hX
      _ = 263 * √(s * M) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 263 ^ 2),
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 263)]
  have ha' : a * (1 / c) ≤ √s :=
    calc a * (1 / c) ≤ ρ / c ^ 2 := by
          rw [mul_one_div, div_le_div_iff₀ hc (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hc₁ (mul_nonneg ha₀ hc.le),
            mul_le_mul_of_nonneg_right ha hc.le]
      _ ≤ √s := hρ
  calc _ ≤ √(s * M) + 263 * √(s * M) := add_le_add (ha'.trans hsM) hsq
    _ = √(264 ^ 2 * (s * M)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 264 ^ 2),
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 264)]
        ring
    _ = √(69696 * s * M) := by
        congr 1
        ring

/-! ### The lower bound of one step of the recursion of the errors -/

section LowerStep

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ}

/-- **The lower bound of one step of the recursion of the errors** [LCCWC24, (121)]. With
rewards in `[0, 1]`, an initial value in `[0, 1 / (1 - γ)]`, learning rates in `[0, 1]` at every
iteration and in the window `[1 / (1 + (1 - γ) T / κ), 1 / (1 + (1 - γ) t / κ)]` at the
iterations `1 ≤ t ≤ T`, with `16 log² T ≤ κ ≤ (1 - γ) T`, let `2 ≤ t ≤ T ≤ log T * t`, let `π` be
greedy for `Q*` and let `D ≥ 0` bound the errors of the value estimates at the late iterations
`(t + 1) / 2 ≤ k < t`. If `x` is at most the bound of Freedman's inequality at iteration `t`
along the state-action kernel of `π`, with a logarithmic factor `ℓ ≤ 3 Λ` and the bound
`2 κ log T / (1 - γ) ^ 2 T` on the increments, then `x ≤ √(5476 s max 1 D)`, with
`s = κ log T Λ / (16 (1 - γ) ^ 3 T)`. -/
private lemma le_sqrt_mul_max_of_le_tdNoiseVarBound (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {T : ℕ} {κ : ℝ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    (h16 : 16 * Real.log T ^ 2 ≤ κ) (hκT : κ ≤ (1 - γ) * T) (hL1 : 1 ≤ Real.log T)
    {ℓ Λ : ℝ} (hℓ₀ : 0 ≤ ℓ) (hℓ : ℓ ≤ 3 * Λ) {s : ℝ} (hs₁ : s ≤ 1 / 36864)
    (hs : κ * Real.log T * Λ / (16 * (1 - γ) ^ 3 * T) = s)
    (hBs : 1 / (1 - (γ : ℝ)) / (T : ℝ) ^ 2 ≤ √s)
    {t : ℕ} (ht : 2 ≤ t) (htT : t ≤ T) (hTt : (T : ℝ) ≤ Real.log T * t)
    {π : 𝓢 → 𝓐} (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s)
    {ω : ℕ → 𝓢 × 𝓐 → 𝓢} {D : ℝ} (hD₀ : 0 ≤ D)
    (hD : ∀ k ∈ Ico ((t + 1) / 2) t, ∀ s',
      |(⨆ a, syncQLearning (meanReward M.R) γ η Q₀ k ω (s', a)) - M.optValue γ s'| ≤ D)
    (q : 𝓢 × 𝓐) {x : ℝ}
    (hx : x ≤ (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (1 / (1 - γ)) +
      (3 * √(tdNoiseVarBound M γ η Q₀
          (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω q * ℓ) +
        2 * (2 * κ * Real.log T / ((1 - γ) * T) * (1 / (1 - γ))) * ℓ)) :
    x ≤ √(5476 * s * max 1 D) := by
  set L := Real.log T with hL_def
  set B : ℝ := 1 / (1 - γ) with hB_def
  set β := 2 * κ * L / ((1 - γ) * T) with hβ_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hL0 : 0 < L := by linarith
  have hκ : 0 < κ := lt_of_lt_of_le (by positivity) h16
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ h1γ]
    linarith
  have hβ₀ : 0 < β := by positivity
  have hs₀ : 0 ≤ s := by
    have hΛ : 0 ≤ Λ := by linarith
    rw [← hs]
    positivity
  have hρ₀ := prod_one_sub_mul_one_sub_nonneg hγ hη
  -- the quadratic variation is at most `β B ^ 2 (2 + 4 D)`
  have hW := tdNoiseVarBound_le hγ hR hη hQ₀ hπ (m := (t + 1) / 2) (t := t) (by omega) hD₀ hD
    hβ₀.le (fun k hk ↦ mul_prod_le_of_window_of_le hγ hκ hL0 hlo hhi htT (mem_Ico.1 hk).2 hTt
      (by have := (mem_Ico.1 hk).1; omega)) q
  have hE : ∑ k ∈ range ((t + 1) / 2),
      (η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) ^ 2 ≤ β := by
    have hterm (k : ℕ) (hk : k ∈ range ((t + 1) / 2)) :
        (η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) ^ 2 ≤
          (1 / (T : ℝ) ^ 2) ^ 2 := by
      have hk' := mem_range.1 hk
      have hρ := prod_le_one_div_sq_of_window hγ h16 hκT hL0 hlo hhi htT hTt (k := k + 1)
        (by omega)
      refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg (hη k).1 γ.coe_nonneg) (hρ₀ _ _)) ?_ 2
      calc η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))
          ≤ 1 * 1 * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (hη k).2 hγ1 γ.coe_nonneg zero_le_one)
              (hρ₀ _ _)
        _ ≤ 1 / (T : ℝ) ^ 2 := by rw [one_mul, one_mul]; exact hρ
    have hm : (((t + 1) / 2 : ℕ) : ℝ) ≤ T := by exact_mod_cast (show (t + 1) / 2 ≤ T by omega)
    have hκL : 1 ≤ 2 * κ * L := by nlinarith
    calc _ ≤ ∑ k ∈ range ((t + 1) / 2), (1 / (T : ℝ) ^ 2) ^ 2 := sum_le_sum hterm
      _ = (((t + 1) / 2 : ℕ) : ℝ) * (1 / (T : ℝ) ^ 2) ^ 2 := by simp
      _ ≤ T * (1 / (T : ℝ) ^ 2) ^ 2 := by gcongr
      _ ≤ β := by
          rw [hβ_def, div_pow, one_pow, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity)
            (by positivity)]
          have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
          have hT3 : (T : ℝ) ^ 2 ≤ (T ^ 2) ^ 2 := le_self_pow₀ (one_le_pow₀ hT1) (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_left h1γ' (by positivity : (0 : ℝ) ≤ T ^ 2),
            mul_le_mul hκL hT3 (by positivity) (by positivity)]
  have hW' : tdNoiseVarBound M γ η Q₀
      (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω q ≤
        β * B ^ 2 * (2 + 4 * D) := by
    have hBB : B / (1 - γ) = B ^ 2 := by
      rw [hB_def]
      field_simp
    have h4 : 4 * γ ^ 2 * B * D / (1 - γ) ≤ 4 * B ^ 2 * D := by
      rw [show 4 * (γ : ℝ) ^ 2 * B * D / (1 - γ) = 4 * γ ^ 2 * D * (B / (1 - γ)) by ring, hBB]
      have : (γ : ℝ) ^ 2 ≤ 1 := pow_le_one₀ γ.coe_nonneg hγ1
      nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hD₀ (sq_nonneg B))]
    have h₁ := mul_le_mul_of_nonneg_left hE (sq_nonneg B)
    have h₂ := mul_le_mul_of_nonneg_left h4 hβ₀.le
    nlinarith
  have hρ0 := prod_le_one_div_sq_of_window hγ h16 hκT hL0 hlo hhi htT hTt (k := 0) (by omega)
  refine hx.trans (add_le_sqrt_mul_max hB1 ?_ hW' hℓ₀ hℓ hβ₀.le hs₀ ?_ hs₁)
  · calc (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * B ≤ 1 / (T : ℝ) ^ 2 * B :=
        mul_le_mul_of_nonneg_right hρ0 (zero_le_one.trans hB1)
      _ = B / (T : ℝ) ^ 2 := by ring
      _ ≤ √s := hBs
  · rw [hβ_def, hB_def, ← hs]
    field_simp
    ring

end LowerStep

/-- **The induction over the dyadic windows** [LCCWC24, Appendix C]. Let `e t` be bounded by
`u 0` at the iterations `t ≤ T`, and let the bound `u j` on the late iterations
`(t + 1) / 2 ≤ k < t` give the bound `u (j + 1)` at every iteration `t ≤ T` of the window
`T ≤ 2 ^ (K - (j + 1)) t`, for `j < K`. Then `e T` is bounded by `u K`: by induction on `j`, the
iterations `T ≤ 2 ^ (K - j) t` are bounded by `u j`. -/
private lemma abs_le_of_dyadic {ι : Type*} {e : ℕ → ι → ℝ} {u : ℕ → ℝ} {T K : ℕ}
    (h0 : ∀ t ≤ T, ∀ q, |e t q| ≤ u 0)
    (hstep : ∀ j < K, ∀ t ≤ T, T ≤ 2 ^ (K - (j + 1)) * t →
      (∀ k ∈ Ico ((t + 1) / 2) t, ∀ q, |e k q| ≤ u j) → ∀ q, |e t q| ≤ u (j + 1))
    (q : ι) : |e T q| ≤ u K := by
  have claim (j : ℕ) (hj : j ≤ K) (t : ℕ) (htT : t ≤ T) (hTt : T ≤ 2 ^ (K - j) * t)
      (q : ι) : |e t q| ≤ u j := by
    induction j generalizing t q with
    | zero => exact h0 t htT q
    | succ j ih =>
      refine hstep j (by omega) t htT hTt (fun k hk q ↦ ?_) q
      obtain ⟨hk₁, hk₂⟩ := mem_Ico.1 hk
      refine ih (by omega) k (by omega) ?_ q
      have h2 : 2 ^ (K - j) = 2 ^ (K - (j + 1)) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      calc T ≤ 2 ^ (K - (j + 1)) * t := hTt
        _ ≤ 2 ^ (K - (j + 1)) * (2 * k) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ (K - j) * k := by rw [h2]; ring
  exact claim K le_rfl T le_rfl (by simp) q

/-! ### The sample complexity of TD learning -/

section TD

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Fintype 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Unique 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ}

/-- **The errors of TD learning on the event of Freedman's inequality** [LCCWC24, Appendix C].
Under the assumptions of `measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_window`, with
learning rates in `[0, 1]` at every iteration, let `K ≥ 1` with `2 ^ K ≤ log T` and
`1 / (1 - γ) ≤ e ^ 2 ^ K`, and let the bound of Freedman's inequality, with the confidence level
`δ / (2 S (T + 1))` and the bound `32 log³ T / (1 - γ) ^ 2 T` on the increments, hold at every
iteration `t ≤ T` of the dyadic windows, `T ≤ 2 ^ K t`. Then the error of the `T`-th iterate is at
most `e √(5476 s)`, with `s = log³ T log (S T / δ) / ((1 - γ) ^ 3 T)`: by
`le_sqrt_mul_max_of_le_tdNoiseVarBound` and the induction over the dyadic windows, the errors at
the iterations `T ≤ 2 ^ (K - j) t` are at most `windowBound (1 / (1 - γ)) (5476 s) j`, which the
square-root recursion bounds at `j = K`. -/
private lemma abs_syncQLearning_sub_optQValue_le_of_window (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {T : ℕ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    (h16 : 16 * Real.log T ^ 2 ≤ (1 - γ) * T) (hL1 : 1 ≤ Real.log T) (hT8 : 8 ≤ (T : ℝ))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1 / 50000)
    (hs : Real.log T ^ 3 * Real.log (Fintype.card 𝓢 * T / δ) / ((1 - γ) ^ 3 * T) = s)
    (hBs : 1 / (1 - (γ : ℝ)) / (T : ℝ) ^ 2 ≤ √s) {K : ℕ} (hK1 : 1 ≤ K)
    (hKL : ((2 ^ K : ℕ) : ℝ) ≤ Real.log T) (hBK : 1 / (1 - (γ : ℝ)) ≤ Real.exp 1 ^ 2 ^ K)
    {ω : ℕ → 𝓢 × 𝓐 → 𝓢}
    (hgood : ∀ t ≤ T, T ≤ 2 ^ K * t → ∀ q,
      |syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q| ≤
        (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (1 / (1 - γ)) +
          (3 * √(tdNoiseVarBound M γ η Q₀
              (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) t ω q *
            max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * Fintype.card 𝓢 * (T + 1)))))) +
          2 * (2 * (16 * Real.log T ^ 2) * Real.log T / ((1 - γ) * T) * (1 / (1 - γ))) *
            max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * Fintype.card 𝓢 * (T + 1)))))))
    (p : 𝓢 × 𝓐) :
    |syncQLearning (meanReward M.R) γ η Q₀ T ω p - M.optQValue γ p| ≤ Real.exp 1 * √(5476 * s) := by
  set B : ℝ := 1 / (1 - γ) with hB_def
  set r := 5476 * s with hr_def
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ (sub_pos.2 (by exact_mod_cast hγ))]
    linarith [γ.coe_nonneg]
  have hS : (1 : ℝ) ≤ Fintype.card 𝓢 := by exact_mod_cast Fintype.card_pos
  have hx₀ (j : ℕ) : 0 ≤ windowBound B r j := by
    cases j with
    | zero => rw [windowBound]; linarith
    | succ j => rw [windowBound]; exact Real.sqrt_nonneg _
  -- with one action, the unique policy is greedy for `Q*`
  have hπ (s' : 𝓢) : M.optQValue γ (s', default) = M.optValue γ s' := by
    rw [← iSup_optQValue hγ (fun p ↦ ae_abs_le_of_ae_mem_Icc (hR p)) s', ciSup_unique]
  refine (abs_le_of_dyadic (u := windowBound B r) (K := K)
    (e := fun t q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q)
    (fun t _ q ↦ ?_) (fun j _ t htT hTt hD q ↦ ?_) p).trans
    (Real.le_mul_sqrt_of_le_sqrt_mul_max (r := r) (c := Real.exp 1) (by positivity)
      (by linarith)
      (Real.one_le_exp zero_le_one) hK1 (fun k _ ↦ ?_) ?_)
  · rw [windowBound]
    exact abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ t ω q
  · -- the errors at the late iterations of the window give the bound at `t`
    have hTt' : T ≤ 2 ^ K * t :=
      hTt.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega)))
    obtain ⟨ht2, hTLt⟩ := two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL hTt'
    rw [windowBound]
    refine le_sqrt_mul_max_of_le_tdNoiseVarBound hγ hR hQ₀ hη hlo hhi le_rfl h16 hL1
      (zero_le_one.trans (le_max_left _ _)) (max_one_log_le hS hδ hδ₁ hT8 htT) (by linarith)
      ?_ hBs ht2 htT hTLt hπ (hx₀ j) (fun k hk s' ↦ ?_) q (hgood t htT hTt' q)
    · have hL0 : Real.log T ≠ 0 := by positivity
      have h1γ : (1 : ℝ) - γ ≠ 0 := (sub_pos.2 (by exact_mod_cast hγ)).ne'
      rw [← hs]
      field_simp
    · rw [ciSup_unique, ← hπ s']
      exact hD k hk (s', default)
  · rw [windowBound]
  · rw [windowBound]
    exact hBK

/-- **The sample complexity of synchronous TD learning** [LCCWC24, Theorem 1]. With one action,
rewards in `[0, 1]`, `γ < 1`, an initial value in `[0, 1 / (1 - γ)]`, `ε ∈ (0, 1]`,
`δ ∈ (0, 1)`, `T ≥ 2` and learning rates in the window
`1 / (1 + (1 - γ) T / (16 log² T)) ≤ η t ≤ 1 / (1 + (1 - γ) t / (16 log² T))` for `1 ≤ t ≤ T`,
if `T ≥ 50000 log³ T log (S T / δ) / ((1 - γ) ^ 3 ε ^ 2)`, with `S` the number of states, then
with probability at least `1 - δ` under the generative model, the `T`-th iterate of synchronous TD
learning is within `ε` of the optimal value at every state. The source states it for
`γ ∈ [1 / 2, 1)` and unspecified constants; it holds for every `γ < 1` since the factor
`1 / γ ^ 2` of the sample size in the proof of the source [LCCWC24, (101)] is not needed. -/
theorem measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_window (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) {T : ℕ} (hT : 2 ≤ T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    (hTε : 50000 * Real.log T ^ 3 * Real.log (Fintype.card 𝓢 * T / δ) / ((1 - γ) ^ 3 * ε ^ 2) ≤
      T) :
    streamMeasure M.P {ω | ∃ p, ε <
      |syncQLearning (meanReward M.R) γ η Q₀ T ω p - M.optQValue γ p|} ≤ ENNReal.ofReal δ := by
  classical
  have hS : (1 : ℝ) ≤ Fintype.card 𝓢 := by exact_mod_cast Fintype.card_pos
  obtain ⟨hT8, hL2, h16, hB3, hs₀, hsε, hBs⟩ := sample_size_facts hγ hε hε₁ hδ hδ₁ hS hT hTε
  set S : ℝ := (Fintype.card 𝓢 : ℝ) with hS_def
  set L := Real.log T with hL_def
  set B : ℝ := 1 / (1 - γ) with hB_def
  set s := L ^ 3 * Real.log (S * T / δ) / ((1 - γ) ^ 3 * T) with hs_def
  set β := 2 * (16 * L ^ 2) * L / ((1 - γ) * T) with hβ_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hL1 : 1 ≤ L := by linarith
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ h1γ]
    linarith [γ.coe_nonneg]
  have hs₁ : s ≤ 1 / 50000 :=
    hsε.trans (div_le_div_of_nonneg_right (pow_le_one₀ hε.le hε₁) (by norm_num))
  have hκ : (0 : ℝ) < 16 * L ^ 2 := by positivity
  -- the dyadic windows: `T / 2 ^ (K - j) ≤ t ≤ T`, with `2 ^ K ≤ log T`
  obtain ⟨hK1, hKL, hBK⟩ := dyadic_facts hL2 hB1 (by
    have h := Real.log_le_log (by positivity) hB3
    rw [Real.log_pow] at h
    push_cast at h
    exact h)
  set K := Nat.log 2 ⌊L⌋₊ with hK_def
  -- the learning rates, set to `0` after `T`
  set η' : ℕ → ℝ := fun i ↦ if i ≤ T then η i else 0 with hη'_def
  have hηη' : ∀ i ∈ Ioc 0 T, η i = η' i := fun i hi ↦ by simp [hη'_def, (mem_Ioc.1 hi).2]
  have hlo' : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * L ^ 2)) ≤ η' i := fun i hi ↦
    hηη' i hi ▸ hlo i hi
  have hhi' : ∀ i ∈ Ioc 0 T, η' i ≤ 1 / (1 + (1 - γ) * i / (16 * L ^ 2)) := fun i hi ↦
    hηη' i hi ▸ hhi i hi
  have hη' : ∀ t, η' (t + 1) ∈ Set.Icc (0 : ℝ) 1 := fun t ↦ by
    by_cases ht : t + 1 ≤ T
    · exact mem_Icc_of_window hγ hκ hlo' hhi' (mem_Ioc.2 ⟨t.succ_pos, ht⟩)
    · simp [hη'_def, ht]
  have hQ (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : syncQLearning (meanReward M.R) γ η Q₀ T ω =
      syncQLearning (meanReward M.R) γ η' Q₀ T ω := by
    rw [syncQLearning_congr_learningRate hηη']
  -- the iterations of the windows
  set I := (range (T + 1)).filter fun t ↦ T ≤ 2 ^ K * t with hI_def
  have hI (t : ℕ) (ht : t ∈ I) : t ≤ T ∧ 2 ≤ t ∧ (T : ℝ) ≤ L * t := by
    rw [hI_def, mem_filter, mem_range] at ht
    exact ⟨by omega, two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL ht.2⟩
  -- the event of Freedman's inequality at the iterations of the windows
  set δ' := δ / (2 * S * (T + 1)) with hδ'_def
  have hδ' : 0 < δ' := by positivity
  have hβ₀ : 0 < β := by positivity
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hvb : ∀ t ∈ I, ∀ k < t, η' (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η' i * (1 - γ))) *
      (1 / (1 - γ)) ≤ β * B := fun t ht k hk ↦ by
    have h := mul_prod_le_of_window hγ le_rfl h16 hL1 hlo' hhi' (hI t ht).2.1 (hI t ht).1 hk
      (hI t ht).2.2
    calc η' (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η' i * (1 - γ))) * (1 / (1 - γ))
        = (η' (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η' i * (1 - γ))) * γ * B := by ring
      _ ≤ β * 1 * B := by gcongr
      _ = β * B := by ring
  have hbad := measure_exists_mem_exists_lt_abs_syncQLearning_sub_optQValue_le (M := M)
    (η := η') (Q₀ := Q₀) (C := 1) hγ hR hη' hQ₀ hδ' (by positivity : 0 < β * B) I hvb
  refine (measure_mono fun ω hω ↦ ?_).trans (hbad.trans ?_)
  · by_contra hgood
    obtain ⟨p, hp⟩ := hω
    rw [hQ] at hp
    have h := abs_syncQLearning_sub_optQValue_le_of_window hγ hR hQ₀ hη' hlo' hhi' h16 hL1 hT8 hδ
      hδ₁ hs₀ hs₁ hs_def.symm hBs hK1 hKL hBK (fun t htT hTt q ↦ not_lt.1 fun h ↦
        hgood ⟨t, mem_filter.2 ⟨mem_range.2 (by omega), hTt⟩, q, h⟩) p
    linarith [exp_one_mul_sqrt_le hε (by positivity : (0 : ℝ) ≤ 5476 * s) (by linarith)]
  · -- `2 S #I δ' ≤ δ`
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : (#I : ℝ) ≤ T + 1 := by
      exact_mod_cast (card_filter_le _ _).trans (card_range _).le
    rw [hδ'_def, show (2 * Fintype.card 𝓢 * #I * (δ / (2 * S * (T + 1))) : ℝ) =
      #I / (T + 1) * δ by rw [hS_def]; field_simp]
    exact mul_le_of_le_one_left hδ.le ((div_le_one (by positivity)).2 hcard)

end TD

/-- The total confidence level of the union bound of Q-learning: with
`δ' = δ / (2 S (T + 1) ^ 3)`, `n ≤ T + 1` and `K ≤ T`, `S n δ' + K n (T + 1) S δ' ≤ δ`. -/
private lemma add_mul_le_of_cube {S δ : ℝ} (hS : 0 < S) (hδ : 0 < δ) {T K n : ℕ}
    (hn : (n : ℝ) ≤ T + 1) (hK : (K : ℝ) ≤ T) :
    S * n * (δ / (2 * (S * (T + 1) ^ 2) * (T + 1))) +
      K * (n * ((T + 1) * S * (δ / (2 * (S * (T + 1) ^ 2) * (T + 1))))) ≤ δ := by
  set δ' := δ / (2 * (S * (T + 1) ^ 2) * (T + 1)) with hδ'_def
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hSδ : 0 ≤ S * δ' := by positivity
  have h₁ : S * n * δ' ≤ S * δ' * (T + 1) :=
    calc S * n * δ' = S * δ' * n := by ring
      _ ≤ S * δ' * (T + 1) := mul_le_mul_of_nonneg_left hn hSδ
  have hKn : (K : ℝ) * n ≤ T * (T + 1) := mul_le_mul hK hn (Nat.cast_nonneg _) hT0
  have h₂ : (K : ℝ) * (n * ((T + 1) * S * δ')) ≤ S * δ' * (T + 1) * (T * (T + 1)) :=
    calc (K : ℝ) * (n * ((T + 1) * S * δ')) = S * δ' * (T + 1) * (K * n) := by ring
      _ ≤ S * δ' * (T + 1) * (T * (T + 1)) :=
          mul_le_mul_of_nonneg_left hKn (mul_nonneg hSδ (by positivity))
  have h₃ : S * δ' * (T + 1) + S * δ' * (T + 1) * (T * (T + 1)) ≤ S * δ' * (T + 1) ^ 3 := by
    nlinarith [mul_nonneg hSδ (mul_nonneg hT0 (by positivity : (0 : ℝ) ≤ T + 1))]
  have hkey : S * δ' * (T + 1) ^ 3 = δ / 2 := by
    rw [hδ'_def]
    field_simp
  linarith

/-! ### The sample complexity of Q-learning -/

section QLearning

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Fintype 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Fintype 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ}

omit [Fintype 𝓢] [Fintype 𝓐] in
/-- **The errors of Q-learning on the events of Freedman's inequality** [LCCWC24, Appendix B].
Under the assumptions of
`measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_cube_window`, with learning rates in
`[0, 1]` at every iteration, let `K ≥ 1` with `2 ^ K ≤ log T` and `1 / (1 - γ) ≤ e ^ 2 ^ K`, let
`γ ^ J ≤ 1 / T`, and, at every iteration `t ≤ T` of the dyadic windows, `T ≤ 2 ^ K t`, let
* the lower bound of Freedman's inequality along the state-action kernel of a policy `π` greedy for
  `Q*` hold, with the confidence level `δ / (2 S (T + 1) ^ 3)` and the bound
  `128 log⁴ T / (1 - γ) ^ 2 T` on the increments;
* the upper bound of the windowed recursion with `J` blocks hold, for the bounds
  `windowBound (1 / (1 - γ)) (69696 s) j` on the errors of the late iterations, `j < K`.

Then the error of the `T`-th iterate is at most `e √(69696 s)`, with
`s = log⁴ T log (S (T + 1) ^ 2 T / δ) / ((1 - γ) ^ 4 T)`. -/
private lemma abs_syncQLearning_sub_optQValue_le_of_cube_window [Finite 𝓢] [Finite 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {T : ℕ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (64 * Real.log T ^ 3)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (64 * Real.log T ^ 3)))
    (h64 : 64 * Real.log T ^ 3 ≤ (1 - γ) * T) (hL2 : 2 ≤ Real.log T) (hT8 : 8 ≤ (T : ℝ))
    {δ S : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (hS : 1 ≤ S) {s : ℝ} (hs₁ : s ≤ 1 / 625000)
    (hs : Real.log T ^ 4 * Real.log (S * (T + 1) ^ 2 * T / δ) / ((1 - γ) ^ 4 * T) = s)
    {K J : ℕ} (hK1 : 1 ≤ K) (hKL : ((2 ^ K : ℕ) : ℝ) ≤ Real.log T)
    (hBK : 1 / (1 - (γ : ℝ)) ≤ Real.exp 1 ^ 2 ^ K) (hJ : (γ : ℝ) ^ J ≤ 1 / T)
    {π : 𝓢 → 𝓐} (hπ : ∀ s, M.optQValue γ (s, π s) = M.optValue γ s) {ω : ℕ → 𝓢 × 𝓐 → 𝓢}
    (hlow : ∀ t ≤ T, T ≤ 2 ^ K * t → ∀ q,
      M.optQValue γ q - syncQLearning (meanReward M.R) γ η Q₀ t ω q ≤
        (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (1 / (1 - γ)) +
          (3 * √(tdNoiseVarBound M γ η Q₀
              (M.saKernel (Kernel.deterministic π (measurable_of_finite π))) t ω q *
            max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) /
              (δ / (2 * (S * (T + 1) ^ 2) * (T + 1)))))) +
          2 * (2 * (64 * Real.log T ^ 3) * Real.log T / ((1 - γ) * T) * (1 / (1 - γ))) *
            max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) /
              (δ / (2 * (S * (T + 1) ^ 2) * (T + 1)))))))
    (hup : ∀ j < K, ∀ t ≤ T, T ≤ 2 ^ K * t →
      (∀ k ∈ Ico ((t + 1) / 2) t, ∀ q,
        |syncQLearning (meanReward M.R) γ η Q₀ k ω q - M.optQValue γ q| ≤
          windowBound (1 / (1 - γ)) (69696 * s) j) → ∀ q,
      syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q ≤
        γ ^ J * (1 / (1 - γ)) +
          √(2 * (1 / (T : ℝ) * (1 / (1 - γ)) +
              2 * (2 * (64 * Real.log T ^ 3) * Real.log T / ((1 - γ) * T) * (1 / (1 - γ))) *
                max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) /
                  (δ / (2 * (S * (T + 1) ^ 2) * (T + 1)))))) ^ 2 +
            36 * (2 * (64 * Real.log T ^ 3) * Real.log T / ((1 - γ) * T)) *
              max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) /
                (δ / (2 * (S * (T + 1) ^ 2) * (T + 1))))) * (1 / (1 - γ)) *
              (1 + 4 * γ ^ 2 * windowBound (1 / (1 - γ)) (69696 * s) j)) / (1 - γ))
    (p : 𝓢 × 𝓐) :
    |syncQLearning (meanReward M.R) γ η Q₀ T ω p - M.optQValue γ p| ≤
      Real.exp 1 * √(69696 * s) := by
  set L := Real.log T with hL_def
  set B : ℝ := 1 / (1 - γ) with hB_def
  set r := 69696 * s with hr_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ h1γ]
    linarith
  -- `s ≥ 1 / ((1 - γ) ^ 4 T)`
  have hΛ : 1 ≤ Real.log (S * (T + 1) ^ 2 * T / δ) := by
    refine hL1.trans (Real.log_le_log hT0 ?_)
    rw [le_div_iff₀ hδ]
    nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ S * (T + 1) ^ 2) hT0.le]
  have hs_lb : 1 / ((1 - γ) ^ 4 * T) ≤ s := by
    rw [← hs]
    exact div_le_div_of_nonneg_right (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hΛ)
      (by positivity)
  have hs₀ : 0 ≤ s := le_trans (by positivity) hs_lb
  have hρs : 1 / (T : ℝ) / (1 - γ) ^ 2 ≤ √s := by
    rw [Real.le_sqrt (by positivity) hs₀]
    refine le_trans ?_ hs_lb
    rw [show (1 / (T : ℝ) / (1 - (γ : ℝ)) ^ 2) ^ 2 = 1 / ((1 - (γ : ℝ)) ^ 4 * T ^ 2) by
      field_simp]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))
  have hBsL : B / (T : ℝ) ^ 2 ≤ √(4 * (1 - γ) * s) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    calc (B / (T : ℝ) ^ 2) ^ 2 = 1 / ((1 - (γ : ℝ)) ^ 2 * T ^ 4) := by
          rw [hB_def]
          field_simp
      _ ≤ 4 * (1 - (γ : ℝ)) * (1 / ((1 - (γ : ℝ)) ^ 4 * T)) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have hT4 : (T : ℝ) ≤ T ^ 4 := le_self_pow₀ hT1 (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_left hT4 (by positivity : (0 : ℝ) ≤ (1 - γ) ^ 3),
            mul_le_mul_of_nonneg_left h1γ' (by positivity : (0 : ℝ) ≤ (1 - γ) ^ 3 * T),
            (by positivity : (0 : ℝ) ≤ (1 - γ) ^ 3 * T ^ 4)]
      _ ≤ 4 * (1 - γ) * s := by gcongr
  have hx₀ (j : ℕ) : 0 ≤ windowBound B r j := by
    cases j with
    | zero => rw [windowBound]; linarith
    | succ j => rw [windowBound]; exact Real.sqrt_nonneg _
  have hγ2 : (γ : ℝ) ^ 2 ≤ 1 := pow_le_one₀ γ.coe_nonneg (by exact_mod_cast hγ.le)
  have hRabs (q : 𝓢 × 𝓐) := ae_abs_le_of_ae_mem_Icc (hR q)
  refine (abs_le_of_dyadic (u := windowBound B r) (K := K)
    (e := fun t q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q)
    (fun t _ q ↦ ?_) (fun j hj t htT hTt hD q ↦ ?_) p).trans
    (Real.le_mul_sqrt_of_le_sqrt_mul_max (r := r) (c := Real.exp 1) (by positivity)
      (by linarith)
      (Real.one_le_exp zero_le_one) hK1 (fun k _ ↦ ?_) ?_)
  · rw [windowBound]
    exact abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ t ω q
  · -- the bounds from below and from above at `t`, from the errors at the late iterations
    have hTt' : T ≤ 2 ^ K * t :=
      hTt.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega)))
    obtain ⟨ht2, hTLt⟩ := two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL hTt'
    have hℓ := max_one_log_le (S := S * (T + 1) ^ 2) (t := t) (by nlinarith) hδ hδ₁ hT8 htT
    have hℓ₀ := zero_le_one.trans (le_max_left 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) /
      (δ / (2 * (S * (T + 1) ^ 2) * (T + 1))))))
    have hlower := le_sqrt_mul_max_of_le_tdNoiseVarBound hγ hR hQ₀ hη hlo hhi
      (by nlinarith) h64 hL1 hℓ₀ hℓ (s := 4 * (1 - γ) * s) (by nlinarith)
      (by rw [← hs]; field_simp; ring) hBsL ht2 htT hTLt hπ (hx₀ j) (fun k hk s' ↦ by
        rw [← iSup_optQValue hγ hRabs s']
        exact abs_ciSup_sub_ciSup_le (Set.finite_range _).bddAbove fun a ↦ hD k hk (s', a))
      q (hlow t htT hTt' q)
    have hupper := (hup j hj t htT hTt' hD q).trans (add_sqrt_div_le_sqrt_mul_max h1γ h1γ' hγ2
      (pow_nonneg γ.coe_nonneg J) hJ hρs (by positivity) hℓ₀ hℓ
      (by rw [← hs]; field_simp; ring) (by linarith) (hx₀ j))
    have hLr : √(5476 * (4 * (1 - γ) * s) * max 1 (windowBound B r j)) ≤
        √(r * max 1 (windowBound B r j)) := by
      refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right ?_
        (zero_le_one.trans (le_max_left _ _)))
      rw [hr_def]
      nlinarith
    rw [windowBound]
    exact abs_le.2 ⟨by linarith, hupper⟩
  · rw [windowBound]
  · rw [windowBound]
    exact hBK

/-- **The upper bound on the error of Q-learning with the learning rates of the window**, the
core of [LCCWC24, Lemma 1] with `J = ⌈log T / (1 - γ)⌉` blocks of
`L = ⌈(1 - γ) T / (32 log² T)⌉` iterations. With rewards in `[0, 1]`, `γ < 1`, an initial value in
`[0, 1 / (1 - γ)]`, learning rates in `[0, 1]` at every iteration and in the window
`[1 / (1 + (1 - γ) T / κ), 1 / (1 + (1 - γ) t / κ)]` at the iterations `1 ≤ t ≤ T`, with
`κ = 64 log³ T ≤ (1 - γ) T` and `log T ≥ 2`, let `t ≤ T ≤ log T * t` and let `D` be real. Then
with probability at least `1 - (T + 1) S A δ`, either an error `|Q k - Q*|` of the late iterations
`(t + 1) / 2 ≤ k < t` exceeds `D`, or for every pair `p`,
`Q t p - Q* p ≤ γ ^ J B + √(2 (B / T + 2 β B ℓ) ^ 2 + 36 β ℓ B (1 + 4 γ ^ 2 D)) / (1 - γ)`, with
`B = 1 / (1 - γ)`, `β = 2 κ log T / ((1 - γ) T)`, `ℓ = max 1 (log ((⌈log₄ t⌉ + 1) / δ))`. -/
private lemma measure_exists_lt_syncQLearning_sub_optQValue_le_of_cube_window (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ)))) {T : ℕ}
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (64 * Real.log T ^ 3)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (64 * Real.log T ^ 3)))
    (h64 : 64 * Real.log T ^ 3 ≤ (1 - γ) * T) (hL2 : 2 ≤ Real.log T) {δ D : ℝ} (hδ : 0 < δ)
    {t : ℕ} (htT : t ≤ T) (hTt : (T : ℝ) ≤ Real.log T * t) :
    streamMeasure M.P {ω | (∀ k ∈ Ico ((t + 1) / 2) t, ∀ q,
        |syncQLearning (meanReward M.R) γ η Q₀ k ω q - M.optQValue γ q| ≤ D) ∧
      ∃ p, γ ^ ⌈Real.log T / (1 - γ)⌉₊ * (1 / (1 - γ)) +
          √(2 * (1 / (T : ℝ) * (1 / (1 - γ)) +
              2 * (2 * (64 * Real.log T ^ 3) * Real.log T / ((1 - γ) * T) * (1 / (1 - γ))) *
                max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ))) ^ 2 +
            36 * (2 * (64 * Real.log T ^ 3) * Real.log T / ((1 - γ) * T)) *
              max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ)) * (1 / (1 - γ)) *
              (1 + 4 * γ ^ 2 * D)) / (1 - γ) <
        syncQLearning (meanReward M.R) γ η Q₀ t ω p - M.optQValue γ p} ≤
      ENNReal.ofReal ((T + 1) * (Fintype.card 𝓢 * Fintype.card 𝓐) * δ) := by
  set L := Real.log T with hL_def
  set κ : ℝ := 64 * L ^ 3 with hκ_def
  set β := 2 * κ * L / ((1 - γ) * T) with hβ_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hL0 : 0 < L := by linarith
  have hκ : 0 < κ := by positivity
  have hT0 : (0 : ℝ) < T := by
    by_contra h
    have : (T : ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [this, mul_zero] at h64
    linarith
  obtain ⟨hLb, hLκ, -, hblock⟩ := block_facts hγ hL2 h64
  set Lb := ⌈(1 - γ) * T / (32 * L ^ 2)⌉₊ with hLb_def
  refine (measure_exists_lt_syncQLearning_sub_optQValue_le (M := M) (η := η) (Q₀ := Q₀)
    (C := 1) (b := β * (1 / (1 - γ))) (β := β) (ρ := 1 / (T : ℝ)) (D := D)
    (m := (t + 1) / 2) (L := Lb) (t := t) hγ hR hη hQ₀ hδ (by positivity) hLb
    (hblock t hTt) (fun k hk i hi ↦ ?_) ?_ (fun k hk ↦ ?_)).trans ?_
  · -- the weights of the windows are at most the late learning rates
    obtain ⟨hk₁, hk₂⟩ := mem_Icc.1 hk
    obtain ⟨hi₁, hi₂⟩ := mem_Ioc.1 hi
    have hiT : i ∈ Ioc 0 T := mem_Ioc.2 ⟨by omega, by omega⟩
    have hTi : (T : ℝ) ≤ 2 * L * i := by
      have : (t : ℝ) ≤ 2 * i := by exact_mod_cast (show t ≤ 2 * i by omega)
      nlinarith
    exact learningRateWeight_le_of_window hγ hκ hη hhi hiT hTi
  · rw [mul_assoc]
    exact mul_le_of_le_one_left (by positivity) hγ1
  · -- the contractions of the windows are at most `1 / T`
    obtain ⟨hk₁, hk₂⟩ := mem_Icc.1 hk
    exact prod_one_sub_le_one_div_of_window hγ hκ h64 hlo hhi hLκ (by omega) (by omega)
  · refine ENNReal.ofReal_le_ofReal ?_
    have : ((t + 1 - ((t + 1) / 2 + Lb) : ℕ) : ℝ) ≤ T + 1 := by
      have : t + 1 - ((t + 1) / 2 + Lb) ≤ T + 1 := by omega
      exact_mod_cast this
    calc ((t + 1 - ((t + 1) / 2 + Lb) : ℕ) : ℝ) * Fintype.card 𝓢 * Fintype.card 𝓐 * δ =
        ((t + 1 - ((t + 1) / 2 + Lb) : ℕ) : ℝ) * ((Fintype.card 𝓢 * Fintype.card 𝓐) * δ) := by
          ring
      _ ≤ (T + 1) * ((Fintype.card 𝓢 * Fintype.card 𝓐) * δ) := by gcongr
      _ = (T + 1) * (Fintype.card 𝓢 * Fintype.card 𝓐) * δ := by ring

/-- **The sample complexity of synchronous Q-learning** [LCCWC24, Theorem 2]. With rewards in
`[0, 1]`, `γ < 1`, an initial value in `[0, 1 / (1 - γ)]`, `ε ∈ (0, 1]`, `δ ∈ (0, 1)`, `T ≥ 2`
and learning rates in the window
`1 / (1 + (1 - γ) T / (64 log³ T)) ≤ η t ≤ 1 / (1 + (1 - γ) t / (64 log³ T))` for `1 ≤ t ≤ T`,
if `T ≥ 2500000 log⁴ T log (S A T / δ) / ((1 - γ) ^ 4 ε ^ 2)`, with `S` and `A` the numbers of
states and actions, then with probability at least `1 - δ` under the generative model, the
`T`-th iterate of synchronous Q-learning is within `ε` of the optimal action value at every
state-action pair. The source states it for `γ ∈ [1 / 2, 1)` and unspecified constants; it holds
for every `γ < 1` since the comparison with a common supersolution of the upper bound
(`LMLExplore.ReinforcementLearning.measure_exists_lt_syncQLearning_sub_optQValue_le`) and the
bound on the quadratic variation of the lower bound
(`LMLExplore.ReinforcementLearning.tdNoiseVarBound_le`) have no factor `1 / γ ^ 2`. -/
theorem measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_cube_window (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {ε δ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) {T : ℕ} (hT : 2 ≤ T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (64 * Real.log T ^ 3)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (64 * Real.log T ^ 3)))
    (hTε : 2500000 * Real.log T ^ 4 *
        Real.log (Fintype.card 𝓢 * Fintype.card 𝓐 * T / δ) / ((1 - γ) ^ 4 * ε ^ 2) ≤ T) :
    streamMeasure M.P {ω | ∃ p, ε <
      |syncQLearning (meanReward M.R) γ η Q₀ T ω p - M.optQValue γ p|} ≤ ENNReal.ofReal δ := by
  classical
  set S : ℝ := Fintype.card 𝓢 * Fintype.card 𝓐 with hS_def
  have hS : (1 : ℝ) ≤ S := by
    rw [hS_def]
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Fintype.card_pos)
      (by exact_mod_cast Fintype.card_pos)
  obtain ⟨hT8, hL2, h64, hB3, hsε⟩ := sample_size_facts_of_cube hγ hε hε₁ hδ hδ₁ hS hT hTε
  set L := Real.log T with hL_def
  set B : ℝ := 1 / (1 - γ) with hB_def
  set κ : ℝ := 64 * L ^ 3 with hκ_def
  set β := 2 * κ * L / ((1 - γ) * T) with hβ_def
  set s := L ^ 4 * Real.log (S * (T + 1) ^ 2 * T / δ) / ((1 - γ) ^ 4 * T) with hs_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hT0 : (0 : ℝ) < T := by linarith
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ h1γ]
    linarith [γ.coe_nonneg]
  have hκ : 0 < κ := by positivity
  have h16 : 16 * L ^ 2 ≤ κ := by nlinarith
  have hβ₀ : 0 < β := by positivity
  have hsε' : s ≤ ε ^ 2 / 625000 :=
    calc s = L ^ 4 * Real.log (S * (T + 1) ^ 2 * T / δ) / ((1 - γ) ^ 4 * T) := hs_def
      _ ≤ L ^ 4 * (4 * Real.log (S * T / δ)) / ((1 - γ) ^ 4 * T) := by
          gcongr
          exact log_mul_sq_le hS hδ hδ₁ hT8
      _ = 4 * (L ^ 4 * Real.log (S * T / δ) / ((1 - γ) ^ 4 * T)) := by ring
      _ ≤ 4 * (ε ^ 2 / 2500000) := by gcongr
      _ = ε ^ 2 / 625000 := by ring
  have hs₁ : s ≤ 1 / 625000 :=
    hsε'.trans (div_le_div_of_nonneg_right (pow_le_one₀ hε.le hε₁) (by norm_num))
  have hs₀ : 0 ≤ s := by
    have : 0 ≤ Real.log (S * (T + 1) ^ 2 * T / δ) := Real.log_nonneg (by
      rw [le_div_iff₀ hδ]
      nlinarith [mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ S * (T + 1) ^ 2) hT0.le])
    positivity
  -- the dyadic windows: `T / 2 ^ (K - j) ≤ t ≤ T`, with `2 ^ K ≤ log T`
  obtain ⟨hK1, hKL, hBK⟩ := dyadic_facts hL2 hB1 (by
    have h := Real.log_le_log (by positivity) hB3
    rw [Real.log_pow] at h
    push_cast at h
    exact h)
  set K := Nat.log 2 ⌊L⌋₊ with hK_def
  have hKT : (K : ℝ) ≤ T := by
    have hK : K < 2 ^ K := Nat.lt_two_pow_self
    have : ((2 ^ K : ℕ) : ℝ) ≤ T := hKL.trans (by
      linarith [Real.log_le_sub_one_of_pos hT0])
    exact_mod_cast hK.le.trans (by exact_mod_cast this)
  -- the number of blocks of the windowed recursion
  have hJ := (block_facts hγ hL2 h64).2.2.1
  set J := ⌈L / (1 - γ)⌉₊ with hJ_def
  -- the learning rates, set to `0` after `T`
  set η' : ℕ → ℝ := fun i ↦ if i ≤ T then η i else 0 with hη'_def
  have hηη' : ∀ i ∈ Ioc 0 T, η i = η' i := fun i hi ↦ by simp [hη'_def, (mem_Ioc.1 hi).2]
  have hlo' : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η' i := fun i hi ↦
    hηη' i hi ▸ hlo i hi
  have hhi' : ∀ i ∈ Ioc 0 T, η' i ≤ 1 / (1 + (1 - γ) * i / κ) := fun i hi ↦
    hηη' i hi ▸ hhi i hi
  have hη' : ∀ t, η' (t + 1) ∈ Set.Icc (0 : ℝ) 1 := fun t ↦ by
    by_cases ht : t + 1 ≤ T
    · exact mem_Icc_of_window hγ hκ hlo' hhi' (mem_Ioc.2 ⟨t.succ_pos, ht⟩)
    · simp [hη'_def, ht]
  have hQ (ω : ℕ → 𝓢 × 𝓐 → 𝓢) : syncQLearning (meanReward M.R) γ η Q₀ T ω =
      syncQLearning (meanReward M.R) γ η' Q₀ T ω := by
    rw [syncQLearning_congr_learningRate hηη']
  -- a policy greedy for `Q*`
  choose π hπ using fun s ↦ exists_eq_ciSup_of_finite (f := fun a ↦ M.optQValue γ (s, a))
  have hπ' (s : 𝓢) : M.optQValue γ (s, π s) = M.optValue γ s :=
    (hπ s).trans (iSup_optQValue hγ (fun p ↦ ae_abs_le_of_ae_mem_Icc (hR p)) s)
  -- the iterations of the windows
  set I := (range (T + 1)).filter fun t ↦ T ≤ 2 ^ K * t with hI_def
  have hI (t : ℕ) (ht : t ∈ I) : t ≤ T ∧ 2 ≤ t ∧ (T : ℝ) ≤ L * t := by
    rw [hI_def, mem_filter, mem_range] at ht
    exact ⟨by omega, two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL ht.2⟩
  have hcard : (#I : ℝ) ≤ T + 1 := by
    exact_mod_cast (card_filter_le _ _).trans (card_range _).le
  -- the events of Freedman's inequality at the iterations of the windows
  set δ' := δ / (2 * (S * (T + 1) ^ 2) * (T + 1)) with hδ'_def
  have hδ' : 0 < δ' := by positivity
  have hvb : ∀ t ∈ I, ∀ k < t, η' (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η' i * (1 - γ))) *
      (1 / (1 - γ)) ≤ β * B := fun t ht k hk ↦ by
    have h := mul_prod_le_of_window hγ h16 h64 hL1 hlo' hhi' (hI t ht).2.1 (hI t ht).1 hk
      (hI t ht).2.2
    calc η' (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η' i * (1 - γ))) * (1 / (1 - γ))
        = (η' (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η' i * (1 - γ))) * γ * B := by ring
      _ ≤ β * 1 * B := by gcongr
      _ = β * B := by ring
  have hlow := measure_exists_mem_exists_lt_optQValue_sub_syncQLearning_le (M := M)
    (η := η') (Q₀ := Q₀) (C := 1) hγ hR hη' hQ₀ hπ' hδ' (by positivity : 0 < β * B) I hvb
  set E : ℕ → ℕ → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun j t ↦ {ω |
    (∀ k ∈ Ico ((t + 1) / 2) t, ∀ q,
      |syncQLearning (meanReward M.R) γ η' Q₀ k ω q - M.optQValue γ q| ≤
        windowBound B (69696 * s) j) ∧
    ∃ p, γ ^ J * (1 / (1 - γ)) +
        √(2 * (1 / (T : ℝ) * (1 / (1 - γ)) +
            2 * (β * B) * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ'))) ^ 2 +
          36 * β * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ')) * (1 / (1 - γ)) *
            (1 + 4 * γ ^ 2 * windowBound B (69696 * s) j)) / (1 - γ) <
      syncQLearning (meanReward M.R) γ η' Q₀ t ω p - M.optQValue γ p}
  have hup (j t : ℕ) (ht : t ∈ I) :
      streamMeasure M.P (E j t) ≤ ENNReal.ofReal ((T + 1) * S * δ') :=
    measure_exists_lt_syncQLearning_sub_optQValue_le_of_cube_window hγ hR hη' hQ₀ hlo' hhi' h64
      hL2 hδ' (hI t ht).1 (hI t ht).2.2
  refine (measure_mono fun ω hω ↦ ?_).trans ((measure_union_le _ _).trans
    ((add_le_add hlow ((measure_biUnion_finset_le (range K) _).trans (sum_le_sum fun j _ ↦
      (measure_biUnion_finset_le I _).trans (sum_le_sum fun t ht ↦ hup j t ht)))).trans ?_))
  · -- on the events of Freedman's inequality, the error is at most `e √(69696 s) ≤ ε`
    by_contra hgood
    obtain ⟨p, hp⟩ := hω
    rw [hQ] at hp
    have hmem (t : ℕ) (htT : t ≤ T) (hTt : T ≤ 2 ^ K * t) : t ∈ I :=
      mem_filter.2 ⟨mem_range.2 (by omega), hTt⟩
    have h := abs_syncQLearning_sub_optQValue_le_of_cube_window hγ hR hQ₀ hη' hlo' hhi' h64 hL2
      hT8 hδ hδ₁ hS hs₁ hs_def.symm hK1 hKL hBK hJ hπ'
      (fun t htT hTt q ↦ not_lt.1 fun h ↦ hgood (Or.inl ⟨t, hmem t htT hTt, q, h⟩))
      (fun j hj t htT hTt hD q ↦ not_lt.1 fun h ↦ hgood (Or.inr (Set.mem_iUnion₂.2
        ⟨j, mem_range.2 hj, Set.mem_iUnion₂.2 ⟨t, hmem t htT hTt, hD, q, h⟩⟩))) p
    linarith [exp_one_mul_sqrt_le hε (by positivity : (0 : ℝ) ≤ 69696 * s) (by linarith)]
  · -- `S #I δ' + K #I (T + 1) S δ' ≤ (T + 1) ^ 3 S δ' = δ / 2`
    simp only [sum_const, card_range]
    rw [← ENNReal.ofReal_nsmul, ← ENNReal.ofReal_nsmul,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [nsmul_eq_mul]
    exact add_mul_le_of_cube (by positivity) hδ hcard hKT

end QLearning

end LMLExplore.ReinforcementLearning
