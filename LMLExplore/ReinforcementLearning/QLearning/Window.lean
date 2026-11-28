/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.ReinforcementLearning.TemporalDifference.Synchronous
import LMLExplore.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The rescaled linear learning rates and the dyadic windows of synchronous Q-learning

The sample complexity bounds of synchronous Q-learning and synchronous TD learning
[LCCWC24, Theorems 1 and 2] take `T ≥ 2` iterations with learning rates in a rescaled linear
window

`1 / (1 + (1 - γ) T / κ) ≤ η t ≤ 1 / (1 + (1 - γ) t / κ)`, `1 ≤ t ≤ T`,

with `κ = 16 log² T` and `κ = 64 log³ T`. This file gathers the steps their proofs share
[LCCWC24, Appendices B and C]:
* the estimates on the learning rates of the window, for any `16 log² T ≤ κ ≤ (1 - γ) T`: the
  products `∏ (1 - η i (1 - γ))` decay geometrically, and the late learning rates and weights are
  of order `κ log T / ((1 - γ) T)`;
* the consequences of the sample size condition
  `T ≥ C log^n T log (S T / δ) / ((1 - γ) ^ n ε ^ 2)`;
* the lower bound of one step of the recursion of the errors, along the state-action kernel of a
  policy greedy for `Q*`, from the bound on the quadratic variation of the noise in terms of the
  late errors (`LMLExplore.ReinforcementLearning.tdNoiseVarBound_le`);
* the induction over the dyadic windows `T / 2 ^ (K - j) ≤ t ≤ T`: when the bound `x j` on the
  errors of the late iterations `t / 2 ≤ k < t` gives the bound `x (j + 1) = √(r max 1 (x j))` at
  `t`, from `x 0 = 1 / (1 - γ)`, the errors reach `e √r` after `K ≈ log₂ log T` windows
  (`Real.le_mul_sqrt_of_le_sqrt_mul_max` [LCCWC24, Appendix B.4]).

## Main statements

* `LMLExplore.ReinforcementLearning.le_sqrt_mul_max_of_le_tdNoiseVarBound`: the lower bound of one
  step of the recursion of the errors [LCCWC24, (121)].
* `LMLExplore.ReinforcementLearning.abs_le_of_dyadic`: the induction over the dyadic windows.
* `LMLExplore.ReinforcementLearning.windowBound_le`: the final accuracy of the dyadic windows.

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
lemma mem_Icc_of_window (hγ : γ < 1) (hκ : 0 < κ)
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
lemma learningRateWeight_le_of_window (hγ : γ < 1) (hκ : 0 < κ)
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
lemma mul_prod_le_of_window (hγ : γ < 1) (h16 : 16 * Real.log T ^ 2 ≤ κ)
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
lemma prod_one_sub_le_one_div_of_window (hγ : γ < 1) (hκ : 0 < κ)
    (hT : κ ≤ (1 - γ) * T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {L k : ℕ} (hLκ : 2 * (1 - γ) * T * Real.log T ≤ κ * L) (hLk : L ≤ k) (hkT : k ≤ T) :
    ∏ j ∈ Ioc (k - L) k, (1 - η j) ≤ 1 / (T : ℝ) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hT0 : (0 : ℝ) < T := pos_of_mul_pos_right (hκ.trans_le hT) h1γ.le
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

/-- The learning rates of the window, set to `0` after `T`, agree with `η` at the iterations
`1 ≤ i ≤ T`, so that they are in the window there, and lie in `[0, 1]` at every iteration. -/
lemma exists_eq_mem_Icc_of_window (hγ : γ < 1) (hκ : 0 < κ)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ)) :
    ∃ η' : ℕ → ℝ, (∀ i ∈ Ioc 0 T, η i = η' i) ∧
      (∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η' i) ∧
      (∀ i ∈ Ioc 0 T, η' i ≤ 1 / (1 + (1 - γ) * i / κ)) ∧
      ∀ t, η' (t + 1) ∈ Set.Icc (0 : ℝ) 1 := by
  set η' : ℕ → ℝ := fun i ↦ if i ≤ T then η i else 0 with hη'_def
  have hηη' : ∀ i ∈ Ioc 0 T, η i = η' i := fun i hi ↦ by simp [hη'_def, (mem_Ioc.1 hi).2]
  have hlo' : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η' i := fun i hi ↦
    hηη' i hi ▸ hlo i hi
  have hhi' : ∀ i ∈ Ioc 0 T, η' i ≤ 1 / (1 + (1 - γ) * i / κ) := fun i hi ↦
    hηη' i hi ▸ hhi i hi
  refine ⟨η', hηη', hlo', hhi', fun t ↦ ?_⟩
  by_cases ht : t + 1 ≤ T
  · exact mem_Icc_of_window hγ hκ hlo' hhi' (mem_Ioc.2 ⟨t.succ_pos, ht⟩)
  · simp [hη'_def, ht]

end Schedule

/-! ### The logarithmic factor -/

/-- The logarithmic factor of Freedman's inequality at an iteration `t ≤ T`, for the confidence
level `δ / (2 S (T + 1))`, is at most `3 log (S T / δ)`, for `T ≥ 8`, `S ≥ 1` and `δ ∈ (0, 1)`. -/
lemma max_one_log_ceil_logb_le {S δ : ℝ} {t T : ℕ} (hS : 1 ≤ S) (hδ : 0 < δ) (hδ₁ : δ < 1)
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
`T ≥ C log^n T log (S T / δ) / ((1 - γ) ^ n ε ^ 2)`, for `n ≥ 3` and `C ≥ 8 * 2 ^ (n + 1)`, used
in the proofs: `T ≥ 8`, `log T ≥ 2`, `log T ≤ log (S T / δ)`, `C log^(n - 1) T ≤ (1 - γ) T`,
`(1 / (1 - γ)) ^ 3 ≤ T` and `log^n T log (S T / δ) / ((1 - γ) ^ n T) ≤ ε ^ 2 / C`. -/
lemma eight_le_and_le_of_sample_size {γ : ℝ≥0} (hγ : γ < 1) {ε δ S : ℝ} (hε : 0 < ε)
    (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hδ₁ : δ < 1) (hS : 1 ≤ S) {n : ℕ} (hn : 3 ≤ n) {C : ℝ}
    (hC : 8 * 2 ^ (n + 1) ≤ C) {T : ℕ} (hT : 2 ≤ T)
    (hTε : C * Real.log T ^ n * Real.log (S * T / δ) / ((1 - γ) ^ n * ε ^ 2) ≤ T) :
    8 ≤ (T : ℝ) ∧ 2 ≤ Real.log T ∧ Real.log T ≤ Real.log (S * T / δ) ∧
      C * Real.log T ^ (n - 1) ≤ (1 - γ) * T ∧ (1 / (1 - (γ : ℝ))) ^ 3 ≤ T ∧
      Real.log T ^ n * Real.log (S * T / δ) / ((1 - γ) ^ n * T) ≤ ε ^ 2 / C := by
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
  have h2n : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hC1 : 1 ≤ C := by linarith
  -- the sample size condition: `C L ^ n Λ ≤ (1 - γ) ^ n ε ^ 2 T`
  have hcond : C * L ^ n * Λ ≤ (1 - γ) ^ n * ε ^ 2 * T := by
    rwa [div_le_iff₀ (by positivity), mul_comm (T : ℝ)] at hTε
  have h1γn : (1 - (γ : ℝ)) ^ n ≤ 1 := pow_le_one₀ h1γ.le h1γ'
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε₁
  have hcondT : C * L ^ n * Λ ≤ (1 - γ) ^ n * T :=
    hcond.trans (by nlinarith [mul_le_mul_of_nonneg_left hε2 (by positivity :
      (0 : ℝ) ≤ (1 - γ) ^ n * T)])
  have hsε : L ^ n * Λ / ((1 - γ) ^ n * T) ≤ ε ^ 2 / C := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    linarith
  -- `T ≥ 8`, since `T ≥ C L ^ (n + 1)` with `L ≥ log 2 ≥ 1 / 2`; hence `log T ≥ 2`
  have hL2' : 1 / 2 ≤ L := by
    have := Real.log_le_log (by norm_num) hT2
    linarith [Real.log_two_gt_d9]
  have hT8 : 8 ≤ (T : ℝ) := by
    have h1 : C * L ^ (n + 1) ≤ T := by
      have := mul_le_mul_of_nonneg_left hΛL (by positivity : (0 : ℝ) ≤ C * L ^ n)
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right h1γn hT0.le]
    have h2 : (1 / 2 : ℝ) ^ (n + 1) ≤ L ^ (n + 1) := pow_le_pow_left₀ (by norm_num) hL2' _
    have h3 : 8 * 2 ^ (n + 1) * (1 / 2 : ℝ) ^ (n + 1) = 8 := by
      rw [mul_assoc, ← mul_pow]
      norm_num
    nlinarith [mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ (1 / 2) ^ (n + 1)),
      mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ C)]
  have hL2 : 2 ≤ L := by
    have h8 := Real.log_le_log (by norm_num) hT8
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [Real.log_two_gt_d9]
  have hL1 : 1 ≤ L := by linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hLΛ : 1 ≤ L ^ n * Λ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1) hΛ1
  have hCL : C * L ^ (n - 1) ≤ (1 - γ) * T := by
    have hn1 : (1 - (γ : ℝ)) ^ n ≤ 1 - γ := by
      simpa using pow_le_pow_of_le_one h1γ.le h1γ' (show 1 ≤ n by omega)
    have hLn : L ^ (n - 1) ≤ L ^ n * Λ :=
      (pow_le_pow_right₀ hL1 (Nat.sub_le n 1)).trans (le_mul_of_one_le_right (by positivity) hΛ1)
    nlinarith [mul_le_mul_of_nonneg_right hn1 hT0.le,
      mul_le_mul_of_nonneg_left hLn (by linarith : (0 : ℝ) ≤ C)]
  have hB3 : (1 / (1 - (γ : ℝ))) ^ 3 ≤ T := by
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
    have h3 : (1 - (γ : ℝ)) ^ n ≤ (1 - γ) ^ 3 := pow_le_pow_of_le_one h1γ.le h1γ' hn
    have h1 : 1 ≤ C * (L ^ n * Λ) := one_le_mul_of_one_le_of_one_le hC1 hLΛ
    nlinarith [mul_le_mul_of_nonneg_right h3 hT0.le]
  exact ⟨hT8, hL2, hΛL, hCL, hB3, hsε⟩

/-- The contraction of the initial error is below the noise level: for `T ≥ 1` and `X ≥ 1`,
`1 / ((1 - γ) T ^ 2) ≤ √(X / ((1 - γ) ^ 3 T))`. -/
lemma one_div_one_sub_div_sq_le_sqrt {γ : ℝ≥0} (hγ : γ < 1) {T : ℕ} (hT : 1 ≤ (T : ℝ)) {X : ℝ}
    (hX : 1 ≤ X) : 1 / (1 - (γ : ℝ)) / (T : ℝ) ^ 2 ≤ √(X / ((1 - γ) ^ 3 * T)) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hT0 : (0 : ℝ) < T := by linarith
  rw [Real.le_sqrt (by positivity) (div_nonneg (by linarith) (by positivity))]
  have h₁ : (1 / (1 - (γ : ℝ)) / (T : ℝ) ^ 2) ^ 2 = 1 / ((1 - γ) ^ 2 * T ^ 4) := by
    field_simp
  have h₂ : (1 - (γ : ℝ)) ^ 3 * T ≤ (1 - γ) ^ 2 * T ^ 4 :=
    mul_le_mul (pow_le_pow_of_le_one h1γ.le h1γ' (by norm_num))
      (le_self_pow₀ hT (by norm_num)) hT0.le (by positivity)
  rw [h₁]
  exact (one_div_le_one_div_of_le (by positivity) h₂).trans
    (div_le_div_of_nonneg_right hX (by positivity))

/-! ### The dyadic windows -/

/-- The dyadic windows: for `log T ≥ 2` and `B ≥ 1` with `3 log B ≤ log T`, the number
`K = log₂ ⌊log T⌋` of windows satisfies `1 ≤ K`, `2 ^ K ≤ log T` and `B ≤ e ^ 2 ^ K`. -/
lemma one_le_natLog_floor_and_two_pow_le {L B : ℝ} (hL2 : 2 ≤ L) (hB1 : 1 ≤ B)
    (hB3 : 3 * Real.log B ≤ L) :
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
lemma two_le_and_le_log_mul_of_le_two_pow_mul {T K t : ℕ} (hT8 : 8 ≤ (T : ℝ))
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

/-- The iterations of the dyadic windows and the bound on their increments: for `T ≥ 8`,
`2 ^ K ≤ log T` and learning rates in the window with `16 log² T ≤ κ ≤ (1 - γ) T`, an iteration
`t ≤ T` with `T ≤ 2 ^ K t` satisfies `2 ≤ t` and `T ≤ log T * t`, and the increments
`η (k + 1) γ ρ (k + 1) t / (1 - γ)`, `k < t`, of the noise are at most
`2 κ log T / ((1 - γ) T) * (1 / (1 - γ))`. -/
lemma le_and_mul_prod_le_of_mem_filter {γ : ℝ≥0} (hγ : γ < 1) {η : ℕ → ℝ} {T K : ℕ} {κ : ℝ}
    (h16 : 16 * Real.log T ^ 2 ≤ κ) (hκT : κ ≤ (1 - γ) * T) (hT8 : 8 ≤ (T : ℝ))
    (hKL : ((2 ^ K : ℕ) : ℝ) ≤ Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / κ) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / κ))
    {t : ℕ} (ht : t ∈ (range (T + 1)).filter fun t ↦ T ≤ 2 ^ K * t) :
    (t ≤ T ∧ 2 ≤ t ∧ (T : ℝ) ≤ Real.log T * t) ∧ ∀ k < t,
      η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (1 / (1 - γ)) ≤
        2 * κ * Real.log T / ((1 - γ) * T) * (1 / (1 - γ)) := by
  rw [mem_filter, mem_range] at ht
  obtain ⟨ht2, hTt⟩ := two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL ht.2
  have hL1 : 1 ≤ Real.log T := le_trans (by exact_mod_cast Nat.one_le_two_pow) hKL
  refine ⟨⟨by omega, ht2, hTt⟩, fun k hk ↦ ?_⟩
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hβ₀ : 0 ≤ 2 * κ * Real.log T / ((1 - γ) * T) :=
    div_nonneg (by nlinarith) (by positivity)
  have h := mul_prod_le_of_window hγ h16 hκT hL1 hlo hhi ht2 (by omega) hk hTt
  calc η (k + 1) * γ * (∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * (1 / (1 - γ))
      = (η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) * γ * (1 / (1 - γ)) := by ring
    _ ≤ 2 * κ * Real.log T / ((1 - γ) * T) * 1 * (1 / (1 - γ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul h hγ1 γ.coe_nonneg hβ₀) (by positivity)
    _ = 2 * κ * Real.log T / ((1 - γ) * T) * (1 / (1 - γ)) := by ring

/-- The final accuracy: if `0 ≤ r` and `7.39 r ≤ ε ^ 2`, then `e √r ≤ ε`. -/
private lemma exp_one_mul_sqrt_le {r ε : ℝ} (hε : 0 < ε) (hr₀ : 0 ≤ r)
    (hrε : 7.39 * r ≤ ε ^ 2) : Real.exp 1 * √r ≤ ε := by
  have he := Real.exp_one_lt_d9
  have he₀ := Real.exp_pos 1
  rw [show Real.exp 1 * √r = √(Real.exp 1 ^ 2 * r) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he₀.le], Real.sqrt_le_left hε.le]
  have he2 : Real.exp 1 ^ 2 ≤ 7.39 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right he2 hr₀]

/-- **The final accuracy of the dyadic windows** [LCCWC24, Appendix B.4]: for `K ≥ 1`,
`B ≤ e ^ 2 ^ K`, `0 ≤ r` and `7.39 r ≤ ε ^ 2` with `ε ∈ (0, 1]`, the bound of the `K`-th window
is `windowBound B r K ≤ e √r ≤ ε`. -/
lemma windowBound_le {B r ε : ℝ} {K : ℕ} (hK : 1 ≤ K) (hB : B ≤ Real.exp 1 ^ 2 ^ K)
    (hr₀ : 0 ≤ r) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hrε : 7.39 * r ≤ ε ^ 2) :
    Real.windowBound B r K ≤ ε := by
  have hr₁ : r ≤ 1 := by nlinarith [pow_le_one₀ (n := 2) hε.le hε₁]
  exact (Real.windowBound_le_mul_sqrt hr₀ hr₁ (Real.one_le_exp zero_le_one) hK hB).trans
    (exp_one_mul_sqrt_le hε hr₀ hrε)

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
lemma le_sqrt_mul_max_of_le_tdNoiseVarBound (hγ : γ < 1)
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
lemma abs_le_of_dyadic {ι : Type*} {e : ℕ → ι → ℝ} {u : ℕ → ℝ} {T K : ℕ}
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

end LMLExplore.ReinforcementLearning
