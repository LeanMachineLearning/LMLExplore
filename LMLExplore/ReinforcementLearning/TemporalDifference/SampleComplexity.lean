/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.Synchronous
import LMLExplore.Analysis.Real.Sqrt
import LMLExplore.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The sample complexity of synchronous TD learning

Synchronous TD learning on the generative model is synchronous Q-learning
(`LMLExplore.ReinforcementLearning.syncQLearning`) with one action. With rewards in `[0, 1]`, an
initial value in `[0, 1 / (1 - γ)]`, `T ≥ 2` iterations and learning rates in the rescaled linear
window

`1 / (1 + (1 - γ) T / (16 log² T)) ≤ η t ≤ 1 / (1 + (1 - γ) t / (16 log² T))`, `1 ≤ t ≤ T`,

it is `ε`-accurate in the sup norm with probability at least `1 - δ` as soon as
`T ≥ 50000 log³ T log (S T / δ) / ((1 - γ) ^ 3 ε ^ 2)`, for `ε ∈ (0, 1]`, where `S` is the number
of states [LCCWC24, Theorem 1]. The constant learning rate `1 / (1 + (1 - γ) T / (16 log² T))` is
in the window.

The proof follows [LCCWC24, Appendix C]. With high probability, by Freedman's inequality
(`LMLExplore.ReinforcementLearning.measure_exists_mem_exists_lt_abs_syncQLearning_sub_optQValue_le`)
and the bound on the quadratic variation of the noise in terms of the late errors
(`LMLExplore.ReinforcementLearning.tdNoiseVarBound_le`), the error of every iterate
`t ≥ T / log T` satisfies `‖Δ t‖ ≤ √(r max 1 (max_{t / 2 ≤ k < t} ‖Δ k‖))`, with
`r = 5476 log³ T log (S T / δ) / ((1 - γ) ^ 3 T)`. On the dyadic windows
`T / 2 ^ (K - j) ≤ t ≤ T`, the bounds `x (j + 1) = √(r max 1 (x j))` from `x 0 = 1 / (1 - γ)` reach
`e √r` after `K ≈ log₂ log T` windows (`Real.le_mul_sqrt_of_le_sqrt_mul_max`
[LCCWC24, Appendix B.4]).

The bound improves the source in two ways: the factor `1 / γ ^ 2` of [LCCWC24, (101)] is not
needed, since the resolvent of the one-step variances of the optimal value satisfies
`γ ^ 2 (I - γ P)⁻¹ Var_P(V*) ≤ 1 / (1 - γ) ^ 2`
(`LMLExplore.ReinforcementLearning.mul_integral_variance_optValue_le`), so that the statement
holds for every `γ < 1`; and the constants are explicit.

## Main statements

* `LMLExplore.ReinforcementLearning.measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_window`:
  the sample complexity of synchronous TD learning [LCCWC24, Theorem 1].

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

variable {γ : ℝ≥0} {η : ℕ → ℝ} {T : ℕ}

/-- The learning rates of the window lie in `[0, 1]`. -/
private lemma mem_Icc_of_window (hγ : γ < 1)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    {i : ℕ} (hi : i ∈ Ioc 0 T) : η i ∈ Set.Icc (0 : ℝ) 1 := by
  have h1γ : (0 : ℝ) ≤ 1 - γ := sub_nonneg.2 (by exact_mod_cast hγ.le)
  refine ⟨le_trans (by positivity) (hlo i hi), (hhi i hi).trans ?_⟩
  rw [div_le_one (by positivity)]
  exact le_add_of_nonneg_right (by positivity)

/-- The lower end of the window makes every factor `1 - η i (1 - γ)` at most `1 - 8 log² T / T`,
once `16 log² T ≤ (1 - γ) T`. -/
private lemma le_mul_one_sub_of_window (hγ : γ < 1) (hT : 16 * Real.log T ^ 2 ≤ (1 - γ) * T)
    (hL : 0 < Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    {i : ℕ} (hi : i ∈ Ioc 0 T) : 8 * Real.log T ^ 2 / T ≤ η i * (1 - γ) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hT0 : (0 : ℝ) < T := by
    have := (mem_Ioc.1 hi).1
    have := (mem_Ioc.1 hi).2
    exact_mod_cast (show 0 < T by omega)
  set X := (1 - (γ : ℝ)) * T / (16 * Real.log T ^ 2)
  have hX : 1 ≤ X := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h₁ : 1 / (2 * X) ≤ η i :=
    (one_div_le_one_div_of_le (by positivity) (by linarith)).trans (hlo i hi)
  calc 8 * Real.log T ^ 2 / T = 1 / (2 * X) * (1 - γ) := by
        simp only [X]
        field_simp
        ring
    _ ≤ η i * (1 - γ) := mul_le_mul_of_nonneg_right h₁ h1γ.le

/-- The products `ρ k t = ∏_{i = k + 1}^t (1 - η i (1 - γ))` of the window decay geometrically:
`ρ k t ≤ exp (-8 log² T (t - k) / T)`. -/
private lemma prod_le_exp_of_window (hγ : γ < 1) (hT : 16 * Real.log T ^ 2 ≤ (1 - γ) * T)
    (hL : 0 < Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    {k t : ℕ} (htT : t ≤ T) :
    ∏ i ∈ Ioc k t, (1 - η i * (1 - γ)) ≤
      Real.exp (-(8 * Real.log T ^ 2 / T * (t - k : ℕ))) := by
  have hsub : Ioc k t ⊆ Ioc 0 T := Ioc_subset_Ioc (Nat.zero_le _) htT
  refine (Real.prod_one_sub_le_exp_neg_sum fun i hi ↦ ?_).trans (Real.exp_le_exp.2 ?_)
  · have hηi := mem_Icc_of_window hγ hlo hhi (hsub hi)
    have h1γ : (0 : ℝ) ≤ 1 - γ := sub_nonneg.2 (by exact_mod_cast hγ.le)
    have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
    nlinarith [hηi.1, hηi.2]
  · rw [neg_le_neg_iff, ← Nat.card_Ioc k t, mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun i hi ↦ le_mul_one_sub_of_window hγ hT hL hlo (hsub hi)

/-- The early products are small: for `T ≤ log T * t` and `t ≤ 4 (t - k)`, `ρ k t ≤ 1 / T ^ 2`. -/
private lemma prod_le_one_div_sq_of_window (hγ : γ < 1)
    (hT : 16 * Real.log T ^ 2 ≤ (1 - γ) * T) (hL : 0 < Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    {k t : ℕ} (htT : t ≤ T) (hTt : (T : ℝ) ≤ Real.log T * t) (hkt : t ≤ 4 * (t - k)) :
    ∏ i ∈ Ioc k t, (1 - η i * (1 - γ)) ≤ 1 / (T : ℝ) ^ 2 := by
  have hT0 : (0 : ℝ) < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · simp [h] at hL
    · exact_mod_cast h
  refine (prod_le_exp_of_window hγ hT hL hlo hhi htT).trans ?_
  have hkt' : (t : ℝ) ≤ 4 * (t - k : ℕ) := by exact_mod_cast hkt
  -- the exponent is at least `2 log² T t / T ≥ 2 log T`
  have h₁ : 2 * Real.log T ≤ 8 * Real.log T ^ 2 / T * (t - k : ℕ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hT0]
    nlinarith [mul_le_mul_of_nonneg_left hkt' (le_of_lt (mul_pos (mul_pos two_pos hL) hL)),
      mul_le_mul_of_nonneg_left hTt (le_of_lt (mul_pos two_pos hL))]
  calc Real.exp (-(8 * Real.log T ^ 2 / T * (t - k : ℕ))) ≤ Real.exp (-(2 * Real.log T)) :=
        Real.exp_le_exp.2 (neg_le_neg h₁)
    _ = 1 / (T : ℝ) ^ 2 := by
        rw [Real.exp_neg, mul_comm, Real.exp_mul, Real.exp_log hT0, one_div]
        norm_cast

/-- The late weights are small: for `T ≤ log T * t` and `t ≤ 2 (k + 1)`,
`η (k + 1) ρ (k + 1) t ≤ 32 log³ T / ((1 - γ) T)`. -/
private lemma mul_prod_le_of_window_of_le (hγ : γ < 1) (hL : 0 < Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    {k t : ℕ} (htT : t ≤ T) (hkt : k < t) (hTt : (T : ℝ) ≤ Real.log T * t)
    (htk : t ≤ 2 * (k + 1)) :
    η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤
      32 * Real.log T ^ 3 / ((1 - γ) * T) := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hT0 : (0 : ℝ) < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · simp [h] at hL
    · exact_mod_cast h
  have hk : k + 1 ∈ Ioc 0 T := mem_Ioc.2 ⟨k.succ_pos, by omega⟩
  have hηk := mem_Icc_of_window hγ hlo hhi hk
  -- the product is at most `1`
  have hρ : ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ 1 := by
    refine prod_le_one₀ (fun i hi ↦ ?_) fun i hi ↦ ?_
    · have := mem_Icc_of_window hγ hlo hhi (Ioc_subset_Ioc (Nat.zero_le _) htT hi)
      nlinarith [this.1, this.2]
    · have := mem_Icc_of_window hγ hlo hhi (Ioc_subset_Ioc (Nat.zero_le _) htT hi)
      nlinarith [this.1]
  -- the learning rate is at most `16 log² T / ((1 - γ) (k + 1)) ≤ 32 log³ T / ((1 - γ) T)`
  have hk1 : (T : ℝ) ≤ 2 * Real.log T * ((k + 1 : ℕ) : ℝ) := by
    have : (t : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by exact_mod_cast htk
    nlinarith
  have hηle : η (k + 1) ≤ 16 * Real.log T ^ 2 / ((1 - γ) * ((k + 1 : ℕ) : ℝ)) := by
    have hY : 0 < (1 - γ) * ((k + 1 : ℕ) : ℝ) / (16 * Real.log T ^ 2) := by positivity
    calc η (k + 1) ≤ 1 / (1 + (1 - γ) * ((k + 1 : ℕ) : ℝ) / (16 * Real.log T ^ 2)) := hhi _ hk
      _ ≤ 1 / ((1 - γ) * ((k + 1 : ℕ) : ℝ) / (16 * Real.log T ^ 2)) :=
          one_div_le_one_div_of_le hY (by linarith)
      _ = 16 * Real.log T ^ 2 / ((1 - γ) * ((k + 1 : ℕ) : ℝ)) := one_div_div _ _
  calc η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ η (k + 1) :=
        mul_le_of_le_one_right hηk.1 hρ
    _ ≤ 16 * Real.log T ^ 2 / ((1 - γ) * ((k + 1 : ℕ) : ℝ)) := hηle
    _ ≤ 32 * Real.log T ^ 3 / ((1 - γ) * T) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hk1 (by positivity : (0 : ℝ) ≤ 16 * Real.log T ^ 2 *
          (1 - γ))]

/-- All the weights `η (k + 1) ρ (k + 1) t`, `k < t`, are at most `32 log³ T / ((1 - γ) T)`, for
`2 ≤ t ≤ T ≤ log T * t`, once `16 log² T ≤ (1 - γ) T` and `1 ≤ log T`. -/
private lemma mul_prod_le_of_window (hγ : γ < 1) (hT : 16 * Real.log T ^ 2 ≤ (1 - γ) * T)
    (hL : 1 ≤ Real.log T)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    {k t : ℕ} (ht : 2 ≤ t) (htT : t ≤ T) (hkt : k < t) (hTt : (T : ℝ) ≤ Real.log T * t) :
    η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤
      32 * Real.log T ^ 3 / ((1 - γ) * T) := by
  have hL0 : 0 < Real.log T := by linarith
  rcases le_or_gt t (2 * (k + 1)) with htk | htk
  · exact mul_prod_le_of_window_of_le hγ hL0 hlo hhi htT hkt hTt htk
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hk := mem_Icc_of_window hγ hlo hhi (i := k + 1) (mem_Ioc.2 ⟨k.succ_pos, by omega⟩)
  have hρ := prod_le_one_div_sq_of_window hγ hT hL0 hlo hhi htT hTt (k := k + 1) (by omega)
  have hρ₀ : 0 ≤ ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) :=
    Real.prod_one_sub_mul_nonneg h1γ.le h1γ' fun _ hi ↦
      mem_Icc_of_window hγ hlo hhi (Ioc_subset_Ioc (Nat.zero_le _) htT hi)
  calc η (k + 1) * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) ≤ 1 * (1 / (T : ℝ) ^ 2) :=
        mul_le_mul hk.2 hρ hρ₀ zero_le_one
    _ ≤ 32 * Real.log T ^ 3 / ((1 - γ) * T) := by
        rw [one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (1 : ℝ) ≤ Real.log T ^ 3 := one_le_pow₀ hL
        nlinarith [mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ T)]

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

/-! ### One step of the recursion of the errors -/

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

/-- The final accuracy: if `s ≤ ε ^ 2 / 50000`, then `e √(5476 s) ≤ ε`. -/
private lemma exp_one_mul_sqrt_le {s ε : ℝ} (hε : 0 < ε)
    (hsε : s ≤ ε ^ 2 / 50000) : Real.exp 1 * √(5476 * s) ≤ ε := by
  have he := Real.exp_one_lt_d9
  have he₀ := Real.exp_pos 1
  rw [show Real.exp 1 * √(5476 * s) = √(Real.exp 1 ^ 2 * (5476 * s)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he₀.le], Real.sqrt_le_left hε.le]
  have he2 : Real.exp 1 ^ 2 ≤ 7.39 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsε (by positivity : (0 : ℝ) ≤ Real.exp 1 ^ 2)]

/-! ### The sample complexity -/

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Fintype 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Unique 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ}

/-- **One step of the recursion of the errors of synchronous TD learning** [LCCWC24, (121)].
Under the assumptions of `measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_window`, with
learning rates in `[0, 1]` at every iteration, let `2 ≤ t ≤ T ≤ log T * t` and let `D ≥ 0` bound
the errors of the value estimates at the late iterations `(t + 1) / 2 ≤ k < t`. On the event of
Freedman's inequality at iteration `t`, with the confidence level `δ / (2 S (T + 1))` and the bound
`32 log³ T / (1 - γ) ^ 2 T` on the increments, the error of the `t`-th iterate is at most
`√(5476 s max 1 D)`, with `s = log³ T log (S T / δ) / ((1 - γ) ^ 3 T)`. -/
private lemma abs_syncQLearning_sub_optQValue_le_sqrt (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {T : ℕ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    (h16 : 16 * Real.log T ^ 2 ≤ (1 - γ) * T) (hL1 : 1 ≤ Real.log T) (hT8 : 8 ≤ (T : ℝ))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1 / 36864)
    (hs : Real.log T ^ 3 * Real.log (Fintype.card 𝓢 * T / δ) / ((1 - γ) ^ 3 * T) = s)
    (hBs : 1 / (1 - (γ : ℝ)) / (T : ℝ) ^ 2 ≤ √s)
    {t : ℕ} (ht : 2 ≤ t) (htT : t ≤ T) (hTt : (T : ℝ) ≤ Real.log T * t)
    {ω : ℕ → 𝓢 × 𝓐 → 𝓢} {D : ℝ} (hD₀ : 0 ≤ D)
    (hD : ∀ k ∈ Ico ((t + 1) / 2) t, ∀ s',
      |syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default) - M.optQValue γ (s', default)| ≤ D)
    (q : 𝓢 × 𝓐)
    (hgood : |syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q| ≤
      (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (1 / (1 - γ)) +
        (3 * √(tdNoiseVarBound M γ η Q₀
            (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) t ω q *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * Fintype.card 𝓢 * (T + 1)))))) +
        2 * (32 * Real.log T ^ 3 / ((1 - γ) * T) * (1 / (1 - γ))) *
          max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * Fintype.card 𝓢 * (T + 1))))))) :
    |syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q| ≤ √(5476 * s * max 1 D) := by
  set L := Real.log T with hL_def
  set B : ℝ := 1 / (1 - γ) with hB_def
  set β := 32 * L ^ 3 / ((1 - γ) * T) with hβ_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have h1γ' : (1 : ℝ) - γ ≤ 1 := by linarith [γ.coe_nonneg]
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hT0 : (0 : ℝ) < T := by linarith
  have hL0 : 0 < L := by linarith
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ h1γ]
    linarith
  have hβ₀ : 0 < β := by positivity
  have hS : (1 : ℝ) ≤ Fintype.card 𝓢 := by exact_mod_cast Fintype.card_pos
  have hρ₀ := prod_one_sub_mul_one_sub_nonneg hγ hη
  -- the quadratic variation is at most `β B ^ 2 (2 + 4 D)`
  -- with one action, the value estimates are the iterates and the unique policy is greedy for `Q*`
  have hπ (s' : 𝓢) : M.optQValue γ (s', default) = M.optValue γ s' := by
    rw [← iSup_optQValue hγ (fun p ↦ (hR p).mono fun x hx ↦
      abs_le.2 ⟨by linarith [hx.1, hx.2], hx.2⟩) s', ciSup_unique]
  have hW := tdNoiseVarBound_le hγ hR hη hQ₀ hπ (m := (t + 1) / 2) (t := t) (by omega) hD₀
    (fun k hk s' ↦ by rw [ciSup_unique, ← hπ s']; exact hD k hk s')
    hβ₀.le (fun k hk ↦ mul_prod_le_of_window_of_le hγ hL0 hlo hhi htT (mem_Ico.1 hk).2 hTt
      (by have := (mem_Ico.1 hk).1; omega)) q
  have hE : ∑ k ∈ range ((t + 1) / 2),
      (η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) ^ 2 ≤ β := by
    have hterm (k : ℕ) (hk : k ∈ range ((t + 1) / 2)) :
        (η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))) ^ 2 ≤
          (1 / (T : ℝ) ^ 2) ^ 2 := by
      have hk' := mem_range.1 hk
      have hρ := prod_le_one_div_sq_of_window hγ h16 hL0 hlo hhi htT hTt (k := k + 1) (by omega)
      refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg (hη k).1 γ.coe_nonneg) (hρ₀ _ _)) ?_ 2
      calc η (k + 1) * γ * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ))
          ≤ 1 * 1 * ∏ i ∈ Ioc (k + 1) t, (1 - η i * (1 - γ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (hη k).2 hγ1 γ.coe_nonneg zero_le_one)
              (hρ₀ _ _)
        _ ≤ 1 / (T : ℝ) ^ 2 := by rw [one_mul, one_mul]; exact hρ
    have hm : (((t + 1) / 2 : ℕ) : ℝ) ≤ T := by exact_mod_cast (show (t + 1) / 2 ≤ T by omega)
    calc _ ≤ ∑ k ∈ range ((t + 1) / 2), (1 / (T : ℝ) ^ 2) ^ 2 := sum_le_sum hterm
      _ = (((t + 1) / 2 : ℕ) : ℝ) * (1 / (T : ℝ) ^ 2) ^ 2 := by simp
      _ ≤ T * (1 / (T : ℝ) ^ 2) ^ 2 := by gcongr
      _ ≤ β := by
          rw [hβ_def, div_pow, one_pow, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity)
            (by positivity)]
          have hL3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
          have hT3 : (T : ℝ) ≤ T ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_left h1γ' (by positivity : (0 : ℝ) ≤ T ^ 2),
            mul_le_mul hL3 hT3 (by positivity) (by positivity)]
  have hW' : tdNoiseVarBound M γ η Q₀
      (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) t ω q ≤
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
  have hℓ := max_one_log_le (t := t) hS hδ hδ₁ hT8 htT
  have hρ0 := prod_le_one_div_sq_of_window hγ h16 hL0 hlo hhi htT hTt (k := 0) (by omega)
  refine hgood.trans (add_le_sqrt_mul_max hB1 ?_ hW' (by positivity) hℓ hβ₀.le hs₀ ?_ hs₁)
  · calc (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * B ≤ 1 / (T : ℝ) ^ 2 * B :=
        mul_le_mul_of_nonneg_right hρ0 (zero_le_one.trans hB1)
      _ = B / (T : ℝ) ^ 2 := by ring
      _ ≤ √s := hBs
  · rw [hβ_def, hB_def, ← hs]
    field_simp

/-- **The errors on the event of Freedman's inequality** [LCCWC24, Appendix C]. Under the
assumptions of `abs_syncQLearning_sub_optQValue_le_sqrt`, let `K ≥ 1` with `2 ^ K ≤ log T` and
`1 / (1 - γ) ≤ e ^ 2 ^ K`, and let the bound of Freedman's inequality hold at every iteration
`t ≤ T` of the dyadic windows, `T ≤ 2 ^ K t`. Then the error of the `T`-th iterate is at most
`e √(5476 s)`: by induction on `j`, the errors at the iterations `T ≤ 2 ^ (K - j) t` are at most
`windowBound (1 / (1 - γ)) (5476 s) j`, which the square-root recursion bounds at `j = K`. -/
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
          2 * (32 * Real.log T ^ 3 / ((1 - γ) * T) * (1 / (1 - γ))) *
            max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * Fintype.card 𝓢 * (T + 1)))))))
    (p : 𝓢 × 𝓐) :
    |syncQLearning (meanReward M.R) γ η Q₀ T ω p - M.optQValue γ p| ≤ Real.exp 1 * √(5476 * s) := by
  set B : ℝ := 1 / (1 - γ) with hB_def
  set r := 5476 * s with hr_def
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ (sub_pos.2 (by exact_mod_cast hγ))]
    linarith [γ.coe_nonneg]
  have hx₀ (j : ℕ) : 0 ≤ windowBound B r j := by
    cases j with
    | zero => rw [windowBound]; linarith
    | succ j => rw [windowBound]; exact Real.sqrt_nonneg _
  have claim (j : ℕ) (hj : j ≤ K) (t : ℕ) (htT : t ≤ T) (hTt : T ≤ 2 ^ (K - j) * t)
      (q : 𝓢 × 𝓐) :
      |syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q| ≤ windowBound B r j := by
    induction j generalizing t q with
    | zero =>
      rw [windowBound]
      exact abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ t ω q
    | succ j ih =>
      have hTt' : T ≤ 2 ^ K * t :=
        hTt.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega)))
      obtain ⟨ht2, hTLt⟩ := two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL hTt'
      -- the errors at the late iterations `(t + 1) / 2 ≤ k < t` are at most `windowBound B r j`
      have hD (k : ℕ) (hk : k ∈ Ico ((t + 1) / 2) t) (s' : 𝓢) :
          |syncQLearning (meanReward M.R) γ η Q₀ k ω (s', default) -
            M.optQValue γ (s', default)| ≤ windowBound B r j := by
        obtain ⟨hk₁, hk₂⟩ := mem_Ico.1 hk
        refine ih (by omega) k (by omega) ?_ (s', default)
        have h2 : 2 ^ (K - j) = 2 ^ (K - (j + 1)) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        calc T ≤ 2 ^ (K - (j + 1)) * t := hTt
          _ ≤ 2 ^ (K - (j + 1)) * (2 * k) := Nat.mul_le_mul_left _ (by omega)
          _ = 2 ^ (K - j) * k := by rw [h2]; ring
      rw [windowBound]
      exact abs_syncQLearning_sub_optQValue_le_sqrt hγ hR hQ₀ hη hlo hhi h16 hL1 hT8 hδ hδ₁
        hs₀ (by linarith) hs hBs ht2 htT hTLt (hx₀ j) hD q (hgood t htT hTt' q)
  refine (claim K le_rfl T le_rfl (by simp) p).trans
    (Real.le_mul_sqrt_of_le_sqrt_mul_max (by positivity) (by linarith)
      (Real.one_le_exp zero_le_one) hK1 (fun k _ ↦ ?_) ?_)
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
  set β := 32 * L ^ 3 / ((1 - γ) * T) with hβ_def
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (by exact_mod_cast hγ)
  have hL1 : 1 ≤ L := by linarith
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ h1γ]
    linarith [γ.coe_nonneg]
  have hs₁ : s ≤ 1 / 50000 :=
    hsε.trans (div_le_div_of_nonneg_right (pow_le_one₀ hε.le hε₁) (by norm_num))
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
    · exact mem_Icc_of_window hγ hlo' hhi' (mem_Ioc.2 ⟨t.succ_pos, ht⟩)
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
    have h := mul_prod_le_of_window hγ h16 hL1 hlo' hhi' (hI t ht).2.1 (hI t ht).1 hk
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
    linarith [exp_one_mul_sqrt_le hε hsε]
  · -- `2 S #I δ' ≤ δ`
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : (#I : ℝ) ≤ T + 1 := by
      exact_mod_cast (card_filter_le _ _).trans (card_range _).le
    rw [hδ'_def, show (2 * Fintype.card 𝓢 * #I * (δ / (2 * S * (T + 1))) : ℝ) =
      #I / (T + 1) * δ by rw [hS_def]; field_simp]
    exact mul_le_of_le_one_left hδ.le ((div_le_one (by positivity)).2 hcard)

end LMLExplore.ReinforcementLearning
