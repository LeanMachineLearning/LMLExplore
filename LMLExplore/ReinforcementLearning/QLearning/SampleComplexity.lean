/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.Synchronous
import LMLExplore.ReinforcementLearning.QLearning.LowerBound
import LMLExplore.ReinforcementLearning.QLearning.UpperBound
import LMLExplore.ReinforcementLearning.QLearning.Window

/-!
# The sample complexity of synchronous Q-learning

Synchronous Q-learning (`LMLExplore.ReinforcementLearning.syncQLearning`) on the generative model,
with rewards in `[0, 1]`, an initial value in `[0, 1 / (1 - γ)]`, `T ≥ 2` iterations and learning
rates in the rescaled linear window

`1 / (1 + (1 - γ) T / (64 log³ T)) ≤ η t ≤ 1 / (1 + (1 - γ) t / (64 log³ T))`, `1 ≤ t ≤ T`,

is `ε`-accurate in the sup norm with probability at least `1 - δ` as soon as
`T ≥ 2500000 log⁴ T log (S A T / δ) / ((1 - γ) ^ 4 ε ^ 2)`, for `ε ∈ (0, 1]`, where `S` and `A` are
the numbers of states and actions [LCCWC24, Theorem 2]. The constant learning rate
`1 / (1 + (1 - γ) T / (64 log³ T))` is in the window.

The proof follows [LCCWC24, Appendix B]. With high probability, by Freedman's inequality, the
error of every iterate `t ≥ T / log T` is bounded in terms of the errors of the late iterations
`t / 2 ≤ k < t`:
* from below, along the state-action kernel of a policy greedy for `Q*`
  (`LMLExplore.ReinforcementLearning.measure_exists_mem_exists_lt_optQValue_sub_syncQLearning_le`
  and `LMLExplore.ReinforcementLearning.le_sqrt_mul_max_of_le_tdNoiseVarBound`);
* from above, by the windowed recursion and the comparison with a common supersolution
  (`LMLExplore.ReinforcementLearning.measure_exists_lt_syncQLearning_sub_optQValue_le`), with
  `J ≈ log T / (1 - γ)` blocks of `L ≈ (1 - γ) T / (32 log² T)` iterations.

This gives `‖Δ t‖ ≤ √(r max 1 (max_{t / 2 ≤ k < t} ‖Δ k‖))`, with
`r = 69696 log⁴ T log (S A (T + 1) ^ 2 T / δ) / ((1 - γ) ^ 4 T)`. On the dyadic windows
`T / 2 ^ (K - j) ≤ t ≤ T`, the bounds `x (j + 1) = √(r max 1 (x j))` from `x 0 = 1 / (1 - γ)`
reach `e √r` after `K ≈ log₂ log T` windows (`LMLExplore.ReinforcementLearning.abs_le_of_dyadic`
and `LMLExplore.ReinforcementLearning.windowBound_le` [LCCWC24, Appendix B.4]). The upper events
are indexed by the window and the iteration, since the bound on the late errors must be fixed
before taking the probability, so that the union bound runs at the confidence level
`δ / (2 S A (T + 1) ^ 3)`.

The bound improves the source in two ways: the factor `1 / γ ^ 2` of [LCCWC24, (101)] is not
needed, since the resolvent of the one-step variances of the optimal value satisfies
`γ ^ 2 (I - γ P)⁻¹ Var_P(V*) ≤ 1 / (1 - γ) ^ 2`
(`LMLExplore.ReinforcementLearning.mul_integral_variance_optValue_le`), so that the statement
holds for every `γ < 1` instead of `γ ∈ [1 / 2, 1)`; and the constants are explicit.

## Main statements

* `measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_cube_window`: the sample complexity
  of synchronous Q-learning [LCCWC24, Theorem 2].

## References

* [LCCWC24] G. Li, C. Cai, Y. Chen, Y. Wei and Y. Chi, *Is Q-learning minimax optimal? A tight
  sample complexity analysis*, Operations Research (2024), arXiv:2102.06548.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP Bandits
open scoped NNReal

namespace LMLExplore.ReinforcementLearning

/-! ### The arithmetic of the sample complexity of Q-learning -/

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
  have hT0 : (0 : ℝ) < T :=
    pos_of_mul_pos_right ((by positivity : (0 : ℝ) < 64 * L ^ 3).trans_le h64) h1γ.le
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
`[0, 1]` at every iteration, let `2 ^ K ≤ log T` and `γ ^ J ≤ 1 / T`, and, at every iteration
`t ≤ T` of the dyadic windows, `T ≤ 2 ^ K t`, let
* the lower bound of Freedman's inequality along the state-action kernel of a policy `π` greedy for
  `Q*` hold, with the confidence level `δ / (2 S (T + 1) ^ 3)` and the bound
  `128 log⁴ T / (1 - γ) ^ 2 T` on the increments;
* the upper bound of the windowed recursion with `J` blocks hold, for the bounds
  `Real.windowBound (1 / (1 - γ)) (69696 s) j` on the errors of the late iterations, `j < K`.

Then the error of the `T`-th iterate is at most `Real.windowBound (1 / (1 - γ)) (69696 s) K`, with
`s = log⁴ T log (S (T + 1) ^ 2 T / δ) / ((1 - γ) ^ 4 T)`. -/
private lemma abs_syncQLearning_sub_optQValue_le_of_cube_window [Finite 𝓢] [Finite 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {T : ℕ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (64 * Real.log T ^ 3)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (64 * Real.log T ^ 3)))
    (h64 : 64 * Real.log T ^ 3 ≤ (1 - γ) * T) (hL2 : 2 ≤ Real.log T) (hT8 : 8 ≤ (T : ℝ))
    {δ S : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (hS : 1 ≤ S) {s : ℝ} (hs₁ : s ≤ 1 / 625000)
    (hs : Real.log T ^ 4 * Real.log (S * (T + 1) ^ 2 * T / δ) / ((1 - γ) ^ 4 * T) = s)
    {K J : ℕ} (hKL : ((2 ^ K : ℕ) : ℝ) ≤ Real.log T) (hJ : (γ : ℝ) ^ J ≤ 1 / T)
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
          Real.windowBound (1 / (1 - γ)) (69696 * s) j) → ∀ q,
      syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q ≤
        γ ^ J * (1 / (1 - γ)) +
          √(2 * (1 / (T : ℝ) * (1 / (1 - γ)) +
              2 * (2 * (64 * Real.log T ^ 3) * Real.log T / ((1 - γ) * T) * (1 / (1 - γ))) *
                max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) /
                  (δ / (2 * (S * (T + 1) ^ 2) * (T + 1)))))) ^ 2 +
            36 * (2 * (64 * Real.log T ^ 3) * Real.log T / ((1 - γ) * T)) *
              max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) /
                (δ / (2 * (S * (T + 1) ^ 2) * (T + 1))))) * (1 / (1 - γ)) *
              (1 + 4 * γ ^ 2 * Real.windowBound (1 / (1 - γ)) (69696 * s) j)) / (1 - γ))
    (p : 𝓢 × 𝓐) :
    |syncQLearning (meanReward M.R) γ η Q₀ T ω p - M.optQValue γ p| ≤
      Real.windowBound (1 / (1 - γ)) (69696 * s) K := by
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
    refine (one_div_one_sub_div_sq_le_sqrt hγ hT1 (X := 4 * (L ^ 4 *
      Real.log (S * (T + 1) ^ 2 * T / δ))) (by
        linarith [one_le_mul_of_one_le_of_one_le (one_le_pow₀ (n := 4) hL1) hΛ])).trans_eq ?_
    rw [← hs]
    congr 1
    field_simp
  have hx₀ := Real.windowBound_nonneg (by linarith : 0 ≤ B) r
  have hγ2 : (γ : ℝ) ^ 2 ≤ 1 := pow_le_one₀ γ.coe_nonneg (by exact_mod_cast hγ.le)
  have hRabs (q : 𝓢 × 𝓐) := ae_abs_le_of_ae_mem_Icc (hR q)
  refine abs_le_of_dyadic (u := Real.windowBound B r) (K := K)
    (e := fun t q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q)
    (fun t _ q ↦ ?_) (fun j hj t htT hTt hD q ↦ ?_) p
  · rw [Real.windowBound_zero]
    exact abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ t ω q
  · -- the bounds from below and from above at `t`, from the errors at the late iterations
    have hTt' : T ≤ 2 ^ K * t :=
      hTt.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega)))
    obtain ⟨ht2, hTLt⟩ := two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL hTt'
    have hℓ := max_one_log_ceil_logb_le (S := S * (T + 1) ^ 2) (t := t) (by nlinarith) hδ hδ₁
      hT8 htT
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
    have hLr : √(5476 * (4 * (1 - γ) * s) * max 1 (Real.windowBound B r j)) ≤
        √(r * max 1 (Real.windowBound B r j)) := by
      refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right ?_
        (zero_le_one.trans (le_max_left _ _)))
      rw [hr_def]
      nlinarith
    rw [Real.windowBound_succ]
    exact abs_le.2 ⟨by linarith, hupper⟩

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
  have hT0 : (0 : ℝ) < T := pos_of_mul_pos_right (hκ.trans_le h64) h1γ.le
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
  -- the consequences of the sample size condition
  obtain ⟨hT8, hL2, -, h2500000, hB3, hsε⟩ := eight_le_and_le_of_sample_size (n := 4)
    (C := 2500000) hγ hε hε₁ hδ hδ₁ hS (by norm_num) (by norm_num) hT hTε
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
  have h64 : 64 * L ^ 3 ≤ (1 - γ) * T := by
    norm_num at h2500000
    nlinarith [pow_nonneg hL0.le 3]
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
  obtain ⟨hK1, hKL, hBK⟩ := one_le_natLog_floor_and_two_pow_le hL2 hB1 (by
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
  obtain ⟨η', hηη', hlo', hhi', hη'⟩ := exists_eq_mem_Icc_of_window hγ hκ hlo hhi
  -- a policy greedy for `Q*`
  choose π hπ using fun s ↦ exists_eq_ciSup_of_finite (f := fun a ↦ M.optQValue γ (s, a))
  have hπ' (s : 𝓢) : M.optQValue γ (s, π s) = M.optValue γ s :=
    (hπ s).trans (iSup_optQValue hγ (fun p ↦ ae_abs_le_of_ae_mem_Icc (hR p)) s)
  -- the iterations of the windows
  set I := (range (T + 1)).filter fun t ↦ T ≤ 2 ^ K * t with hI_def
  have hI (t : ℕ) (ht : t ∈ I) := le_and_mul_prod_le_of_mem_filter hγ h16 h64 hT8 hKL hlo' hhi' ht
  have hcard : (#I : ℝ) ≤ T + 1 := by
    exact_mod_cast (card_filter_le _ _).trans (card_range _).le
  -- the events of Freedman's inequality at the iterations of the windows, at the confidence
  -- level `δ'`: the lower bound at every iteration of the windows, and, for every window `j` and
  -- iteration `t`, the upper bound from the bound `windowBound B (69696 s) j` on the late errors
  set δ' := δ / (2 * (S * (T + 1) ^ 2) * (T + 1)) with hδ'_def
  have hδ' : 0 < δ' := by positivity
  have hlow := measure_exists_mem_exists_lt_optQValue_sub_syncQLearning_le (M := M)
    (η := η') (Q₀ := Q₀) (C := 1) hγ hR hη' hQ₀ hπ' hδ' (by positivity : 0 < β * B) I
    fun t ht ↦ (hI t ht).2
  set E : ℕ → ℕ → Set (ℕ → 𝓢 × 𝓐 → 𝓢) := fun j t ↦ {ω |
    (∀ k ∈ Ico ((t + 1) / 2) t, ∀ q,
      |syncQLearning (meanReward M.R) γ η' Q₀ k ω q - M.optQValue γ q| ≤
        Real.windowBound B (69696 * s) j) ∧
    ∃ p, γ ^ J * (1 / (1 - γ)) +
        √(2 * (1 / (T : ℝ) * (1 / (1 - γ)) +
            2 * (β * B) * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ'))) ^ 2 +
          36 * β * max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / δ')) * (1 / (1 - γ)) *
            (1 + 4 * γ ^ 2 * Real.windowBound B (69696 * s) j)) / (1 - γ) <
      syncQLearning (meanReward M.R) γ η' Q₀ t ω p - M.optQValue γ p}
  have hup (j t : ℕ) (ht : t ∈ I) :
      streamMeasure M.P (E j t) ≤ ENNReal.ofReal ((T + 1) * S * δ') :=
    measure_exists_lt_syncQLearning_sub_optQValue_le_of_cube_window hγ hR hη' hQ₀ hlo' hhi' h64
      hL2 hδ' (hI t ht).1.1 (hI t ht).1.2.2
  -- the union bound over the lower event and the upper events `E j t`, `j < K`, `t ∈ I`
  refine (measure_mono fun ω hω ↦ ?_).trans ((measure_union_le _ _).trans
    ((add_le_add hlow ((measure_biUnion_finset_le (range K) _).trans (sum_le_sum fun j _ ↦
      (measure_biUnion_finset_le I _).trans (sum_le_sum fun t ht ↦ hup j t ht)))).trans ?_))
  · -- on the events of Freedman's inequality, the error is at most `e √(69696 s) ≤ ε`
    by_contra hgood
    obtain ⟨p, hp⟩ := hω
    rw [syncQLearning_congr_learningRate hηη'] at hp
    have hmem (t : ℕ) (htT : t ≤ T) (hTt : T ≤ 2 ^ K * t) : t ∈ I :=
      mem_filter.2 ⟨mem_range.2 (by omega), hTt⟩
    have h := abs_syncQLearning_sub_optQValue_le_of_cube_window hγ hR hQ₀ hη' hlo' hhi' h64 hL2
      hT8 hδ hδ₁ hS hs₁ hs_def.symm hKL hJ hπ'
      (fun t htT hTt q ↦ not_lt.1 fun h ↦ hgood (Or.inl ⟨t, hmem t htT hTt, q, h⟩))
      (fun j hj t htT hTt hD q ↦ not_lt.1 fun h ↦ hgood (Or.inr (Set.mem_iUnion₂.2
        ⟨j, mem_range.2 hj, Set.mem_iUnion₂.2 ⟨t, hmem t htT hTt, hD, q, h⟩⟩))) p
    linarith [windowBound_le hK1 hBK (by positivity : (0 : ℝ) ≤ 69696 * s) hε hε₁ (by linarith)]
  · -- `S #I δ' + K #I (T + 1) S δ' ≤ (T + 1) ^ 3 S δ' = δ / 2`
    simp only [sum_const, card_range]
    rw [← ENNReal.ofReal_nsmul, ← ENNReal.ofReal_nsmul,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [nsmul_eq_mul]
    exact add_mul_le_of_cube (by positivity) hδ hcard hKT

end QLearning

end LMLExplore.ReinforcementLearning
