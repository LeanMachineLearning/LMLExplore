/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.ReinforcementLearning.TemporalDifference.Synchronous
import LMLExplore.ReinforcementLearning.QLearning.Window

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
and the lower bound of one step of the recursion of the errors
(`LMLExplore.ReinforcementLearning.le_sqrt_mul_max_of_le_tdNoiseVarBound`), which is two-sided
with one action, the error of every iterate `t ≥ T / log T` satisfies
`‖Δ t‖ ≤ √(r max 1 (max_{t / 2 ≤ k < t} ‖Δ k‖))`, with
`r = 5476 log³ T log (S T / δ) / ((1 - γ) ^ 3 T)`. On the dyadic windows
`T / 2 ^ (K - j) ≤ t ≤ T`, the bounds `x (j + 1) = √(r max 1 (x j))` from `x 0 = 1 / (1 - γ)` reach
`e √r` after `K ≈ log₂ log T` windows (`LMLExplore.ReinforcementLearning.abs_le_of_dyadic` and
`LMLExplore.ReinforcementLearning.windowBound_le` [LCCWC24, Appendix B.4]).

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

section TD

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Fintype 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Unique 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {η : ℕ → ℝ} {Q₀ : 𝓢 × 𝓐 → ℝ}

/-- **The errors of TD learning on the event of Freedman's inequality** [LCCWC24, Appendix C].
Under the assumptions of `measure_exists_lt_abs_syncQLearning_sub_optQValue_le_of_window`, with
learning rates in `[0, 1]` at every iteration, let `2 ^ K ≤ log T`, and let the bound of
Freedman's inequality, with the confidence level `δ / (2 S (T + 1))` and the bound
`32 log³ T / (1 - γ) ^ 2 T` on the increments, hold at every iteration `t ≤ T` of the dyadic
windows, `T ≤ 2 ^ K t`. Then the error of the `T`-th iterate is at
most `windowBound (1 / (1 - γ)) (5476 s) K`, with `s = log³ T log (S T / δ) / ((1 - γ) ^ 3 T)`:
by `le_sqrt_mul_max_of_le_tdNoiseVarBound` and the induction over the dyadic windows, the errors
at the iterations `T ≤ 2 ^ (K - j) t` are at most `windowBound (1 / (1 - γ)) (5476 s) j`. -/
private lemma abs_syncQLearning_sub_optQValue_le_of_window (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hQ₀ : ∀ p, Q₀ p ∈ Set.Icc 0 (1 / (1 - (γ : ℝ))))
    {T : ℕ} (hη : ∀ t, η (t + 1) ∈ Set.Icc (0 : ℝ) 1)
    (hlo : ∀ i ∈ Ioc 0 T, 1 / (1 + (1 - γ) * T / (16 * Real.log T ^ 2)) ≤ η i)
    (hhi : ∀ i ∈ Ioc 0 T, η i ≤ 1 / (1 + (1 - γ) * i / (16 * Real.log T ^ 2)))
    (h16 : 16 * Real.log T ^ 2 ≤ (1 - γ) * T) (hL1 : 1 ≤ Real.log T) (hT8 : 8 ≤ (T : ℝ))
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) {s : ℝ} (hs₁ : s ≤ 1 / 50000)
    (hs : Real.log T ^ 3 * Real.log (Fintype.card 𝓢 * T / δ) / ((1 - γ) ^ 3 * T) = s)
    (hBs : 1 / (1 - (γ : ℝ)) / (T : ℝ) ^ 2 ≤ √s) {K : ℕ}
    (hKL : ((2 ^ K : ℕ) : ℝ) ≤ Real.log T) {ω : ℕ → 𝓢 × 𝓐 → 𝓢}
    (hgood : ∀ t ≤ T, T ≤ 2 ^ K * t → ∀ q,
      |syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q| ≤
        (∏ i ∈ Ioc 0 t, (1 - η i * (1 - γ))) * (1 / (1 - γ)) +
          (3 * √(tdNoiseVarBound M γ η Q₀
              (M.saKernel (Kernel.deterministic (fun _ ↦ default) measurable_const)) t ω q *
            max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * Fintype.card 𝓢 * (T + 1)))))) +
          2 * (2 * (16 * Real.log T ^ 2) * Real.log T / ((1 - γ) * T) * (1 / (1 - γ))) *
            max 1 (Real.log ((⌈Real.logb 4 t⌉₊ + 1 : ℝ) / (δ / (2 * Fintype.card 𝓢 * (T + 1)))))))
    (p : 𝓢 × 𝓐) :
    |syncQLearning (meanReward M.R) γ η Q₀ T ω p - M.optQValue γ p| ≤
      windowBound (1 / (1 - γ)) (5476 * s) K := by
  set B : ℝ := 1 / (1 - γ) with hB_def
  set r := 5476 * s with hr_def
  have hB1 : 1 ≤ B := by
    rw [hB_def, le_div_iff₀ (sub_pos.2 (by exact_mod_cast hγ))]
    linarith [γ.coe_nonneg]
  have hS : (1 : ℝ) ≤ Fintype.card 𝓢 := by exact_mod_cast Fintype.card_pos
  -- with one action, the unique policy is greedy for `Q*`
  have hπ (s' : 𝓢) : M.optQValue γ (s', default) = M.optValue γ s' := by
    rw [← iSup_optQValue hγ (fun p ↦ ae_abs_le_of_ae_mem_Icc (hR p)) s', ciSup_unique]
  refine abs_le_of_dyadic (u := windowBound B r) (K := K)
    (e := fun t q ↦ syncQLearning (meanReward M.R) γ η Q₀ t ω q - M.optQValue γ q)
    (fun t _ q ↦ ?_) (fun j _ t htT hTt hD q ↦ ?_) p
  · rw [windowBound_zero]
    exact abs_syncQLearning_sub_optQValue_le hγ hR hη hQ₀ t ω q
  · -- the errors at the late iterations of the window give the bound at `t`
    have hTt' : T ≤ 2 ^ K * t :=
      hTt.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos (by omega)))
    obtain ⟨ht2, hTLt⟩ := two_le_and_le_log_mul_of_le_two_pow_mul hT8 hKL hTt'
    rw [windowBound_succ]
    refine le_sqrt_mul_max_of_le_tdNoiseVarBound hγ hR hQ₀ hη hlo hhi le_rfl h16 hL1
      (zero_le_one.trans (le_max_left _ _)) (max_one_log_ceil_logb_le hS hδ hδ₁ hT8 htT)
      (by linarith) ?_ hBs ht2 htT hTLt hπ (windowBound_nonneg (by linarith) r j)
      (fun k hk s' ↦ ?_) q (hgood t htT hTt' q)
    · have hL0 : Real.log T ≠ 0 := by positivity
      have h1γ : (1 : ℝ) - γ ≠ 0 := (sub_pos.2 (by exact_mod_cast hγ)).ne'
      rw [← hs]
      field_simp
    · rw [ciSup_unique, ← hπ s']
      exact hD k hk (s', default)

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
  obtain ⟨hT8, hL2, hΛL, h50000, hB3, hsε⟩ := eight_le_and_le_of_sample_size (n := 3)
    (C := 50000) hγ hε hε₁ hδ hδ₁ hS le_rfl (by norm_num) hT hTε
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
  have h16 : 16 * L ^ 2 ≤ (1 - γ) * T := by
    norm_num at h50000
    nlinarith [sq_nonneg L]
  have hs₀ : 0 ≤ s := by
    have : 0 ≤ Real.log (S * T / δ) := by linarith
    positivity
  have hs₁ : s ≤ 1 / 50000 :=
    hsε.trans (div_le_div_of_nonneg_right (pow_le_one₀ hε.le hε₁) (by norm_num))
  have hBs : B / (T : ℝ) ^ 2 ≤ √s :=
    one_div_one_sub_div_sq_le_sqrt hγ (by linarith) (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ hL1) (by linarith))
  have hκ : (0 : ℝ) < 16 * L ^ 2 := by positivity
  -- the dyadic windows: `T / 2 ^ (K - j) ≤ t ≤ T`, with `2 ^ K ≤ log T`
  obtain ⟨hK1, hKL, hBK⟩ := one_le_natLog_floor_and_two_pow_le hL2 hB1 (by
    have h := Real.log_le_log (by positivity) hB3
    rw [Real.log_pow] at h
    push_cast at h
    exact h)
  set K := Nat.log 2 ⌊L⌋₊ with hK_def
  -- the learning rates, set to `0` after `T`, and the iterations of the windows
  obtain ⟨η', hηη', hlo', hhi', hη'⟩ := exists_eq_mem_Icc_of_window hγ hκ hlo hhi
  set I := (range (T + 1)).filter fun t ↦ T ≤ 2 ^ K * t with hI_def
  have hI (t : ℕ) (ht : t ∈ I) :=
    le_and_mul_prod_le_of_mem_filter hγ le_rfl h16 hT8 hKL hlo' hhi' ht
  -- the event of Freedman's inequality at the iterations of the windows
  set δ' := δ / (2 * S * (T + 1)) with hδ'_def
  have hδ' : 0 < δ' := by positivity
  have hβ₀ : 0 < β := by positivity
  have hbad := measure_exists_mem_exists_lt_abs_syncQLearning_sub_optQValue_le (M := M)
    (η := η') (Q₀ := Q₀) (C := 1) hγ hR hη' hQ₀ hδ' (by positivity : 0 < β * B) I
    fun t ht ↦ (hI t ht).2
  refine (measure_mono fun ω hω ↦ ?_).trans (hbad.trans ?_)
  · -- on the event of Freedman's inequality, the error is at most `e √(5476 s) ≤ ε`
    by_contra hgood
    obtain ⟨p, hp⟩ := hω
    rw [syncQLearning_congr_learningRate hηη'] at hp
    have h := abs_syncQLearning_sub_optQValue_le_of_window hγ hR hQ₀ hη' hlo' hhi' h16 hL1 hT8 hδ
      hδ₁ hs₁ hs_def.symm hBs hKL (fun t htT hTt q ↦ not_lt.1 fun h ↦
        hgood ⟨t, mem_filter.2 ⟨mem_range.2 (by omega), hTt⟩, q, h⟩) p
    linarith [windowBound_le hK1 hBK (by positivity : (0 : ℝ) ≤ 5476 * s) hε hε₁ (by linarith)]
  · -- `2 S #I δ' ≤ δ`
    refine ENNReal.ofReal_le_ofReal ?_
    have hcard : (#I : ℝ) ≤ T + 1 := by
      exact_mod_cast (card_filter_le _ _).trans (card_range _).le
    rw [hδ'_def, show (2 * Fintype.card 𝓢 * #I * (δ / (2 * S * (T + 1))) : ℝ) =
      #I / (T + 1) * δ by rw [hS_def]; field_simp]
    exact mul_le_of_le_one_left hδ.le ((div_le_one (by positivity)).2 hcard)

end TD

end LMLExplore.ReinforcementLearning
