/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.ValueLevel
public import LMLExplore.ReinforcementLearning.Generative.Episodic
import Mathlib.Data.Nat.Log

/-!
# Model-based planning in finite horizon over the full range of accuracies

Let `M` be an episodic MDP with horizon `H`, `S` states, `A` actions and rewards in `[0, 1]`, and
`M̂ = M.empirical H N ω` the empirical episodic MDP of `N` samples per step and state-action pair
under the generative model `Bandits.streamMeasure (M.generativeKernel H)`. Model-based planning
plays the greedy optimal policy `π̂ = M̂.optPolicy H` of the empirical MDP. Li, Wei, Chi, Gu and
Chen [LWCGC24, Theorem 4] prove that it is `ε`-optimal over the full range of accuracies
`ε ∈ (0, H]` as soon as `N` is of order `H ^ 3 log (H S A / δ) / ε ^ 2`, with no perturbation of
the rewards, unlike the discounted case (`ReinforcementLearning/Generative/PerturbedPlugIn.lean`).

The proof has a deterministic part and a probabilistic part.
* The **deterministic part**, [LWCGC24, Lemma 9], is
  `EpisodicMDP.abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le` in
  `MarkovDecisionProcess/Episodic/ValueLevel.lean`: if the transitions of `M̂` deviate from those
  of `M` by Bernstein-type bounds on the levels `V l` of [LWCGC24, (62)] of a policy, for
  `l ≤ m` with `H ≤ 4 ^ m`, then the values of the policy in `M` and in `M̂` are within
  `4 H √(2 L H / N)`.
* The **probabilistic part** is the uniform Bernstein bound at the steps of the empirical MDP
  (`EpisodicMDP.le_streamMeasure_forall_abs_integral_sub_integral_empirical_trans_lt`),
  applied to the levels `V l (h + 1)`, rescaled to `[0, 1]`, of two policies: the greedy optimal
  policy `π*` of `M`, which does not depend on the samples, and the greedy optimal policy `π̂` of
  `M̂`. The levels of `π̂` from the step `h + 1` on only depend on `π̂` from the step `h + 1` on,
  which only depends on the transitions of `M̂` after the step `h`: they are independent of the
  samples of the step `h` [LWCGC24, §7.3].

On the intersection of the two events, the suboptimality
`V* - V^π̂ = (V^π* - V̂^π*) + (V̂^π* - V̂*) + (V̂^π̂ - V^π̂)`, whose middle term is nonpositive, is
at most `8 H √(2 L H / N)`. With `m = ⌈log₄ H⌉` and `L = log (4 (m + 1) H S A / δ)`, this gives,
for `0 < δ ≤ 1` and `18 L H ≤ N`: with probability at least `1 - δ`,
`V^π̂_h ≥ V*_h - 8 H √(2 L H / N)` and `Q^π̂_h ≥ Q*_h - 8 H √(2 L H / N)` at every step `h`
(`le_streamMeasure_forall_optValue_sub_le_value_optPolicy_empirical`). For `0 < ε ≤ H` and
`N ≥ 128 H ^ 3 L / ε ^ 2`, the greedy optimal policy of the empirical MDP is `ε`-optimal at every
step with probability at least `1 - δ`
(`le_streamMeasure_forall_optValue_sub_le_value_optPolicy_empirical_of_le`).

[LWCGC24, Theorem 4] states the level `log (H S A / δ)` with unspecified constants. The level here
is the one the proof gives: the union bound runs over the `2 (m + 1)` families of levels, the `H`
steps and the `S A` pairs. Since `m + 1 ≤ H` for `H ≥ 1`, `L ≤ log (4 H ^ 2 S A / δ)`, which is
at most `2 log (2 H S A / δ)`.

## Main statements

* `EpisodicMDP.le_streamMeasure_forall_optValue_sub_le_value_optPolicy_empirical`:
  the values and action values of the greedy optimal policy of the empirical MDP are within
  `8 H √(2 L H / N)` of the optimal ones, with probability at least `1 - δ`.
* `EpisodicMDP.le_streamMeasure_forall_optValue_sub_le_value_optPolicy_empirical_of_le`:
  model-based planning is `ε`-optimal over the full range `ε ∈ (0, H]` [LWCGC24, Theorem 4].

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24],
  Theorem 4 and §7.3 (arXiv:2005.12900)
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning Bandits
open Real (log)

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  [Fintype 𝓢] [Fintype 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]

variable (𝓢 𝓐) in
/-- The level `log (4 (m + 1) H S A / δ)` of the union bound is nonnegative for `δ ≤ 1` and
`H ≥ 1`. -/
private lemma log_level_nonneg {H : ℕ} (hH : 0 < H) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ log (4 * (Nat.clog 4 H + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) := by
  rcases isEmpty_or_nonempty 𝓢 with h𝓢 | h𝓢
  · simp
  refine Real.log_nonneg ((one_le_div hδ).2 (hδ1.trans ?_))
  have h₁ : (1 : ℝ) ≤ Fintype.card 𝓢 := by exact_mod_cast Fintype.card_pos
  have h₂ : (1 : ℝ) ≤ Fintype.card 𝓐 := by exact_mod_cast Fintype.card_pos
  have h₃ : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have h₄ : (1 : ℝ) ≤ 4 * (Nat.clog 4 H + 1) := by
    have : (0 : ℝ) ≤ Nat.clog 4 H := Nat.cast_nonneg _
    linarith
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
    _ ≤ 4 * (Nat.clog 4 H + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 := by gcongr

/-- **Model-based planning in finite horizon** [LWCGC24, Theorem 4], explicit form. Let `M` be an
episodic MDP with horizon `H`, `S` states, `A` actions and rewards in `[0, 1]`, and let
`m = ⌈log₄ H⌉` and `L = log (4 (m + 1) H S A / δ)` for `0 < δ ≤ 1`. If `18 L H ≤ N`, then under
the generative model of `M`, with probability at least `1 - δ`, the greedy optimal policy `π̂` of
the empirical episodic MDP of `N` samples per step and pair satisfies
`V^π̂_h ≥ V*_h - 8 H √(2 L H / N)` and `Q^π̂_h ≥ Q*_h - 8 H √(2 L H / N)` at every step `h`. -/
theorem le_streamMeasure_forall_optValue_sub_le_value_optPolicy_empirical (M : EpisodicMDP 𝓢 𝓐)
    (hM : M.RewardsIn (Set.Icc 0 1)) (H N : ℕ) [NeZero N] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : 18 * log (4 * (Nat.clog 4 H + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) * H ≤ N) :
    1 - δ ≤ (streamMeasure (M.generativeKernel H)).real {ω |
      (∀ h s, M.optValue H h s -
          8 * H * √(2 * log (4 * (Nat.clog 4 H + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) *
            H / N) ≤
        M.value H (fun h ↦ Kernel.deterministic ((M.empirical H N ω).optPolicy H h)
          (measurable_optPolicy h)) h s) ∧
      ∀ h s a, M.optQValue H h s a -
          8 * H * √(2 * log (4 * (Nat.clog 4 H + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) *
            H / N) ≤
        M.qValue H (fun h ↦ Kernel.deterministic ((M.empirical H N ω).optPolicy H h)
          (measurable_optPolicy h)) h s a} := by
  have : Countable 𝓢 := Finite.to_countable
  have : Countable 𝓐 := Finite.to_countable
  set m := Nat.clog 4 H with hm_def
  have hm : H ≤ 4 ^ m := Nat.le_pow_clog (by norm_num) H
  set L := log (4 * (m + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) with hL_def
  have hN₀ : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  -- the levels of the greedy optimal policies of `M` (`i = false`) and of the empirical MDP
  -- (`i = true`), rescaled to `[0, 1]`
  have key := le_streamMeasure_forall_abs_integral_sub_integral_empirical_trans_lt M H N
    (fun (j : Fin (m + 1) × Bool) h M' s ↦ ((H : ℝ) * √H ^ (j.1 : ℕ))⁻¹ *
      M.valueLevel H (fun h' ↦ Kernel.deterministic ((bif j.2 then M' else M).optPolicy H h')
        (measurable_optPolicy h')) j.1 (h + 1) s) ?_ zero_lt_one ?_ hδ
  rotate_left
  · -- the levels of `π̂` from the step `h + 1` on only depend on the transitions after `h`
    intro j h _ M₁ M₂ hrew htr
    funext s
    congr 1
    refine congrFun (valueLevel_congr (h₀ := h + 1) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun h' hh' ↦ ?_) _ le_rfl) s
    ext1 s'
    rw [Kernel.deterministic_apply, Kernel.deterministic_apply]
    cases j.2
    · rfl
    · simp only [Bool.cond_true]
      rw [optPolicy_congr (h₀ := h + 1) (fun h'' hh'' ↦ htr h'' (by omega))
        (fun h'' _ ↦ by funext s a; simp only [meanReward_def, hrew]) hh']
  · intro j h hh ω s
    have hb : (0 : ℝ) < H * √H ^ (j.1 : ℕ) := by
      have : (0 : ℝ) < H := Nat.cast_pos.2 (by omega)
      positivity
    have hV := valueLevel_mem_Icc (M := M) (H := H)
      (π := fun h' ↦ Kernel.deterministic ((bif j.2 then M.empirical H N ω else M).optPolicy H h')
        (measurable_optPolicy h')) hM j.1 (h + 1) s
    rw [one_mul] at hV
    exact ⟨mul_nonneg (inv_nonneg.2 hb.le) hV.1, by rw [inv_mul_le_iff₀ hb, mul_one]; exact hV.2⟩
  have hcard : (Fintype.card (Fin (m + 1) × Bool) : ℝ) = 2 * (m + 1) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    push_cast
    ring
  rw [hcard, show 2 * (2 * ((m : ℝ) + 1)) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ =
    4 * (m + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ by ring, ← hL_def] at key
  refine key.trans (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  set Me := M.empirical H N ω with hMe
  -- it suffices to bound the values: the action values follow
  suffices hval : ∀ h s, M.optValue H h s - 8 * H * √(2 * L * H / N) ≤
      M.value H (fun h ↦ Kernel.deterministic (Me.optPolicy H h) (measurable_optPolicy h)) h s from
    ⟨hval, optQValue_sub_le_qValue_of_forall_optValue_sub_le hM hval⟩
  intro h s
  rcases Nat.eq_zero_or_pos H with hH | hH
  · rw [optValue_of_le (by omega), value_of_le (by omega)]
    simp [hH]
  have hL : 0 ≤ L := log_level_nonneg 𝓢 𝓐 hH hδ hδ1
  -- the deterministic part for the two greedy optimal policies
  have hi (i : Bool) (h : ℕ) (s : 𝓢) :
      |Me.value H (fun h' ↦ Kernel.deterministic ((bif i then Me else M).optPolicy H h')
          (measurable_optPolicy h')) h s -
        M.value H (fun h' ↦ Kernel.deterministic ((bif i then Me else M).optPolicy H h')
          (measurable_optPolicy h')) h s| ≤ 4 * 1 * H * √(2 * L * H / N) := by
    refine abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le (empirical_reward M ω) hM _
      hm hN₀ hL hN (fun l hl j hj s' ↦ ?_) h s
    simp only [stateKernel_deterministic_apply]
    have hb : (0 : ℝ) < H * √H ^ l := by
      have : (0 : ℝ) < H := Nat.cast_pos.2 hH
      positivity
    have h₁ := hω (⟨l, Nat.lt_succ_of_le hl⟩, i) j hj (s', (bif i then Me else M).optPolicy H j s')
    simp only [integral_const_mul, variance_const_mul] at h₁
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hb), show ∀ v : ℝ,
      2 * (((H : ℝ) * √H ^ l)⁻¹ ^ 2 * v) * L / N = ((H : ℝ) * √H ^ l)⁻¹ ^ 2 * (2 * v * L / N)
      from fun v ↦ by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.2 hb.le),
      sub_zero, one_mul] at h₁
    rw [abs_sub_comm]
    have h₂ := mul_lt_mul_of_pos_left h₁ hb
    rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul, one_mul] at h₂
    exact h₂.le.trans_eq (by ring)
  have h₁ := hi false h s
  have h₂ := hi true h s
  simp only [Bool.cond_false, Bool.cond_true] at h₁ h₂
  have h₃ : Me.value H (fun h' ↦ Kernel.deterministic (M.optPolicy H h') (measurable_optPolicy h'))
      h s ≤ Me.optValue H h s := value_le_optValue ((rewardsIn_empirical M ω).2 hM) h s
  rw [value_optPolicy] at h₁ h₂
  rw [abs_le] at h₁ h₂
  linarith

/-- **Model-based planning in finite horizon is `ε`-optimal over the full range of accuracies**
[LWCGC24, Theorem 4]. Let `M` be an episodic MDP with horizon `H`, `S` states, `A` actions and
rewards in `[0, 1]`, and let `m = ⌈log₄ H⌉` and `L = log (4 (m + 1) H S A / δ)` for
`0 < δ ≤ 1`. For `0 < ε ≤ H` and `N ≥ 128 H ^ 3 L / ε ^ 2` samples per step and state-action
pair, under the generative model of `M`, with probability at least `1 - δ`, the greedy optimal
policy `π̂` of the empirical episodic MDP satisfies `V^π̂_h ≥ V*_h - ε` and
`Q^π̂_h ≥ Q*_h - ε` at every step `h`. -/
theorem le_streamMeasure_forall_optValue_sub_le_value_optPolicy_empirical_of_le
    (M : EpisodicMDP 𝓢 𝓐) (hM : M.RewardsIn (Set.Icc 0 1)) (H N : ℕ) [NeZero N] {δ ε : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hεH : ε ≤ H)
    (hN : 128 * H ^ 3 * log (4 * (Nat.clog 4 H + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) /
      ε ^ 2 ≤ N) :
    1 - δ ≤ (streamMeasure (M.generativeKernel H)).real {ω |
      (∀ h s, M.optValue H h s - ε ≤
        M.value H (fun h ↦ Kernel.deterministic ((M.empirical H N ω).optPolicy H h)
          (measurable_optPolicy h)) h s) ∧
      ∀ h s a, M.optQValue H h s a - ε ≤
        M.qValue H (fun h ↦ Kernel.deterministic ((M.empirical H N ω).optPolicy H h)
          (measurable_optPolicy h)) h s a} := by
  set L := log (4 * (Nat.clog 4 H + 1) * H * Fintype.card 𝓢 * Fintype.card 𝓐 / δ) with hL_def
  have hN₀ : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  have hH : (0 : ℝ) < H := hε.trans_le hεH
  have hL : 0 ≤ L := log_level_nonneg 𝓢 𝓐 (Nat.cast_pos.1 hH) hδ hδ1
  -- `128 H ^ 3 L ≤ N ε ^ 2`, hence `18 L H ≤ N` and `8 H √(2 L H / N) ≤ ε`
  have hN' : 128 * H ^ 3 * L ≤ N * ε ^ 2 := (div_le_iff₀ (by positivity)).1 hN
  have hN18 : 18 * L * H ≤ N := by
    have : (H : ℝ) ^ 2 * (18 * L * H) ≤ H ^ 2 * N := by
      nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hεH 2) hN₀.le,
        mul_nonneg hL hH.le, pow_pos hH 3]
    exact le_of_mul_le_mul_left this (by positivity)
  have hdev : 8 * H * √(2 * L * H / N) ≤ ε := by
    rw [show 8 * (H : ℝ) * √(2 * L * H / N) = √(128 * H ^ 3 * L / N) by
      rw [show 128 * (H : ℝ) ^ 3 * L / N = (8 * H) ^ 2 * (2 * L * H / N) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
    rw [Real.sqrt_le_left hε.le, div_le_iff₀ hN₀]
    linarith
  refine (le_streamMeasure_forall_optValue_sub_le_value_optPolicy_empirical M hM H N hδ hδ1
    hN18).trans (measureReal_mono (fun ω hω ↦ ⟨fun h s ↦ ?_, fun h s a ↦ ?_⟩)
      (measure_ne_top _ _))
  · linarith [hω.1 h s]
  · linarith [hω.2 h s a]

end Learning.MDP.Episodic.EpisodicMDP
