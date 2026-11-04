/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Optimal

/-!
# Greedy policies for approximate action values in an episodic MDP

Let `M : EpisodicMDP 𝓢 𝓐` be an episodic MDP with bounded rewards, a nonempty countable action
set and a horizon `H`. Many learning algorithms (least-squares value iteration, fitted
Q-iteration) compute estimates `Q̂_h` of the optimal action values by backward induction and play
the deterministic Markov policy `π̂` greedy for them: `π̂_h s` maximizes `Q̂_h (s, ·)`. This file
bounds the suboptimality of `π̂` by the errors of the estimates.

* **Q-error amplification.** If `|Q̂_k - Q*_k| ≤ ε_k` at every step `k < H`, then every greedy
  `π̂` has `V*_h - V^π̂_h ≤ 2 ∑_{h ≤ k < H} ε_k`. This is the episodic form of the bound
  `V^π_Q ≥ V* - 2 ‖Q - Q*‖ / (1 - γ)` of discounted MDPs [AJKS, Lemma 1.11].
* **Bellman residuals** [AJKS, Lemma 3.4]. If `Q̂_H = 0` and the estimates have Bellman residuals
  at most `ε`,
  `|Q̂_k (s, a) - (r_k (s, a) + ∫ (s' ↦ ⨆ a', Q̂_{k+1} (s', a')) dP_k (s, a))| ≤ ε` for `k < H`,
  then `|Q̂_h - Q*_h| ≤ (H - h) ε` and `|⨆ a, Q̂_h (·, a) - V*_h| ≤ (H - h) ε`, and every greedy
  `π̂` has `V*_h - V^π̂_h ≤ 2 (H - h) ^ 2 ε`; at the first step, `V^π̂_0 ≥ V*_0 - 2 H ^ 2 ε`.

[AJKS] state these bounds with sup norms and a constant error. Here they are pointwise, with an
explicit bound on the errors (one per step for the amplification bound), on a measurable state
space and a countable action set. The estimates need no measurability for the amplification
bound, and measurability in the state for the Bellman residual bounds.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.optValue_sub_value_le_of_abs_sub_optQValue_le`: Q-error
  amplification for greedy policies.
* `Learning.MDP.Episodic.EpisodicMDP.abs_iSup_sub_optValue_le`,
  `Learning.MDP.Episodic.EpisodicMDP.abs_sub_optQValue_le`: estimates with Bellman residuals at
  most `ε` are within `(H - h) ε` of the optimal values [AJKS, Lemma 3.4 (1)].
* `Learning.MDP.Episodic.EpisodicMDP.optValue_sub_value_le`: their greedy policies are
  `2 (H - h) ^ 2 ε`-optimal [AJKS, Lemma 3.4 (2)].

## References

* [AJKS] A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022, Lemma 1.11 and Lemma 3.4.
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning LMLExplore

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Countable 𝓐]
  [Nonempty 𝓐] {M : EpisodicMDP 𝓢 𝓐} {H h : ℕ} {a b : ℝ} {Q : ℕ → 𝓢 → 𝓐 → ℝ}

/-! ### Q-error amplification -/

/-- **Q-error amplification for greedy policies** (the episodic form of [AJKS, Lemma 1.11]): for
bounded rewards and a nonempty countable action set, if the estimates `Q k` are within `ε k` of
the optimal action values at every step `k < H`, then the deterministic Markov policy `d` greedy
for them, `Q k s a' ≤ Q k s (d k s)`, has a value within `2 ∑_{h ≤ k < H} ε k` of the optimal
value at the step `h`. -/
theorem optValue_sub_value_le_of_abs_sub_optQValue_le (hM : M.RewardsIn (Set.Icc a b))
    {ε : ℕ → ℝ} (hQ : ∀ k < H, ∀ s a', |Q k s a' - M.optQValue H k s a'| ≤ ε k)
    {d : ℕ → 𝓢 → 𝓐} (hd : ∀ k, Measurable (d k))
    (hgreedy : ∀ k < H, ∀ s a', Q k s a' ≤ Q k s (d k s)) (h : ℕ) (s : 𝓢) :
    M.optValue H h s - M.value H (fun k ↦ Kernel.deterministic (d k) (hd k)) h s ≤
      2 * ∑ k ∈ Ico h H, ε k := by
  by_cases hh : h < H
  · set π := fun k ↦ Kernel.deterministic (d k) (hd k)
    -- the greedy action loses at most `2 ε h` in optimal action value
    have h₁ : M.optValue H h s ≤ M.optQValue H h s (d h s) + 2 * ε h := by
      rw [optValue_of_lt hh]
      refine ciSup_le fun a' ↦ ?_
      have h₁ := abs_sub_le_iff.1 (hQ h hh s a')
      have h₂ := abs_sub_le_iff.1 (hQ h hh s (d h s))
      linarith [hgreedy h hh s a']
    -- after the first step, the optimal value and the value of `π` differ by the remaining sum
    have h₂ : M.optQValue H h s (d h s) - M.qValue H π h s (d h s) ≤
        2 * ∑ k ∈ Ico (h + 1) H, ε k := by
      have hV : Integrable (M.optValue H (h + 1)) (M.trans h (s, d h s)) :=
        integrable_optValue hM (h + 1)
      have hVπ : Integrable (M.value H π (h + 1)) (M.trans h (s, d h s)) :=
        integrable_value hM (h + 1)
      rw [optQValue_def, qValue_def, add_sub_add_left_eq_sub, ← integral_sub hV hVπ]
      calc ∫ s', (M.optValue H (h + 1) s' - M.value H π (h + 1) s') ∂(M.trans h (s, d h s))
          ≤ ∫ _, 2 * ∑ k ∈ Ico (h + 1) H, ε k ∂(M.trans h (s, d h s)) :=
            integral_mono (hV.sub hVπ) (integrable_const _) fun s' ↦
              optValue_sub_value_le_of_abs_sub_optQValue_le hM hQ hd hgreedy (h + 1) s'
        _ = 2 * ∑ k ∈ Ico (h + 1) H, ε k := by simp
    rw [value_deterministic_of_lt hd hh, sum_eq_sum_Ico_succ_bot hh]
    linarith
  · rw [optValue_of_le (not_lt.1 hh), value_of_le (not_lt.1 hh), Ico_eq_empty_of_le (not_lt.1 hh)]
    simp
termination_by H - h

/-! ### Estimates with small Bellman residuals -/

/-- For bounded rewards, if a measurable `V` is within `c` of the optimal value at the step
`h + 1`, then its backup `r_h + P_h V` is within `c` of the optimal action value at the step
`h`. -/
private lemma abs_meanReward_add_integral_sub_optQValue_le (hM : M.RewardsIn (Set.Icc a b))
    {V : 𝓢 → ℝ} (hV : Measurable V) {c : ℝ}
    (hVc : ∀ s', |V s' - M.optValue H (h + 1) s'| ≤ c) (s : 𝓢) (a' : 𝓐) :
    |M.meanReward h s a' + ∫ s', V s' ∂(M.trans h (s, a')) - M.optQValue H h s a'| ≤ c := by
  have hV' : Integrable (M.optValue H (h + 1)) (M.trans h (s, a')) := integrable_optValue hM (h + 1)
  have hint : Integrable V (M.trans h (s, a')) := by
    simpa using
      (integrable_of_abs_le (hV.sub (measurable_optValue (h + 1))) hVc _).add hV'
  rw [optQValue_def, add_sub_add_left_eq_sub, ← integral_sub hint hV']
  exact abs_integral_le_of_abs_le hVc

variable {ε : ℝ}

/-- One step of backward induction: for bounded rewards, if the estimate `Q h` at a step `h < H`
has Bellman residual at most `ε` with respect to the estimates `Q (h + 1)`, measurable in the
state, whose suprema are within `(H - (h + 1)) ε` of the optimal value at the step `h + 1`, then
`Q h` is within `(H - h) ε` of the optimal action value at the step `h`. -/
private lemma abs_sub_optQValue_le_of_abs_iSup_sub_optValue_le (hM : M.RewardsIn (Set.Icc a b))
    (hQm : ∀ a', Measurable fun s ↦ Q (h + 1) s a') (hh : h < H)
    (hε : ∀ s a', |Q h s a' -
      (M.meanReward h s a' + ∫ s', ⨆ a'', Q (h + 1) s' a'' ∂(M.trans h (s, a')))| ≤ ε)
    (hc : ∀ s', |(⨆ a'', Q (h + 1) s' a'') - M.optValue H (h + 1) s'| ≤ (H - (h + 1) : ℕ) * ε)
    (s : 𝓢) (a' : 𝓐) :
    |Q h s a' - M.optQValue H h s a'| ≤ (H - h : ℕ) * ε := by
  have := (abs_sub_le _ _ _).trans <| add_le_add (hε s a')
    (abs_meanReward_add_integral_sub_optQValue_le hM (V := fun s' ↦ ⨆ a'', Q (h + 1) s' a'')
      (.iSup hQm) hc s a')
  rw [show H - h = H - (h + 1) + 1 by omega]
  push_cast
  linarith

/-- **Accuracy of the estimates of the optimal value** ([AJKS, Lemma 3.4 (1)]): for bounded
rewards and a nonempty countable action set, let `Q k` be estimates of the optimal action values,
measurable in the state, with `Q H = 0` and Bellman residuals at most `ε` at every step `k < H`:
`|Q k s a' - (r_k (s, a') + ∫ (s' ↦ ⨆ a'', Q (k + 1) s' a'') dP_k (s, a'))| ≤ ε`. Then the
estimate `⨆ a', Q h s a'` of the optimal value at a step `h ≤ H` is within `(H - h) ε` of it. -/
theorem abs_iSup_sub_optValue_le (hM : M.RewardsIn (Set.Icc a b))
    (hQm : ∀ k a', Measurable fun s ↦ Q k s a') (hQH : ∀ s a', Q H s a' = 0)
    (hε : ∀ k < H, ∀ s a', |Q k s a' -
      (M.meanReward k s a' + ∫ s', ⨆ a'', Q (k + 1) s' a'' ∂(M.trans k (s, a')))| ≤ ε)
    {h : ℕ} (hh : h ≤ H) (s : 𝓢) :
    |(⨆ a', Q h s a') - M.optValue H h s| ≤ (H - h : ℕ) * ε := by
  obtain hh | rfl := hh.lt_or_eq
  · -- the estimates at the step `h` are within `(H - h) ε` of the optimal action values
    have hc := abs_iSup_sub_optValue_le hM hQm hQH hε (Nat.succ_le_of_lt hh)
    have hQ := abs_sub_optQValue_le_of_abs_iSup_sub_optValue_le hM (hQm (h + 1)) hh (hε h hh) hc s
    have hbdd : BddAbove (Set.range (M.optQValue H h s)) :=
      ⟨_, Set.forall_mem_range.2 fun a' ↦ (optQValue_mem_Icc hM hh s a').2⟩
    rw [optValue_of_lt hh]
    exact abs_ciSup_sub_ciSup_le hbdd hQ
  · simp [hQH]
termination_by H - h

/-- **Accuracy of the estimates of the optimal action values** ([AJKS, Lemma 3.4 (1)]): for
bounded rewards and a nonempty countable action set, let `Q k` be estimates of the optimal action
values, measurable in the state, with `Q H = 0` and Bellman residuals at most `ε` at every step
`k < H`. Then the estimate `Q h` is within `(H - h) ε` of the optimal action value at every step
`h < H`. -/
theorem abs_sub_optQValue_le (hM : M.RewardsIn (Set.Icc a b))
    (hQm : ∀ k a', Measurable fun s ↦ Q k s a') (hQH : ∀ s a', Q H s a' = 0)
    (hε : ∀ k < H, ∀ s a', |Q k s a' -
      (M.meanReward k s a' + ∫ s', ⨆ a'', Q (k + 1) s' a'' ∂(M.trans k (s, a')))| ≤ ε)
    (hh : h < H) (s : 𝓢) (a' : 𝓐) :
    |Q h s a' - M.optQValue H h s a'| ≤ (H - h : ℕ) * ε :=
  abs_sub_optQValue_le_of_abs_iSup_sub_optValue_le hM (hQm (h + 1)) hh (hε h hh)
    (abs_iSup_sub_optValue_le hM hQm hQH hε (Nat.succ_le_of_lt hh)) s a'

/-- **Greedy policies for estimates with small Bellman residuals** ([AJKS, Lemma 3.4 (2)]): for
bounded rewards and a nonempty countable action set, let `Q k` be estimates of the optimal action
values, measurable in the state, with `Q H = 0` and Bellman residuals at most `ε` at every step
`k < H`. Then the deterministic Markov policy `d` greedy for them, `Q k s a' ≤ Q k s (d k s)`, has
a value within `2 (H - h) ^ 2 ε` of the optimal value at the step `h`; at the first step,
`V^d_0 ≥ V*_0 - 2 H ^ 2 ε`. -/
theorem optValue_sub_value_le (hM : M.RewardsIn (Set.Icc a b))
    (hQm : ∀ k a', Measurable fun s ↦ Q k s a') (hQH : ∀ s a', Q H s a' = 0)
    (hε : ∀ k < H, ∀ s a', |Q k s a' -
      (M.meanReward k s a' + ∫ s', ⨆ a'', Q (k + 1) s' a'' ∂(M.trans k (s, a')))| ≤ ε)
    {d : ℕ → 𝓢 → 𝓐} (hd : ∀ k, Measurable (d k))
    (hgreedy : ∀ k < H, ∀ s a', Q k s a' ≤ Q k s (d k s)) (h : ℕ) (s : 𝓢) :
    M.optValue H h s - M.value H (fun k ↦ Kernel.deterministic (d k) (hd k)) h s ≤
      2 * (H - h : ℕ) ^ 2 * ε := by
  refine (optValue_sub_value_le_of_abs_sub_optQValue_le hM
    (fun k hk ↦ abs_sub_optQValue_le hM hQm hQH hε hk) hd hgreedy h s).trans ?_
  by_cases hh : h < H
  · have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε h hh s (Classical.arbitrary 𝓐))
    -- each of the `H - h` terms of the sum is at most `(H - h) ε`
    have hsum : ∑ k ∈ Ico h H, ((H - k : ℕ) : ℝ) * ε ≤ #(Ico h H) • ((H - h : ℕ) * ε) :=
      sum_le_card_nsmul _ _ _ fun k hk ↦ by
        gcongr
        exact (mem_Ico.1 hk).1
    rw [Nat.card_Ico, nsmul_eq_mul] at hsum
    nlinarith
  · simp [Ico_eq_empty_of_le (not_lt.1 hh), Nat.sub_eq_zero_of_le (not_lt.1 hh)]

end Learning.MDP.Episodic.EpisodicMDP
