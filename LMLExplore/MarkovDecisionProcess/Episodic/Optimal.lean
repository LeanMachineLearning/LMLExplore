/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Value

/-!
# Optimal values and the optimal policy of an episodic MDP

For an episodic MDP `M : EpisodicMDP 𝓢 𝓐` and a horizon `H`, the optimal values `V*_h` and the
optimal action values `Q*_h` are defined by the optimality equations, by backward induction from
`V*_H = 0`:
* `Q*_h (s, a) = r_h (s, a) + ∫ V*_{h+1} dP_h (s, a)`;
* `V*_h s = ⨆ a, Q*_h (s, a)` for `h < H`, and `V*_h = 0` for `h ≥ H`.

For a finite action set, the greedy deterministic Markov policy `π*`, which plays at the step `h`
an action maximizing `Q*_h (s, ·)` (chosen by LML's measurable `argmax`), has the value `V*_h` at
every step. For bounded rewards and a nonempty countable action set, no Markov policy has a larger
value: `V^π_h ≤ V*_h` for every Markov policy `π`. These are the comparisons that the regret and
sample complexity bounds of episodic learning start from: the regret of a learner is the sum over
the episodes of `V*_0 - V^{π_k}_0` for the policies `π_k` it plays.

In the time-augmented MDP `M.augmented`, `Q*_h (s, a)` is the one-step lookahead of the optimal
values at the augmented state `(s, h)` (`lookahead_augmented_optValue`), the optimality equation
is the Bellman optimality operator of `M.augmented` (`optValue_eq_bellman_augmented`), and `π*` is
the greedy policy `MDP.greedy` of `M.augmented` for the optimal values.

The greedy optimal policy `optPolicy` follows, in its construction as an `argmax` of the
backed-up action values at each step and state, the policy `greedy` of the formalization
entropy-mdp (`github.com/RemyDegenne/entropy-mdp`, file `Essakine2026Tight/EV2026/Algorithm.lean`,
by Rémy Degenne, Apache 2.0), which is its entropic analogue.

## Main definitions

* `Learning.MDP.Episodic.EpisodicMDP.optValue M H h s`: the optimal value `V*_h s`.
* `Learning.MDP.Episodic.EpisodicMDP.optQValue M H h s a`: the optimal action value
  `Q*_h (s, a)`.
* `Learning.MDP.Episodic.EpisodicMDP.optPolicy M H h s`: the action of the greedy optimal policy
  at the step `h` and the state `s`, for a finite action set.

## Main statements

* `Learning.MDP.Episodic.EpisodicMDP.optValue_of_lt`,
  `Learning.MDP.Episodic.EpisodicMDP.optValue_of_le`: the optimality equation
  `V*_h s = ⨆ a, Q*_h (s, a)` for `h < H`, and `V*_h = 0` for `H ≤ h`.
* `Learning.MDP.Episodic.EpisodicMDP.measurable_optValue`,
  `Learning.MDP.Episodic.EpisodicMDP.measurable_optQValue`: for a countable action set, the
  optimal values are measurable.
* `Learning.MDP.Episodic.EpisodicMDP.lookahead_augmented_optValue`,
  `Learning.MDP.Episodic.EpisodicMDP.optValue_eq_bellman_augmented`: for a countable action set,
  the optimal action values and the optimality equation in the augmented MDP.
* `Learning.MDP.Episodic.EpisodicMDP.optValue_mem_Icc`: for rewards in `[a, b]` and a nonempty
  countable action set, the optimal value at the step `h` lies in `[(H - h) a, (H - h) b]`.
* `Learning.MDP.Episodic.EpisodicMDP.value_le_optValue`,
  `Learning.MDP.Episodic.EpisodicMDP.qValue_le_optQValue`: for bounded rewards and a nonempty
  countable action set, the values of every Markov policy are at most the optimal values.
* `Learning.MDP.Episodic.EpisodicMDP.optQValue_optPolicy`: for a finite action set, the greedy
  action attains the optimal value.
* `Learning.MDP.Episodic.EpisodicMDP.value_optPolicy`,
  `Learning.MDP.Episodic.EpisodicMDP.qValue_optPolicy`: for a finite action set, the values of
  the greedy optimal policy are the optimal values at every step.

## References

* [P] M. L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*,
  Wiley, 1994, §4.3 and Theorem 4.3.3.
* [AJKS] A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022, §1.2.
-/

public section

open MeasureTheory ProbabilityTheory Learning LMLExplore

namespace Learning.MDP.Episodic.EpisodicMDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-! ### Optimal values and optimal action values -/

variable (M : EpisodicMDP 𝓢 𝓐) (H : ℕ)

/-- The optimal value `V*_h s` at the step `h` and the state `s`, with the horizon `H`. It is
defined by the optimality equations, by backward induction:
`V*_h s = ⨆ a, (r_h (s, a) + ∫ V*_{h+1} dP_h (s, a))` for `h < H`, and `V*_h = 0` for `h ≥ H`.
See `optValue_of_lt` and `optValue_of_le`. The supremum is meaningful for bounded rewards and a
nonempty countable action set (`optValue_mem_Icc`). -/
noncomputable def optValue (h : ℕ) (s : 𝓢) : ℝ :=
  if h < H then
    ⨆ a, (M.meanReward h s a + ∫ s', optValue (h + 1) s' ∂(M.trans h (s, a)))
  else 0
termination_by H - h

/-- The optimal action value `Q*_h (s, a) = r_h (s, a) + ∫ V*_{h+1} dP_h (s, a)` at the step `h`,
with the horizon `H`: the reward of the action `a` at the state `s` plus the expected optimal value
of the next state. -/
noncomputable def optQValue (h : ℕ) (s : 𝓢) (a : 𝓐) : ℝ :=
  M.meanReward h s a + ∫ s', M.optValue H (h + 1) s' ∂(M.trans h (s, a))

lemma optQValue_def (h : ℕ) (s : 𝓢) (a : 𝓐) :
    M.optQValue H h s a = M.meanReward h s a + ∫ s', M.optValue H (h + 1) s' ∂(M.trans h (s, a)) :=
  (rfl)

variable {M H} {h : ℕ}

/-- **The optimality equation.** Before the horizon, the optimal value is the supremum of the
optimal action values: `V*_h s = ⨆ a, Q*_h (s, a)`. -/
theorem optValue_of_lt (hh : h < H) (s : 𝓢) :
    M.optValue H h s = ⨆ a, M.optQValue H h s a := by
  rw [optValue]
  simp only [hh, ↓reduceIte, optQValue_def]

/-- From the horizon on, the optimal value is zero. -/
theorem optValue_of_le (hh : H ≤ h) (s : 𝓢) : M.optValue H h s = 0 := by
  rw [optValue]
  simp [not_lt.2 hh]

@[simp]
lemma optValue_self (s : 𝓢) : M.optValue H H s = 0 :=
  optValue_of_le le_rfl s

/-- At the last step before the horizon, the optimal action value is the mean reward. -/
theorem optQValue_of_le_add_one (hh : H ≤ h + 1) (s : 𝓢) (a : 𝓐) :
    M.optQValue H h s a = M.meanReward h s a := by
  simp [optQValue_def, optValue_of_le hh]

/-! ### Measurability and bounds -/

section Countable

variable [Countable 𝓐]

/-- For a countable action set, the optimal value at every step is a measurable function of the
state. -/
theorem measurable_optValue (h : ℕ) : Measurable (M.optValue H h) := by
  by_cases hh : h < H
  · have hQ : Measurable fun p : 𝓢 × 𝓐 ↦ M.optQValue H h p.1 p.2 :=
      measurable_meanReward_add_integral (M := M) (measurable_optValue (h + 1)) h
    rw [funext (optValue_of_lt hh)]
    exact Measurable.iSup fun a ↦ hQ.comp measurable_prodMk_right
  · rw [funext (optValue_of_le (not_lt.1 hh))]
    exact measurable_const
termination_by H - h

/-- For a countable action set, the optimal action value at every step is a measurable function
of the state-action pair. -/
theorem measurable_optQValue (h : ℕ) :
    Measurable fun p : 𝓢 × 𝓐 ↦ M.optQValue H h p.1 p.2 :=
  measurable_meanReward_add_integral (M := M) (measurable_optValue (h + 1)) h

/-- The optimal values at all steps, read at the step of the augmented state, form a measurable
function on the augmented states. -/
private lemma measurable_optValue_augmented :
    Measurable fun q : 𝓢 × ℕ ↦ M.optValue H q.2 q.1 :=
  measurable_from_prod_countable_left fun h ↦ measurable_optValue h

variable (M H) in
/-- The optimal action value is the one-step lookahead, in the augmented MDP and without discount,
of the optimal values read at the step of the augmented state. -/
theorem lookahead_augmented_optValue (s : 𝓢) (h : ℕ) (a' : 𝓐) :
    M.augmented.lookahead 1 (fun q ↦ M.optValue H q.2 q.1) ((s, h), a') = M.optQValue H h s a' := by
  simp only [MDP.lookahead_def, meanReward_augmented, augmented_P_apply, NNReal.coe_one, one_mul,
    optQValue_def, integral_map measurable_prodMk_right.aemeasurable
      measurable_optValue_augmented.aestronglyMeasurable]

/-- **The optimality equation in the augmented MDP.** Before the horizon, the optimal value is the
Bellman optimality operator of the augmented MDP, without discount, applied to the optimal values
read at the step of the augmented state. -/
theorem optValue_eq_bellman_augmented (hh : h < H) (s : 𝓢) :
    M.optValue H h s = M.augmented.bellman 1 (fun q ↦ M.optValue H q.2 q.1) (s, h) := by
  simp only [MDP.bellman_def, lookahead_augmented_optValue, optValue_of_lt hh]

variable {a b : ℝ}

variable [Nonempty 𝓐]

/-- For rewards in `[a, b]` and a nonempty countable action set, the optimal value at the step
`h` lies in `[(H - h) a, (H - h) b]`. -/
theorem optValue_mem_Icc (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) (s : 𝓢) :
    M.optValue H h s ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) := by
  by_cases hh : h < H
  · -- the optimal action values lie in the same interval, and so does their supremum
    have hQ : ∀ a', M.optQValue H h s a' ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) :=
      meanReward_add_integral_mem_Icc hM hh (measurable_optValue (h + 1))
        (fun s' ↦ optValue_mem_Icc hM (h + 1) s') s
    have hbdd : BddAbove (Set.range (M.optQValue H h s)) :=
      ⟨_, Set.forall_mem_range.2 fun a' ↦ (hQ a').2⟩
    rw [optValue_of_lt hh]
    exact ⟨le_ciSup_of_le hbdd (Classical.arbitrary 𝓐) (hQ _).1, ciSup_le fun a' ↦ (hQ a').2⟩
  · rw [optValue_of_le (not_lt.1 hh), Nat.sub_eq_zero_of_le (not_lt.1 hh)]
    simp
termination_by H - h

/-- For rewards in `[a, b]` and a nonempty countable action set, the optimal action value at a
step `h < H` lies in `[(H - h) a, (H - h) b]`. -/
theorem optQValue_mem_Icc (hM : M.RewardsIn (Set.Icc a b)) (hh : h < H) (s : 𝓢) (a' : 𝓐) :
    M.optQValue H h s a' ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) :=
  meanReward_add_integral_mem_Icc hM hh (measurable_optValue (h + 1)) (optValue_mem_Icc hM (h + 1))
    s a'

/-- For bounded rewards and a nonempty countable action set, the optimal value at every step is
integrable with respect to every finite measure on the states. -/
theorem integrable_optValue (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) {μ : Measure 𝓢}
    [IsFiniteMeasure μ] : Integrable (M.optValue H h) μ :=
  .of_mem_Icc _ _ (measurable_optValue h).aemeasurable (.of_forall (optValue_mem_Icc hM h))

/-- For nonnegative rewards in `[0, b]`, the optimal value is nonnegative. -/
theorem optValue_nonneg (hM : M.RewardsIn (Set.Icc 0 b)) (h : ℕ) (s : 𝓢) :
    0 ≤ M.optValue H h s := by
  simpa using (optValue_mem_Icc (H := H) hM h s).1

/-- For rewards in `[a, 1]`, the optimal value at the step `h` is at most the number `H - h` of
steps to go. -/
theorem optValue_le (hM : M.RewardsIn (Set.Icc a 1)) (h : ℕ) (s : 𝓢) :
    M.optValue H h s ≤ (H - h : ℕ) := by
  simpa using (optValue_mem_Icc (H := H) hM h s).2

/-- For bounded rewards, every optimal action value before the horizon is at most the optimal
value. -/
theorem optQValue_le_optValue (hM : M.RewardsIn (Set.Icc a b)) (hh : h < H) (s : 𝓢) (a' : 𝓐) :
    M.optQValue H h s a' ≤ M.optValue H h s := by
  rw [optValue_of_lt hh]
  exact le_ciSup ⟨_, Set.forall_mem_range.2 fun a'' ↦ (optQValue_mem_Icc hM hh s a'').2⟩ a'

/-! ### Optimality among Markov policies -/

variable {π : ℕ → Kernel 𝓢 𝓐} [∀ h, IsMarkovKernel (π h)]

/-- If the value of `π` at the step `h + 1` is at most the optimal value, then so is its action
value at the step `h`. -/
private lemma qValue_le_optQValue_of (hM : M.RewardsIn (Set.Icc a b))
    (hV : ∀ s', M.value H π (h + 1) s' ≤ M.optValue H (h + 1) s') (s : 𝓢) (a' : 𝓐) :
    M.qValue H π h s a' ≤ M.optQValue H h s a' := by
  rw [qValue_def, optQValue_def]
  gcongr M.meanReward h s a' + ?_
  exact integral_mono (integrable_value hM (h + 1)) (integrable_optValue hM (h + 1)) hV

/-- **Optimality of the optimal values.** For bounded rewards and a nonempty countable action
set, the value of every Markov policy is at most the optimal value, at every step and state:
`V^π_h ≤ V*_h`. -/
theorem value_le_optValue (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) (s : 𝓢) :
    M.value H π h s ≤ M.optValue H h s := by
  by_cases hh : h < H
  · -- every action value of `π` is at most the optimal action value, hence at most `V*_h s`
    have hQ : ∀ a', M.qValue H π h s a' ≤ M.optValue H h s := fun a' ↦
      (qValue_le_optQValue_of hM (fun s' ↦ value_le_optValue hM (h + 1) s') s a').trans
        (optQValue_le_optValue hM hh s a')
    have hint : Integrable (M.qValue H π h s) (π h s) :=
      .of_mem_Icc _ _ ((measurable_qValue h).comp measurable_prodMk_left).aemeasurable
        (.of_forall (qValue_mem_Icc hM hh s))
    rw [value_of_lt hh]
    calc ∫ a', M.qValue H π h s a' ∂(π h s)
        ≤ ∫ _, M.optValue H h s ∂(π h s) := integral_mono hint (integrable_const _) hQ
      _ = M.optValue H h s := by simp
  · rw [value_of_le (not_lt.1 hh), optValue_of_le (not_lt.1 hh)]
termination_by H - h

/-- For bounded rewards and a nonempty countable action set, the action value of every Markov
policy is at most the optimal action value: `Q^π_h ≤ Q*_h`. -/
theorem qValue_le_optQValue (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) (s : 𝓢) (a' : 𝓐) :
    M.qValue H π h s a' ≤ M.optQValue H h s a' :=
  qValue_le_optQValue_of hM (value_le_optValue hM (h + 1)) s a'

end Countable

/-! ### The greedy optimal policy -/

section Greedy

variable [Fintype 𝓐] [Nonempty 𝓐]

variable (M H) in
/-- The greedy optimal policy: at the step `h` and the state `s`, an action maximizing the optimal
action value `Q*_h (s, ·)`. It is the greedy policy `MDP.greedy` of the augmented MDP, without
discount, for the optimal values, at the augmented state `(s, h)`. -/
noncomputable def optPolicy (h : ℕ) (s : 𝓢) : 𝓐 :=
  M.augmented.greedy 1 (fun q ↦ M.optValue H q.2 q.1) (s, h)

variable (M H) in
lemma optPolicy_def (h : ℕ) (s : 𝓢) :
    M.optPolicy H h s = M.augmented.greedy 1 (fun q ↦ M.optValue H q.2 q.1) (s, h) :=
  (rfl)

/-- The greedy optimal policy is measurable at every step. -/
theorem measurable_optPolicy (h : ℕ) : Measurable (M.optPolicy H h) :=
  (MDP.measurable_greedy measurable_optValue_augmented).comp measurable_prodMk_right

/-- Before the horizon, the action of the greedy optimal policy attains the optimal value:
`Q*_h (s, π*_h s) = V*_h s`. -/
@[simp]
theorem optQValue_optPolicy (hh : h < H) (s : 𝓢) :
    M.optQValue H h s (M.optPolicy H h s) = M.optValue H h s := by
  rw [← lookahead_augmented_optValue, optPolicy_def, MDP.lookahead_greedy,
    optValue_eq_bellman_augmented hh]

/-- **The greedy optimal policy is optimal.** For a finite action set, the deterministic Markov
policy playing the greedy optimal policy `M.optPolicy H` has the optimal value `V*_h` at every
step. -/
theorem value_optPolicy (h : ℕ) (s : 𝓢) :
    M.value H (fun h ↦ Kernel.deterministic (M.optPolicy H h) (measurable_optPolicy h)) h s =
      M.optValue H h s := by
  by_cases hh : h < H
  · have hV := funext (value_optPolicy (h + 1))
    rw [value_deterministic_of_lt _ hh, qValue_def, hV, ← optQValue_def, optQValue_optPolicy hh]
  · rw [value_of_le (not_lt.1 hh), optValue_of_le (not_lt.1 hh)]
termination_by H - h

/-- For a finite action set, the action values of the deterministic Markov policy playing the
greedy optimal policy `M.optPolicy H` are the optimal action values: `Q^{π*}_h = Q*_h`. -/
theorem qValue_optPolicy (h : ℕ) (s : 𝓢) (a : 𝓐) :
    M.qValue H (fun h ↦ Kernel.deterministic (M.optPolicy H h) (measurable_optPolicy h)) h s a =
      M.optQValue H h s a := by
  rw [qValue_def, funext (value_optPolicy (h + 1)), optQValue_def]

end Greedy

end Learning.MDP.Episodic.EpisodicMDP
