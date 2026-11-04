/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Episodic.Value
import Mathlib.Analysis.Convex.Integral

/-!
# Optimal values and the optimal policy of an episodic MDP

For an episodic MDP `M : EpisodicMDP 𝓢 𝓐` and a horizon `H`, the optimal values `V*_h` and the
optimal action values `Q*_h` are defined by the optimality equations, by backward induction from
`V*_H = 0`:
* `Q*_h (s, a) = r_h (s, a) + ∫ V*_{h+1} dP_h (s, a)`;
* `V*_h s = ⨆ a, Q*_h (s, a)` for `h < H`, and `V*_h = 0` for `h ≥ H`.

For a finite action set, the greedy deterministic Markov policy `π*`, which plays at the step `h`
an action maximizing `Q*_h (s, ·)` (chosen by LML's measurable `argmax`), has the value `V*_h` at
every step, and no Markov policy has a larger value: `V^π_h ≤ V*_h` for every Markov policy `π`,
already for countable action sets. These are the comparisons that the regret and sample
complexity bounds of episodic learning start from: the regret of a learner is the sum over the
episodes of `V*_0 - V^{π_k}_0` for the policies `π_k` it plays.

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
* `Learning.MDP.Episodic.EpisodicMDP.optValue_mem_Icc`: for rewards in `[a, b]`, the optimal
  value at the step `h` lies in `[(H - h) a, (H - h) b]`.
* `Learning.MDP.Episodic.EpisodicMDP.value_le_optValue`,
  `Learning.MDP.Episodic.EpisodicMDP.qValue_le_optQValue`: for bounded rewards and a countable
  action set, the values of every Markov policy are at most the optimal values.
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

/-- If the optimal value at the step `h + 1` is measurable, then the optimal action value at the
step `h` is a measurable function of the state-action pair. -/
private lemma measurable_optQValue_of (hV : Measurable (M.optValue H (h + 1))) :
    Measurable fun p : 𝓢 × 𝓐 ↦ M.optQValue H h p.1 p.2 :=
  (M.measurable_meanReward h).add
    (hV.stronglyMeasurable.integral_kernel (κ := M.trans h)).measurable

section Countable

variable [Countable 𝓐]

/-- For a countable action set, the optimal value at every step is a measurable function of the
state. -/
theorem measurable_optValue (h : ℕ) : Measurable (M.optValue H h) := by
  by_cases hh : h < H
  · have hQ := measurable_optQValue_of (M := M) (measurable_optValue (h + 1))
    rw [funext (optValue_of_lt hh)]
    exact Measurable.iSup fun a ↦ hQ.comp measurable_prodMk_right
  · rw [funext (optValue_of_le (not_lt.1 hh))]
    exact measurable_const
termination_by H - h

/-- For a countable action set, the optimal action value at every step is a measurable function
of the state-action pair. -/
theorem measurable_optQValue (h : ℕ) :
    Measurable fun p : 𝓢 × 𝓐 ↦ M.optQValue H h p.1 p.2 :=
  measurable_optQValue_of (measurable_optValue (h + 1))

variable {a b : ℝ}

/-- For rewards in `[a, b]`, if the optimal value at the step `h + 1` lies in
`[(H - (h + 1)) a, (H - (h + 1)) b]`, then the optimal action value at the step `h < H` lies in
`[(H - h) a, (H - h) b]`. -/
private lemma optQValue_mem_Icc_of (hM : M.RewardsIn (Set.Icc a b)) (hh : h < H)
    (hV : ∀ s', M.optValue H (h + 1) s' ∈
      Set.Icc ((H - (h + 1) : ℕ) * a) ((H - (h + 1) : ℕ) * b))
    (s : 𝓢) (a' : 𝓐) :
    M.optQValue H h s a' ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) := by
  have hr := meanReward_mem_Icc hM h s a'
  have hPV := Convex.integral_mem (μ := M.trans h (s, a')) (convex_Icc _ _) isClosed_Icc
    (.of_forall hV) (.of_mem_Icc _ _ (measurable_optValue (h + 1)).aemeasurable (.of_forall hV))
  rw [optQValue_def, show H - h = H - (h + 1) + 1 by omega, Nat.cast_add_one]
  constructor <;> linarith [hr.1, hr.2, hPV.1, hPV.2]

variable [Nonempty 𝓐]

/-- For rewards in `[a, b]` and a nonempty countable action set, the optimal value at the step
`h` lies in `[(H - h) a, (H - h) b]`. -/
theorem optValue_mem_Icc (hM : M.RewardsIn (Set.Icc a b)) (h : ℕ) (s : 𝓢) :
    M.optValue H h s ∈ Set.Icc ((H - h : ℕ) * a) ((H - h : ℕ) * b) := by
  by_cases hh : h < H
  · -- the optimal action values lie in the same interval, and so does their supremum
    have hQ := optQValue_mem_Icc_of hM hh (fun s' ↦ optValue_mem_Icc hM (h + 1) s') s
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
  optQValue_mem_Icc_of hM hh (optValue_mem_Icc hM (h + 1)) s a'

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
  have hVπ := value_mem_Icc (H := H) (π := π) hM (h + 1)
  have hV' := optValue_mem_Icc (H := H) hM (h + 1)
  rw [qValue_def, optQValue_def]
  gcongr M.meanReward h s a' + ?_
  exact integral_mono (μ := M.trans h (s, a'))
    (.of_mem_Icc _ _ (measurable_value (h + 1)).aemeasurable (.of_forall hVπ))
    (.of_mem_Icc _ _ (measurable_optValue (h + 1)).aemeasurable (.of_forall hV')) hV

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
action value `Q*_h (s, ·)`, chosen by LML's `argmax`. -/
noncomputable def optPolicy (h : ℕ) (s : 𝓢) : 𝓐 :=
  argmax fun a ↦ M.optQValue H h s a

variable (M H) in
lemma optPolicy_def (h : ℕ) (s : 𝓢) : M.optPolicy H h s = argmax fun a ↦ M.optQValue H h s a :=
  (rfl)

/-- The greedy optimal policy is measurable at every step. -/
theorem measurable_optPolicy (h : ℕ) : Measurable (M.optPolicy H h) :=
  measurable_argmax.comp <| measurable_pi_iff.2 fun _ ↦
    (measurable_optQValue h).comp measurable_prodMk_right

/-- Before the horizon, the action of the greedy optimal policy attains the optimal value:
`Q*_h (s, π*_h s) = V*_h s`. -/
@[simp]
theorem optQValue_optPolicy (hh : h < H) (s : 𝓢) :
    M.optQValue H h s (M.optPolicy H h s) = M.optValue H h s := by
  rw [optValue_of_lt hh]
  exact le_antisymm (le_ciSup (Finite.bddAbove_range _) _)
    (ciSup_le fun a ↦ isMaxOn_argmax (fun a ↦ M.optQValue H h s a) (Set.mem_univ a))

/-- **The greedy optimal policy is optimal.** For a finite action set, the deterministic Markov
policy playing the greedy optimal policy `M.optPolicy H` has the optimal value `V*_h` at every
step. -/
theorem value_optPolicy (h : ℕ) (s : 𝓢) :
    M.value H (fun h ↦ Kernel.deterministic (M.optPolicy H h) (measurable_optPolicy h)) h s =
      M.optValue H h s := by
  by_cases hh : h < H
  · have hV := funext (value_optPolicy (h + 1))
    rw [value_of_lt hh, Kernel.integral_deterministic' (measurable_optPolicy h)
      (Measurable.stronglyMeasurable (f := M.qValue H _ h s)
        ((measurable_qValue h).comp measurable_prodMk_left)), qValue_def, hV,
      ← optQValue_def, optQValue_optPolicy hh]
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
