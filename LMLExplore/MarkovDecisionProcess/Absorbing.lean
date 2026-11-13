/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Simulation

/-!
# Absorbing modifications of a Markov decision process

Let `M : MDP 𝓢 𝓐 𝓡` be an MDP, `s` a state and `c` a reward. The `s`-absorbing modification
`M.absorbing s c` is identical to `M` except at the state `s`: there, every action leads back to
`s` and yields the deterministic reward `c`. The transitions and the rewards of the other states
are those of `M`, so that the modification only depends on `M` through its rows outside `s`
(`Learning.MDP.absorbing_congr`).

For real rewards, a discount factor `γ < 1` and `c = (1 - γ) u`, every stationary policy has value
`u` at `s` in the modification. These MDPs are the decoupling device of Agarwal, Kakade and Yang
[AKY20, §4.2]. Applied to an empirical MDP estimated from a generative model, the modification at
`s` is a function of the samples drawn at the other states only (`Learning.MDP.absorbing_congr`),
so that its values are independent of the samples drawn at `s`. Nothing is lost at the level of
values by a good choice of `u`:
* if `u = v^π s` then the modification has the same value `v^π` as `M` (and the same optimal value
  for `u = v* s`) [AKY20, Lemma 7];
* the values and the optimal values of the modification are `1`-Lipschitz in `u` for the sup
  norm [AKY20, Lemma 8].

Together, these bound the distance from the value of `M` to the value of a modification by the
error `|v s - u|` at `s` alone. This is what lets the modifications for a finite net of values `u`
approximate the value of `M`.

## Main definitions

* `Learning.MDP.absorbing M s c`: the `s`-absorbing modification of `M` with reward `c` at `s`.

## Main statements

* `Learning.MDP.absorbing_congr`: the modification at `s` only depends on the rows of the
  transition and reward kernels outside `s`.
* `Learning.MDP.value_absorbing_self`, `Learning.MDP.optValue_absorbing_self`: the value of every
  stationary policy and the optimal value of `M.absorbing s c` at `s` are `c / (1 - γ)`.
* `Learning.MDP.value_absorbing_value`, `Learning.MDP.optValue_absorbing_optValue`: with
  `c = (1 - γ) v^π s`, the modification has value `v^π`; with `c = (1 - γ) v* s`, it has optimal
  value `v*` [AKY20, Lemma 7].
* `Learning.MDP.abs_qValue_absorbing_sub_qValue_absorbing_le`,
  `Learning.MDP.abs_optQValue_absorbing_sub_optQValue_absorbing_le`: the action values and the
  optimal action values of the modifications with rewards `c` and `c'` differ by at most
  `|c - c'| / (1 - γ)` [AKY20, Lemma 8], and so do the values and the optimal values.
* `Learning.MDP.abs_value_sub_value_absorbing_le`,
  `Learning.MDP.abs_optValue_sub_optValue_absorbing_le`: the values of `M` and of the modification
  with reward `(1 - γ) u` differ by at most `|v^π s - u|`, and the optimal values by at most
  `|v* s - u|`.

## References

* [A. Agarwal, S. Kakade and L. F. Yang, *Model-based reinforcement learning with a generative
  model is minimax optimal*, COLT 2020][AKY20], §4.2
-/

public section

open MeasureTheory ProbabilityTheory Set LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡} [MeasurableSingletonClass 𝓢] {s : 𝓢}

/-! ### The absorbing modification -/

open scoped Classical in
/-- The `s`-absorbing modification of the MDP `M` with reward `c`: in the state `s`, every action
leads back to `s` with the deterministic reward `c`; in every other state, the transitions and the
rewards are those of `M`. -/
noncomputable def absorbing (M : MDP 𝓢 𝓐 𝓡) (s : 𝓢) (c : 𝓡) : MDP 𝓢 𝓐 𝓡 where
  P := Kernel.piecewise (measurable_fst (measurableSet_singleton s))
    (Kernel.const _ (Measure.dirac s)) M.P
  R := Kernel.piecewise (measurable_fst (measurableSet_singleton s))
    (Kernel.const _ (Measure.dirac c)) M.R

variable (M M' : MDP 𝓢 𝓐 𝓡) (c : 𝓡)

/-- In the absorbing state, every action leads back to it. -/
@[simp]
lemma absorbing_P_apply_self (a : 𝓐) : (M.absorbing s c).P (s, a) = Measure.dirac s := by
  simp [absorbing, Kernel.piecewise_apply]

/-- In the absorbing state, every action yields the reward `c`. -/
@[simp]
lemma absorbing_R_apply_self (a : 𝓐) : (M.absorbing s c).R (s, a) = Measure.dirac c := by
  simp [absorbing, Kernel.piecewise_apply]

/-- Outside the absorbing state, the transitions are those of `M`. -/
lemma absorbing_P_apply_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) : (M.absorbing s c).P p = M.P p := by
  simp [absorbing, Kernel.piecewise_apply, hp]

/-- Outside the absorbing state, the rewards are those of `M`. -/
lemma absorbing_R_apply_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) : (M.absorbing s c).R p = M.R p := by
  simp [absorbing, Kernel.piecewise_apply, hp]

/-- The transitions of the absorbing modification do not depend on the reward at the absorbing
state. -/
lemma absorbing_P_eq_absorbing_P (c' : 𝓡) : (M.absorbing s c).P = (M.absorbing s c').P := by
  ext1 p
  by_cases hp : p.1 = s
  · obtain ⟨_, a⟩ := p
    cases hp
    simp
  · rw [absorbing_P_apply_of_ne _ _ hp, absorbing_P_apply_of_ne _ _ hp]

variable {M M'} in
/-- **Decoupling**: the `s`-absorbing modification of an MDP only depends on its transitions and
rewards outside `s`. -/
theorem absorbing_congr (hP : ∀ p : 𝓢 × 𝓐, p.1 ≠ s → M.P p = M'.P p)
    (hR : ∀ p : 𝓢 × 𝓐, p.1 ≠ s → M.R p = M'.R p) : M.absorbing s c = M'.absorbing s c := by
  ext1
  · ext1 p
    by_cases hp : p.1 = s
    · obtain ⟨_, a⟩ := p
      cases hp
      simp
    · rw [absorbing_P_apply_of_ne _ _ hp, absorbing_P_apply_of_ne _ _ hp, hP p hp]
  · ext1 p
    by_cases hp : p.1 = s
    · obtain ⟨_, a⟩ := p
      cases hp
      simp
    · rw [absorbing_R_apply_of_ne _ _ hp, absorbing_R_apply_of_ne _ _ hp, hR p hp]

/-! ### Rewards and Bellman operators of the modification -/

section Real

variable (M : MDP 𝓢 𝓐 ℝ) (c : ℝ) {γ : ℝ≥0} {π : Kernel 𝓢 𝓐} {v : 𝓢 → ℝ} {C : ℝ}

/-- In the absorbing state, the mean reward is `c`. -/
@[simp]
lemma meanReward_absorbing_self (a : 𝓐) : meanReward (M.absorbing s c).R (s, a) = c := by
  simp [meanReward_def]

/-- Outside the absorbing state, the mean rewards are those of `M`. -/
lemma meanReward_absorbing_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) :
    meanReward (M.absorbing s c).R p = meanReward M.R p := by
  rw [meanReward_def, meanReward_def, absorbing_R_apply_of_ne _ _ hp]

variable {M c}

/-- If the rewards of `M` are bounded by `C`, those of its absorbing modification with reward `c`
are bounded by `max C |c|`. -/
lemma ae_abs_absorbing_R_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    ∀ᵐ x ∂((M.absorbing s c).R p), |x| ≤ max C |c| := by
  by_cases hp : p.1 = s
  · obtain ⟨_, a⟩ := p
    cases hp
    simp
  · rw [absorbing_R_apply_of_ne _ _ hp]
    exact (hR p).mono fun _ hx ↦ hx.trans (le_max_left _ _)

/-- The mean rewards of two absorbing modifications at the same state differ by at most the
difference of their rewards at that state. -/
lemma abs_meanReward_absorbing_sub_le (c' : ℝ) (p : 𝓢 × 𝓐) :
    |meanReward (M.absorbing s c).R p - meanReward (M.absorbing s c').R p| ≤ |c - c'| := by
  by_cases hp : p.1 = s
  · obtain ⟨_, a⟩ := p
    cases hp
    simp
  · simp [meanReward_absorbing_of_ne _ _ hp]

/-- In the absorbing state, the lookahead of `v` at every action is `c + γ * v s`. -/
@[simp]
lemma lookahead_absorbing_self (a : 𝓐) :
    (M.absorbing s c).lookahead γ v (s, a) = c + γ * v s := by
  simp [lookahead_def, integral_dirac]

/-- Outside the absorbing state, the lookahead is that of `M`. -/
lemma lookahead_absorbing_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) :
    (M.absorbing s c).lookahead γ v p = M.lookahead γ v p := by
  rw [lookahead_def, lookahead_def, meanReward_absorbing_of_ne _ _ hp,
    absorbing_P_apply_of_ne _ _ hp]

/-- In the absorbing state, the evaluation operator of every stationary policy maps `v` to
`c + γ * v s`. -/
@[simp]
lemma bellmanEval_absorbing_self [IsMarkovKernel π] :
    (M.absorbing s c).bellmanEval γ π v s = c + γ * v s := by
  simp [bellmanEval_def]

/-- Outside the absorbing state, the evaluation operators are those of `M`. -/
lemma bellmanEval_absorbing_of_ne {s' : 𝓢} (hs' : s' ≠ s) :
    (M.absorbing s c).bellmanEval γ π v s' = M.bellmanEval γ π v s' := by
  simp_rw [bellmanEval_def, lookahead_absorbing_of_ne (v := v) (γ := γ) (p := (s', _)) hs']

/-- In the absorbing state, the optimality operator maps `v` to `c + γ * v s`. -/
@[simp]
lemma bellman_absorbing_self [Nonempty 𝓐] : (M.absorbing s c).bellman γ v s = c + γ * v s := by
  simp [bellman_def]

/-- Outside the absorbing state, the optimality operator is that of `M`. -/
lemma bellman_absorbing_of_ne {s' : 𝓢} (hs' : s' ≠ s) :
    (M.absorbing s c).bellman γ v s' = M.bellman γ v s' := by
  simp_rw [bellman_def, lookahead_absorbing_of_ne (v := v) (γ := γ) (p := (s', _)) hs']

/-! ### Values in the absorbing state -/

/-- With bounded rewards and `γ < 1`, every stationary policy has value `c / (1 - γ)` at the
absorbing state of `M.absorbing s c`. -/
theorem value_absorbing_self [IsMarkovKernel π] (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.absorbing s c).value γ π s = c / (1 - γ) := by
  -- the value at `s` solves `x = c + γ * x`
  have h := congrFun (bellmanEval_value (π := π) hγ (ae_abs_absorbing_R_le (c := c) (s := s) hR)) s
  rw [bellmanEval_absorbing_self] at h
  rw [eq_div_iff (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne']
  linarith

/-- With bounded rewards and `γ < 1`, the action value of every stationary policy at the absorbing
state of `M.absorbing s c` is `c / (1 - γ)`, for every action. -/
theorem qValue_absorbing_self [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (a : 𝓐) :
    (M.absorbing s c).qValue γ π (s, a) = c / (1 - γ) := by
  rw [qValue_eq_lookahead, lookahead_absorbing_self, value_absorbing_self hγ hR]
  have : (1 - γ : ℝ) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne'
  field_simp
  ring

/-! ### The modification at the value of `M` -/

/-- **The modification at the value of a policy** [AKY20, Lemma 7]: with bounded rewards and
`γ < 1`, the `s`-absorbing modification of `M` with reward `(1 - γ) v^π s` has the same value
`v^π` as `M` for the stationary policy `π`. -/
theorem value_absorbing_value [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.absorbing s ((1 - γ) * M.value γ π s)).value γ π = M.value γ π := by
  refine (eq_value_of_bellmanEval_eq hγ (ae_abs_absorbing_R_le hR) (measurable_value hγ hR)
    (abs_value_le hγ hR) ?_).symm
  ext s'
  by_cases hs' : s' = s
  · subst hs'
    rw [bellmanEval_absorbing_self]
    ring
  · rw [bellmanEval_absorbing_of_ne hs', bellmanEval_value hγ hR]

/-- With bounded rewards and `γ < 1`, outside the absorbing state, the `s`-absorbing modification
of `M` with reward `(1 - γ) v^π s` has the same action values as `M` for the stationary policy
`π`. -/
theorem qValue_absorbing_value_of_ne [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) :
    (M.absorbing s ((1 - γ) * M.value γ π s)).qValue γ π p = M.qValue γ π p := by
  rw [qValue_eq_lookahead, qValue_eq_lookahead, value_absorbing_value hγ hR,
    lookahead_absorbing_of_ne hp]

/-! ### Lipschitz dependence on the reward at the absorbing state -/

/-- **The action values are Lipschitz in the absorbing reward** [AKY20, Lemma 8]: with bounded
rewards and `γ < 1`, the action values of a stationary policy in the `s`-absorbing modifications
of `M` with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. For `c = (1 - γ) u` and
`c' = (1 - γ) u'`, this is `|u - u'|`. -/
theorem abs_qValue_absorbing_sub_qValue_absorbing_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (p : 𝓢 × 𝓐) :
    |(M.absorbing s c).qValue γ π p - (M.absorbing s c').qValue γ π p| ≤ |c - c'| / (1 - γ) := by
  simpa using abs_qValue_sub_qValue_le hγ (ae_abs_absorbing_R_le hR) (ae_abs_absorbing_R_le hR)
    (abs_meanReward_absorbing_sub_le c') (ε := 0)
    (fun q ↦ by rw [absorbing_P_eq_absorbing_P M c c', sub_self, abs_zero]) p

/-- **The values are Lipschitz in the absorbing reward** [AKY20, Lemma 8]: with bounded rewards
and `γ < 1`, the values of a stationary policy in the `s`-absorbing modifications of `M` with
rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_value_absorbing_sub_value_absorbing_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.absorbing s c).value γ π s' - (M.absorbing s c').value γ π s'| ≤ |c - c'| / (1 - γ) := by
  simpa using abs_value_sub_value_le hγ (ae_abs_absorbing_R_le hR) (ae_abs_absorbing_R_le hR)
    (abs_meanReward_absorbing_sub_le c') (ε := 0)
    (fun q ↦ by rw [absorbing_P_eq_absorbing_P M c c', sub_self, abs_zero]) s'

/-- With bounded rewards and `γ < 1`, the value of a stationary policy in `M` and in the
`s`-absorbing modification of `M` with reward `(1 - γ) u` differ by at most `|v^π s - u|`: the
error of the modification is controlled by the error of `u` at `s` alone. -/
theorem abs_value_sub_value_absorbing_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (u : ℝ) (s' : 𝓢) :
    |M.value γ π s' - (M.absorbing s ((1 - γ) * u)).value γ π s'| ≤ |M.value γ π s - u| := by
  have h1γ : 0 < 1 - (γ : ℝ) := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have h := abs_value_absorbing_sub_value_absorbing_le (s := s) (π := π) hγ hR
    ((1 - γ) * M.value γ π s)
    ((1 - γ) * u) s'
  rwa [value_absorbing_value hγ hR, ← mul_sub, abs_mul, abs_of_pos h1γ,
    mul_div_cancel_left₀ _ h1γ.ne'] at h

/-! ### Optimal values -/

section Optimal

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐]

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal value of
`M.absorbing s c` at the absorbing state is `c / (1 - γ)`. -/
theorem optValue_absorbing_self (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.absorbing s c).optValue γ s = c / (1 - γ) := by
  -- the optimal value at `s` solves `x = c + γ * x`
  have h := congrFun (bellman_optValue hγ (ae_abs_absorbing_R_le (c := c) (s := s) hR)) s
  rw [bellman_absorbing_self] at h
  rw [eq_div_iff (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne']
  linarith

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal action value of
`M.absorbing s c` at the absorbing state is `c / (1 - γ)`, for every action. -/
theorem optQValue_absorbing_self (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (a : 𝓐) :
    (M.absorbing s c).optQValue γ (s, a) = c / (1 - γ) := by
  rw [optQValue_eq_lookahead, lookahead_absorbing_self, optValue_absorbing_self hγ hR]
  have : (1 - γ : ℝ) ≠ 0 := (sub_pos.2 (NNReal.coe_lt_one.2 hγ)).ne'
  field_simp
  ring

/-- **The modification at the optimal value** [AKY20, Lemma 7]: with finitely many actions,
bounded rewards and `γ < 1`, the `s`-absorbing modification of `M` with reward `(1 - γ) v* s`
has the same optimal value `v*` as `M`. -/
theorem optValue_absorbing_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.absorbing s ((1 - γ) * M.optValue γ s)).optValue γ = M.optValue γ := by
  refine (eq_optValue_of_bellman_eq hγ (ae_abs_absorbing_R_le hR) (measurable_optValue hγ hR)
    (abs_optValue_le hγ hR) ?_).symm
  ext s'
  by_cases hs' : s' = s
  · subst hs'
    rw [bellman_absorbing_self]
    ring
  · rw [bellman_absorbing_of_ne hs', bellman_optValue hγ hR]

/-- With finitely many actions, bounded rewards and `γ < 1`, outside the absorbing state, the
`s`-absorbing modification of `M` with reward `(1 - γ) v* s` has the same optimal action values
as `M`. -/
theorem optQValue_absorbing_optValue_of_ne (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) :
    (M.absorbing s ((1 - γ) * M.optValue γ s)).optQValue γ p = M.optQValue γ p := by
  rw [optQValue_eq_lookahead, optQValue_eq_lookahead, optValue_absorbing_optValue hγ hR,
    lookahead_absorbing_of_ne hp]

/-- **The optimal action values are Lipschitz in the absorbing reward** [AKY20, Lemma 8]: with
finitely many actions, bounded rewards and `γ < 1`, the optimal action values of the `s`-absorbing
modifications of `M` with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. For
`c = (1 - γ) u` and `c' = (1 - γ) u'`, this is `|u - u'|`. -/
theorem abs_optQValue_absorbing_sub_optQValue_absorbing_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (p : 𝓢 × 𝓐) :
    |(M.absorbing s c).optQValue γ p - (M.absorbing s c').optQValue γ p| ≤
      |c - c'| / (1 - γ) := by
  simpa using abs_optQValue_sub_optQValue_le hγ (ae_abs_absorbing_R_le hR)
    (ae_abs_absorbing_R_le hR) (abs_meanReward_absorbing_sub_le c') (ε := 0)
    (fun q ↦ by rw [absorbing_P_eq_absorbing_P M c c', sub_self, abs_zero]) p

/-- **The optimal values are Lipschitz in the absorbing reward** [AKY20, Lemma 8]: with finitely
many actions, bounded rewards and `γ < 1`, the optimal values of the `s`-absorbing modifications
of `M` with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_optValue_absorbing_sub_optValue_absorbing_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.absorbing s c).optValue γ s' - (M.absorbing s c').optValue γ s'| ≤
      |c - c'| / (1 - γ) := by
  simpa using abs_optValue_sub_optValue_le hγ (ae_abs_absorbing_R_le hR)
    (ae_abs_absorbing_R_le hR) (abs_meanReward_absorbing_sub_le c') (ε := 0)
    (fun q ↦ by rw [absorbing_P_eq_absorbing_P M c c', sub_self, abs_zero]) s'

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal values of `M` and of the
`s`-absorbing modification of `M` with reward `(1 - γ) u` differ by at most `|v* s - u|`: the
error of the modification is controlled by the error of `u` at `s` alone. -/
theorem abs_optValue_sub_optValue_absorbing_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (u : ℝ) (s' : 𝓢) :
    |M.optValue γ s' - (M.absorbing s ((1 - γ) * u)).optValue γ s'| ≤ |M.optValue γ s - u| := by
  have h1γ : 0 < 1 - (γ : ℝ) := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have h := abs_optValue_absorbing_sub_optValue_absorbing_le (s := s) hγ hR
    ((1 - γ) * M.optValue γ s)
    ((1 - γ) * u) s'
  rwa [optValue_absorbing_optValue hγ hR, ← mul_sub, abs_mul, abs_of_pos h1γ,
    mul_div_cancel_left₀ _ h1γ.ne'] at h

end Optimal

end Real

end Learning.MDP
