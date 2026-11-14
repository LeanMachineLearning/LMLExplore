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

The modification is an instance of the redirection `M.redirect hS s c` of `M` on a measurable set
`S` of state-action pairs: at the pairs of `S`, the next state is `s` and the reward is `c`, and
elsewhere the transitions and the rewards are those of `M`. The `s`-absorbing modification is the
redirection on the pairs at `s`; the state-action absorbing modifications
(`LMLExplore.MarkovDecisionProcess.Absorbing.StateAction`) are the redirections on a single pair.
The decoupling and the Lipschitz dependence on `c` are proved once for redirections.

## Main definitions

* `Learning.MDP.redirect M hS s c`: the redirection of `M` on `S` to `s` with reward `c`.
* `Learning.MDP.absorbing M s c`: the `s`-absorbing modification of `M` with reward `c` at `s`.

## Main statements

* `Learning.MDP.redirect_congr`: the redirection on `S` only depends on the rows of the transition
  and reward kernels outside `S`.
* `Learning.MDP.abs_qValue_redirect_sub_qValue_redirect_le`,
  `Learning.MDP.abs_optQValue_redirect_sub_optQValue_redirect_le`: the action values and the
  optimal action values of the redirections with rewards `c` and `c'` differ by at most
  `|c - c'| / (1 - γ)`, and so do the values and the optimal values.

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
  {m𝓡 : MeasurableSpace 𝓡} {S : Set (𝓢 × 𝓐)} {s : 𝓢}

/-! ### Redirection on a set of state-action pairs -/

open scoped Classical in
/-- The redirection of the MDP `M` on a measurable set `S` of state-action pairs to the state `s`
with reward `c`: at the pairs of `S`, the next state is `s` and the reward is `c`; at every other
pair, the transitions and the rewards are those of `M`. The `s`-absorbing modification
(`Learning.MDP.absorbing`) is the redirection on the pairs at `s`, and the state-action absorbing
modification at `p` (`Learning.MDP.saAbsorbing`) is the redirection on `{p}` to `p.1`. -/
noncomputable def redirect (M : MDP 𝓢 𝓐 𝓡) (hS : MeasurableSet S) (s : 𝓢) (c : 𝓡) :
    MDP 𝓢 𝓐 𝓡 where
  P := Kernel.piecewise hS (Kernel.const _ (Measure.dirac s)) M.P
  R := Kernel.piecewise hS (Kernel.const _ (Measure.dirac c)) M.R

variable (M M' : MDP 𝓢 𝓐 𝓡) (hS : MeasurableSet S) (c : 𝓡)

/-- On `S`, the redirection moves to `s`. -/
lemma redirect_P_apply_of_mem {q : 𝓢 × 𝓐} (hq : q ∈ S) :
    (M.redirect hS s c).P q = Measure.dirac s := by
  simp [redirect, Kernel.piecewise_apply, hq]

/-- On `S`, the reward of the redirection is `c`. -/
lemma redirect_R_apply_of_mem {q : 𝓢 × 𝓐} (hq : q ∈ S) :
    (M.redirect hS s c).R q = Measure.dirac c := by
  simp [redirect, Kernel.piecewise_apply, hq]

/-- Outside `S`, the transitions of the redirection are those of `M`. -/
lemma redirect_P_apply_of_notMem {q : 𝓢 × 𝓐} (hq : q ∉ S) : (M.redirect hS s c).P q = M.P q := by
  simp [redirect, Kernel.piecewise_apply, hq]

/-- Outside `S`, the rewards of the redirection are those of `M`. -/
lemma redirect_R_apply_of_notMem {q : 𝓢 × 𝓐} (hq : q ∉ S) : (M.redirect hS s c).R q = M.R q := by
  simp [redirect, Kernel.piecewise_apply, hq]

/-- The transitions of the redirection do not depend on its reward. -/
lemma redirect_P_eq_redirect_P (c' : 𝓡) : (M.redirect hS s c).P = (M.redirect hS s c').P := by
  ext1 q
  by_cases hq : q ∈ S
  · rw [redirect_P_apply_of_mem _ _ _ hq, redirect_P_apply_of_mem _ _ _ hq]
  · rw [redirect_P_apply_of_notMem _ _ _ hq, redirect_P_apply_of_notMem _ _ _ hq]

variable {M M'} in
/-- **Decoupling**: the redirection of an MDP on `S` only depends on its transitions and rewards
outside `S`. -/
theorem redirect_congr (hP : ∀ q ∉ S, M.P q = M'.P q) (hR : ∀ q ∉ S, M.R q = M'.R q) :
    M.redirect hS s c = M'.redirect hS s c := by
  ext1
  · ext1 q
    by_cases hq : q ∈ S
    · rw [redirect_P_apply_of_mem _ _ _ hq, redirect_P_apply_of_mem _ _ _ hq]
    · rw [redirect_P_apply_of_notMem _ _ _ hq, redirect_P_apply_of_notMem _ _ _ hq, hP q hq]
  · ext1 q
    by_cases hq : q ∈ S
    · rw [redirect_R_apply_of_mem _ _ _ hq, redirect_R_apply_of_mem _ _ _ hq]
    · rw [redirect_R_apply_of_notMem _ _ _ hq, redirect_R_apply_of_notMem _ _ _ hq, hR q hq]

section Real

variable (M : MDP 𝓢 𝓐 ℝ) (hS : MeasurableSet S) (c : ℝ) {γ : ℝ≥0} {π : Kernel 𝓢 𝓐} {v : 𝓢 → ℝ}
  {C : ℝ}

/-- On `S`, the mean reward of the redirection is `c`. -/
lemma meanReward_redirect_of_mem {q : 𝓢 × 𝓐} (hq : q ∈ S) :
    meanReward (M.redirect hS s c).R q = c := by
  simp [meanReward_def, redirect_R_apply_of_mem _ _ _ hq]

/-- Outside `S`, the mean rewards of the redirection are those of `M`. -/
lemma meanReward_redirect_of_notMem {q : 𝓢 × 𝓐} (hq : q ∉ S) :
    meanReward (M.redirect hS s c).R q = meanReward M.R q := by
  rw [meanReward_def, meanReward_def, redirect_R_apply_of_notMem _ _ _ hq]

variable [MeasurableSingletonClass 𝓢] in
/-- On `S`, the lookahead of `v` in the redirection is `c + γ * v s`. -/
lemma lookahead_redirect_of_mem {q : 𝓢 × 𝓐} (hq : q ∈ S) :
    (M.redirect hS s c).lookahead γ v q = c + γ * v s := by
  rw [lookahead_def, meanReward_redirect_of_mem _ _ _ hq, redirect_P_apply_of_mem _ _ _ hq,
    integral_dirac]

/-- Outside `S`, the lookahead in the redirection is that of `M`. -/
lemma lookahead_redirect_of_notMem {q : 𝓢 × 𝓐} (hq : q ∉ S) :
    (M.redirect hS s c).lookahead γ v q = M.lookahead γ v q := by
  rw [lookahead_def, lookahead_def, meanReward_redirect_of_notMem _ _ _ hq,
    redirect_P_apply_of_notMem _ _ _ hq]

variable {M c}

/-- If the rewards of `M` are bounded by `C`, those of its redirection with reward `c` are bounded
by `max C |c|`. -/
lemma ae_abs_redirect_R_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (q : 𝓢 × 𝓐) :
    ∀ᵐ x ∂((M.redirect hS s c).R q), |x| ≤ max C |c| := by
  by_cases hq : q ∈ S
  · simp [redirect_R_apply_of_mem _ _ _ hq]
  · rw [redirect_R_apply_of_notMem _ _ _ hq]
    exact (hR q).mono fun _ hx ↦ hx.trans (le_max_left _ _)

/-- The mean rewards of two redirections on the same set to the same state differ by at most the
difference of their rewards. -/
lemma abs_meanReward_redirect_sub_le (c' : ℝ) (q : 𝓢 × 𝓐) :
    |meanReward (M.redirect hS s c).R q - meanReward (M.redirect hS s c').R q| ≤ |c - c'| := by
  by_cases hq : q ∈ S
  · simp [meanReward_redirect_of_mem _ _ _ hq]
  · simp [meanReward_redirect_of_notMem _ _ _ hq]

variable (M c) in
/-- Two redirections that differ only in their rewards have the same transitions: the transition
term of the simulation bounds vanishes. -/
private lemma abs_integral_redirect_P_sub_le (c' : ℝ) (f : 𝓢 → ℝ) (q : 𝓢 × 𝓐) :
    |∫ x, f x ∂((M.redirect hS s c).P q) - ∫ x, f x ∂((M.redirect hS s c').P q)| ≤ 0 := by
  rw [redirect_P_eq_redirect_P M hS c c', sub_self, abs_zero]

/-- **The action values are Lipschitz in the reward of the redirection**: with bounded rewards and
`γ < 1`, the action values of a stationary policy in the redirections of `M` on `S` to `s` with
rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_qValue_redirect_sub_qValue_redirect_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (q : 𝓢 × 𝓐) :
    |(M.redirect hS s c).qValue γ π q - (M.redirect hS s c').qValue γ π q| ≤
      |c - c'| / (1 - γ) := by
  simpa using abs_qValue_sub_qValue_le hγ (ae_abs_redirect_R_le hS hR) (ae_abs_redirect_R_le hS hR)
    (abs_meanReward_redirect_sub_le hS c') (abs_integral_redirect_P_sub_le M hS c c' _) q

/-- **The values are Lipschitz in the reward of the redirection**: with bounded rewards and
`γ < 1`, the values of a stationary policy in the redirections of `M` on `S` to `s` with rewards
`c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_value_redirect_sub_value_redirect_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.redirect hS s c).value γ π s' - (M.redirect hS s c').value γ π s'| ≤
      |c - c'| / (1 - γ) := by
  simpa using abs_value_sub_value_le hγ (ae_abs_redirect_R_le hS hR) (ae_abs_redirect_R_le hS hR)
    (abs_meanReward_redirect_sub_le hS c') (abs_integral_redirect_P_sub_le M hS c c' _) s'

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐]

/-- **The optimal action values are Lipschitz in the reward of the redirection**: with finitely
many actions, bounded rewards and `γ < 1`, the optimal action values of the redirections of `M` on
`S` to `s` with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_optQValue_redirect_sub_optQValue_redirect_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (q : 𝓢 × 𝓐) :
    |(M.redirect hS s c).optQValue γ q - (M.redirect hS s c').optQValue γ q| ≤
      |c - c'| / (1 - γ) := by
  simpa using abs_optQValue_sub_optQValue_le hγ (ae_abs_redirect_R_le hS hR)
    (ae_abs_redirect_R_le hS hR) (abs_meanReward_redirect_sub_le hS c')
    (abs_integral_redirect_P_sub_le M hS c c' _) q

/-- **The optimal values are Lipschitz in the reward of the redirection**: with finitely many
actions, bounded rewards and `γ < 1`, the optimal values of the redirections of `M` on `S` to `s`
with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_optValue_redirect_sub_optValue_redirect_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.redirect hS s c).optValue γ s' - (M.redirect hS s c').optValue γ s'| ≤
      |c - c'| / (1 - γ) := by
  simpa using abs_optValue_sub_optValue_le hγ (ae_abs_redirect_R_le hS hR)
    (ae_abs_redirect_R_le hS hR) (abs_meanReward_redirect_sub_le hS c')
    (abs_integral_redirect_P_sub_le M hS c c' _) s'

end Real

/-! ### The absorbing modification -/

variable [MeasurableSingletonClass 𝓢]

/-- The `s`-absorbing modification of the MDP `M` with reward `c`: in the state `s`, every action
leads back to `s` with the deterministic reward `c`; in every other state, the transitions and the
rewards are those of `M`. It is the redirection of `M` on the pairs at `s` to `s`. -/
noncomputable def absorbing (M : MDP 𝓢 𝓐 𝓡) (s : 𝓢) (c : 𝓡) : MDP 𝓢 𝓐 𝓡 :=
  M.redirect (measurable_fst (measurableSet_singleton s)) s c

/-- The `s`-absorbing modification is the redirection on the pairs at `s` to `s`. -/
lemma absorbing_def :
    M.absorbing s c = M.redirect (measurable_fst (measurableSet_singleton s)) s c :=
  (rfl)

/-- In the absorbing state, every action leads back to it. -/
@[simp]
lemma absorbing_P_apply_self (a : 𝓐) : (M.absorbing s c).P (s, a) = Measure.dirac s :=
  redirect_P_apply_of_mem M _ c rfl

/-- In the absorbing state, every action yields the reward `c`. -/
@[simp]
lemma absorbing_R_apply_self (a : 𝓐) : (M.absorbing s c).R (s, a) = Measure.dirac c :=
  redirect_R_apply_of_mem M _ c rfl

/-- Outside the absorbing state, the transitions are those of `M`. -/
lemma absorbing_P_apply_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) : (M.absorbing s c).P p = M.P p :=
  redirect_P_apply_of_notMem M _ c hp

/-- Outside the absorbing state, the rewards are those of `M`. -/
lemma absorbing_R_apply_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) : (M.absorbing s c).R p = M.R p :=
  redirect_R_apply_of_notMem M _ c hp

/-- The transitions of the absorbing modification do not depend on the reward at the absorbing
state. -/
lemma absorbing_P_eq_absorbing_P (c' : 𝓡) : (M.absorbing s c).P = (M.absorbing s c').P :=
  redirect_P_eq_redirect_P M _ c c'

variable {M M'} in
/-- **Decoupling**: the `s`-absorbing modification of an MDP only depends on its transitions and
rewards outside `s`. -/
theorem absorbing_congr (hP : ∀ p : 𝓢 × 𝓐, p.1 ≠ s → M.P p = M'.P p)
    (hR : ∀ p : 𝓢 × 𝓐, p.1 ≠ s → M.R p = M'.R p) : M.absorbing s c = M'.absorbing s c :=
  redirect_congr _ c hP hR

/-! ### Rewards and Bellman operators of the modification -/

section Real

variable (M : MDP 𝓢 𝓐 ℝ) (c : ℝ) {γ : ℝ≥0} {π : Kernel 𝓢 𝓐} {v : 𝓢 → ℝ} {C : ℝ}

/-- In the absorbing state, the mean reward is `c`. -/
@[simp]
lemma meanReward_absorbing_self (a : 𝓐) : meanReward (M.absorbing s c).R (s, a) = c :=
  meanReward_redirect_of_mem M _ c rfl

/-- Outside the absorbing state, the mean rewards are those of `M`. -/
lemma meanReward_absorbing_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) :
    meanReward (M.absorbing s c).R p = meanReward M.R p :=
  meanReward_redirect_of_notMem M _ c hp

variable {M c}

/-- If the rewards of `M` are bounded by `C`, those of its absorbing modification with reward `c`
are bounded by `max C |c|`. -/
lemma ae_abs_absorbing_R_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    ∀ᵐ x ∂((M.absorbing s c).R p), |x| ≤ max C |c| :=
  ae_abs_redirect_R_le _ hR p

/-- The mean rewards of two absorbing modifications at the same state differ by at most the
difference of their rewards at that state. -/
lemma abs_meanReward_absorbing_sub_le (c' : ℝ) (p : 𝓢 × 𝓐) :
    |meanReward (M.absorbing s c).R p - meanReward (M.absorbing s c').R p| ≤ |c - c'| :=
  abs_meanReward_redirect_sub_le _ c' p

/-- In the absorbing state, the lookahead of `v` at every action is `c + γ * v s`. -/
@[simp]
lemma lookahead_absorbing_self (a : 𝓐) :
    (M.absorbing s c).lookahead γ v (s, a) = c + γ * v s :=
  lookahead_redirect_of_mem M _ c rfl

/-- Outside the absorbing state, the lookahead is that of `M`. -/
lemma lookahead_absorbing_of_ne {p : 𝓢 × 𝓐} (hp : p.1 ≠ s) :
    (M.absorbing s c).lookahead γ v p = M.lookahead γ v p :=
  lookahead_redirect_of_notMem M _ c hp

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
    |(M.absorbing s c).qValue γ π p - (M.absorbing s c').qValue γ π p| ≤ |c - c'| / (1 - γ) :=
  abs_qValue_redirect_sub_qValue_redirect_le _ hγ hR c c' p

/-- **The values are Lipschitz in the absorbing reward** [AKY20, Lemma 8]: with bounded rewards
and `γ < 1`, the values of a stationary policy in the `s`-absorbing modifications of `M` with
rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_value_absorbing_sub_value_absorbing_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.absorbing s c).value γ π s' - (M.absorbing s c').value γ π s'| ≤ |c - c'| / (1 - γ) :=
  abs_value_redirect_sub_value_redirect_le _ hγ hR c c' s'

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
      |c - c'| / (1 - γ) :=
  abs_optQValue_redirect_sub_optQValue_redirect_le _ hγ hR c c' p

/-- **The optimal values are Lipschitz in the absorbing reward** [AKY20, Lemma 8]: with finitely
many actions, bounded rewards and `γ < 1`, the optimal values of the `s`-absorbing modifications
of `M` with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_optValue_absorbing_sub_optValue_absorbing_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.absorbing s c).optValue γ s' - (M.absorbing s c').optValue γ s'| ≤
      |c - c'| / (1 - γ) :=
  abs_optValue_redirect_sub_optValue_redirect_le _ hγ hR c c' s'

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
