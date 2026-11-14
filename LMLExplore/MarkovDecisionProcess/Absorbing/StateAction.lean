/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Absorbing.Basic
import LMLExplore.Topology.UnitInterval

/-!
# State-action absorbing modifications of a Markov decision process

Let `M : MDP 𝓢 𝓐 𝓡` be an MDP, `p = (s, a)` a state-action pair and `c` a reward. The
`p`-absorbing modification `M.saAbsorbing p c` is identical to `M` except at the pair `p`: there,
the next state is `s` and the reward is the deterministic `c`. The state `s` is thus absorbing
when the action `a` is always played at `s`, and only then. The transitions and the rewards of the
other pairs, including the other actions at `s`, are those of `M`, so that the modification only
depends on `M` through its rows outside `p` (`Learning.MDP.saAbsorbing_congr`). The modification
is the redirection `Learning.MDP.redirect` of `M` on `{p}` to `s`, so that its basic properties and
its Lipschitz dependence on `c` are those of redirections.

These MDPs are the decoupling device of Li, Wei, Chi, Gu and Chen [LWCGC24, §6.3.2], a
state-action refinement of the state-absorbing MDPs of Agarwal, Kakade and Yang
(`LMLExplore.MarkovDecisionProcess.Absorbing.Basic`). Applied to an empirical MDP estimated from a
generative model, the modification at `p` with a fixed reward `c` is computed from the samples
drawn at the other pairs only, so that its optimal values and its optimal policies do not depend on
the samples drawn at `p`. Nothing is lost by a good choice of `c`, for real rewards and `γ < 1`:
* with `c = Q* p - γ v* s`, the modification has the same optimal value `v*` and the same optimal
  action value `Q*` as `M` [LWCGC24, Lemma 3]; with `c = Q^π p - γ v^π s`, it has the same value
  and the same action value for the stationary policy `π`;
* the optimal action values of the modification are `1 / (1 - γ)`-Lipschitz in `c` for the sup
  norm [LWCGC24, (88)], and so are its optimal values and the values of every stationary policy;
* if the optimal policy `d` of `M` is separated, `Q* (s', a') + ω ≤ Q* (s', d s')` for every
  state `s'` and every action `a' ≠ d s'`, then the modifications whose reward `c` is within
  `(1 - γ) ω / 4` of `Q* p - γ v* s` have the same greedy optimal policy `d`. A uniform grid of
  rewards with spacing `(1 - γ) ω / 4`, fixed in advance, thus contains a reward whose modification
  has the optimal policy `d` of `M` [LWCGC24, Lemma 4].

In [LWCGC24, Theorem 1], the separation comes from the random perturbation of the rewards
(`LMLExplore.MarkovDecisionProcess.TieBreaking`), and the union bound over the pairs and over the
grid transfers Bernstein's inequality from the fixed modifications to the optimal policy of the
empirical MDP.

## Main definitions

* `Learning.MDP.saAbsorbing M p c`: the `p`-absorbing modification of `M` with reward `c` at `p`.

## Main statements

* `Learning.MDP.saAbsorbing_congr`: the modification at `p` only depends on the rows of the
  transition and reward kernels outside `p`.
* `Learning.MDP.lookahead_saAbsorbing_of_eq`: the modification with `c + γ v s = r p + γ P v p`
  has the same lookahead of `v` as `M`.
* `Learning.MDP.optValue_saAbsorbing_optQValue`, `Learning.MDP.optQValue_saAbsorbing_optQValue`:
  with `c = Q* p - γ v* s`, the modification has optimal value `v*` and optimal action value `Q*`
  [LWCGC24, Lemma 3].
* `Learning.MDP.value_saAbsorbing_qValue`, `Learning.MDP.qValue_saAbsorbing_qValue`: the same for
  the value and the action value of a stationary policy.
* `Learning.MDP.abs_optQValue_saAbsorbing_sub_optQValue_saAbsorbing_le`: the optimal action values
  of the modifications with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`
  [LWCGC24, (88)], and so do the optimal values, the action values and the values.
* `Learning.MDP.optQValue_saAbsorbing_add_le`, `Learning.MDP.greedy_optValue_saAbsorbing_eq`: a
  policy separated by `ω > 0` in `M` is separated by `ω / 2` in, and is the greedy optimal policy
  of, the modifications whose reward is within `(1 - γ) ω / 4` of `Q* p - γ v* s`.
* `Learning.MDP.exists_greedy_optValue_saAbsorbing_eq`: **the net of modifications**
  [LWCGC24, Lemma 4]: for an optimal policy separated by `ω > 0`, a uniform grid of `K + 1`
  rewards on `[-B, B]` with `8 B ≤ (1 - γ) ω K` contains a reward whose modification has the same
  greedy optimal policy.

## References

* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], §6.3.2,
  Lemmas 3–4 and their proofs in Appendices B.2–B.3 (arXiv:2005.12900)
-/

public section

open MeasureTheory ProbabilityTheory Set LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡} [MeasurableSingletonClass 𝓢] [MeasurableSingletonClass 𝓐]
  {p : 𝓢 × 𝓐}

/-! ### The state-action absorbing modification -/

/-- The `p`-absorbing modification of the MDP `M` with reward `c`, for a state-action pair
`p = (s, a)`: at the pair `p`, the next state is `s` and the reward is `c`; at every other pair,
the transitions and the rewards are those of `M`. It is the redirection of `M` on `{p}` to `s`. -/
noncomputable def saAbsorbing (M : MDP 𝓢 𝓐 𝓡) (p : 𝓢 × 𝓐) (c : 𝓡) : MDP 𝓢 𝓐 𝓡 :=
  M.redirect (measurableSet_singleton p) p.1 c

variable (M M' : MDP 𝓢 𝓐 𝓡) (c : 𝓡)

/-- The `p`-absorbing modification is the redirection on `{p}` to `p.1`. -/
lemma saAbsorbing_def : M.saAbsorbing p c = M.redirect (measurableSet_singleton p) p.1 c :=
  (rfl)

/-- At the absorbing pair `(s, a)`, the next state is `s`. -/
@[simp]
lemma saAbsorbing_P_apply_self : (M.saAbsorbing p c).P p = Measure.dirac p.1 :=
  redirect_P_apply_of_mem M _ c rfl

/-- At the absorbing pair, the reward is `c`. -/
@[simp]
lemma saAbsorbing_R_apply_self : (M.saAbsorbing p c).R p = Measure.dirac c :=
  redirect_R_apply_of_mem M _ c rfl

/-- Outside the absorbing pair, the transitions are those of `M`. -/
lemma saAbsorbing_P_apply_of_ne {q : 𝓢 × 𝓐} (hq : q ≠ p) : (M.saAbsorbing p c).P q = M.P q :=
  redirect_P_apply_of_notMem M _ c hq

/-- Outside the absorbing pair, the rewards are those of `M`. -/
lemma saAbsorbing_R_apply_of_ne {q : 𝓢 × 𝓐} (hq : q ≠ p) : (M.saAbsorbing p c).R q = M.R q :=
  redirect_R_apply_of_notMem M _ c hq

variable {M M'} in
/-- **Decoupling**: the `p`-absorbing modification of an MDP only depends on its transitions and
rewards at the pairs other than `p`. -/
theorem saAbsorbing_congr (hP : ∀ q ≠ p, M.P q = M'.P q) (hR : ∀ q ≠ p, M.R q = M'.R q) :
    M.saAbsorbing p c = M'.saAbsorbing p c :=
  redirect_congr _ c hP hR

/-! ### Rewards and lookaheads of the modification -/

section Real

variable (M : MDP 𝓢 𝓐 ℝ) (c : ℝ) {γ : ℝ≥0} {π : Kernel 𝓢 𝓐} {v : 𝓢 → ℝ} {C : ℝ}

/-- At the absorbing pair, the mean reward is `c`. -/
@[simp]
lemma meanReward_saAbsorbing_self : meanReward (M.saAbsorbing p c).R p = c :=
  meanReward_redirect_of_mem M _ c rfl

/-- Outside the absorbing pair, the mean rewards are those of `M`. -/
lemma meanReward_saAbsorbing_of_ne {q : 𝓢 × 𝓐} (hq : q ≠ p) :
    meanReward (M.saAbsorbing p c).R q = meanReward M.R q :=
  meanReward_redirect_of_notMem M _ c hq

/-- At the absorbing pair `(s, a)`, the lookahead of `v` is `c + γ * v s`. -/
@[simp]
lemma lookahead_saAbsorbing_self : (M.saAbsorbing p c).lookahead γ v p = c + γ * v p.1 :=
  lookahead_redirect_of_mem M _ c rfl

/-- Outside the absorbing pair, the lookahead is that of `M`. -/
lemma lookahead_saAbsorbing_of_ne {q : 𝓢 × 𝓐} (hq : q ≠ p) :
    (M.saAbsorbing p c).lookahead γ v q = M.lookahead γ v q :=
  lookahead_redirect_of_notMem M _ c hq

variable {M c}

/-- If the reward `c` of the modification at `p = (s, a)` is such that `c + γ * v s` is the
lookahead `r p + γ ∫ v dP p` of `v` in `M`, then the lookaheads of `v` in the modification and in
`M` agree everywhere. -/
theorem lookahead_saAbsorbing_of_eq (h : c + γ * v p.1 = M.lookahead γ v p) :
    (M.saAbsorbing p c).lookahead γ v = M.lookahead γ v := by
  ext q
  rcases eq_or_ne q p with rfl | hq
  · rw [lookahead_saAbsorbing_self, h]
  · exact lookahead_saAbsorbing_of_ne _ _ hq

/-- If the rewards of `M` are bounded by `C`, those of its modification with reward `c` are
bounded by `max C |c|`. -/
lemma ae_abs_saAbsorbing_R_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (q : 𝓢 × 𝓐) :
    ∀ᵐ x ∂((M.saAbsorbing p c).R q), |x| ≤ max C |c| :=
  ae_abs_redirect_R_le _ hR q

/-! ### The modification at the value of a policy -/

/-- With bounded rewards and `γ < 1`, the `p`-absorbing modification of `M` with reward
`Q^π p - γ v^π s`, for `p = (s, a)`, has the same value `v^π` as `M` for the stationary policy
`π`. -/
theorem value_saAbsorbing_qValue [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.saAbsorbing p (M.qValue γ π p - γ * M.value γ π p.1)).value γ π = M.value γ π := by
  have h := lookahead_saAbsorbing_of_eq (M := M) (v := M.value γ π) (p := p)
    (c := M.qValue γ π p - γ * M.value γ π p.1) (by rw [sub_add_cancel, qValue_eq_lookahead])
  refine (eq_value_of_bellmanEval_eq hγ (ae_abs_saAbsorbing_R_le hR) (measurable_value hγ hR)
    (abs_value_le hγ hR) ?_).symm
  ext s'
  simp only [bellmanEval_def, h]
  rw [← bellmanEval_def, bellmanEval_value hγ hR]

/-- With bounded rewards and `γ < 1`, the `p`-absorbing modification of `M` with reward
`Q^π p - γ v^π s`, for `p = (s, a)`, has the same action value `Q^π` as `M` for the stationary
policy `π`. -/
theorem qValue_saAbsorbing_qValue [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.saAbsorbing p (M.qValue γ π p - γ * M.value γ π p.1)).qValue γ π = M.qValue γ π := by
  rw [qValue_eq_lookahead, value_saAbsorbing_qValue hγ hR, qValue_eq_lookahead,
    lookahead_saAbsorbing_of_eq (sub_add_cancel _ _)]

/-! ### Lipschitz dependence on the absorbing reward -/

/-- With bounded rewards and `γ < 1`, the action values of a stationary policy in the
`p`-absorbing modifications of `M` with rewards `c` and `c'` differ by at most
`|c - c'| / (1 - γ)`. -/
theorem abs_qValue_saAbsorbing_sub_qValue_saAbsorbing_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (q : 𝓢 × 𝓐) :
    |(M.saAbsorbing p c).qValue γ π q - (M.saAbsorbing p c').qValue γ π q| ≤
      |c - c'| / (1 - γ) :=
  abs_qValue_redirect_sub_qValue_redirect_le _ hγ hR c c' q

/-- With bounded rewards and `γ < 1`, the values of a stationary policy in the `p`-absorbing
modifications of `M` with rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_value_saAbsorbing_sub_value_saAbsorbing_le [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.saAbsorbing p c).value γ π s' - (M.saAbsorbing p c').value γ π s'| ≤
      |c - c'| / (1 - γ) :=
  abs_value_redirect_sub_value_redirect_le _ hγ hR c c' s'

/-! ### Optimal values and optimal policies -/

section Optimal

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐]

/-- **The modification at the optimal value** [LWCGC24, Lemma 3]: with finitely many actions,
bounded rewards and `γ < 1`, the `p`-absorbing modification of `M` with reward `Q* p - γ v* s`,
for `p = (s, a)`, has the same optimal value `v*` as `M`. -/
theorem optValue_saAbsorbing_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.saAbsorbing p (M.optQValue γ p - γ * M.optValue γ p.1)).optValue γ = M.optValue γ := by
  have h := lookahead_saAbsorbing_of_eq (M := M) (v := M.optValue γ) (p := p)
    (c := M.optQValue γ p - γ * M.optValue γ p.1) (by rw [sub_add_cancel, optQValue_eq_lookahead])
  refine (eq_optValue_of_bellman_eq hγ (ae_abs_saAbsorbing_R_le hR) (measurable_optValue hγ hR)
    (abs_optValue_le hγ hR) ?_).symm
  ext s'
  simp only [bellman_def, h]
  rw [← bellman_def, bellman_optValue hγ hR]

/-- **The modification at the optimal value** [LWCGC24, Lemma 3]: with finitely many actions,
bounded rewards and `γ < 1`, the `p`-absorbing modification of `M` with reward `Q* p - γ v* s`,
for `p = (s, a)`, has the same optimal action value `Q*` as `M`. -/
theorem optQValue_saAbsorbing_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    (M.saAbsorbing p (M.optQValue γ p - γ * M.optValue γ p.1)).optQValue γ = M.optQValue γ := by
  rw [optQValue_eq_lookahead, optValue_saAbsorbing_optQValue hγ hR, optQValue_eq_lookahead,
    lookahead_saAbsorbing_of_eq (sub_add_cancel _ _)]

/-- **The optimal action values are Lipschitz in the absorbing reward** [LWCGC24, (88)]: with
finitely many actions, bounded rewards and `γ < 1`, the optimal action values of the
`p`-absorbing modifications of `M` with rewards `c` and `c'` differ by at most
`|c - c'| / (1 - γ)`. -/
theorem abs_optQValue_saAbsorbing_sub_optQValue_saAbsorbing_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (q : 𝓢 × 𝓐) :
    |(M.saAbsorbing p c).optQValue γ q - (M.saAbsorbing p c').optQValue γ q| ≤
      |c - c'| / (1 - γ) :=
  abs_optQValue_redirect_sub_optQValue_redirect_le _ hγ hR c c' q

/-- **The optimal values are Lipschitz in the absorbing reward**: with finitely many actions,
bounded rewards and `γ < 1`, the optimal values of the `p`-absorbing modifications of `M` with
rewards `c` and `c'` differ by at most `|c - c'| / (1 - γ)`. -/
theorem abs_optValue_saAbsorbing_sub_optValue_saAbsorbing_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c c' : ℝ) (s' : 𝓢) :
    |(M.saAbsorbing p c).optValue γ s' - (M.saAbsorbing p c').optValue γ s'| ≤
      |c - c'| / (1 - γ) :=
  abs_optValue_redirect_sub_optValue_redirect_le _ hγ hR c c' s'

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal action values of `M` and
of its `p`-absorbing modification with reward `c` differ by at most `|c - (Q* p - γ v* s)| /
(1 - γ)`, for `p = (s, a)`: the error of the modification is controlled by the error of its reward
at `p` alone. -/
theorem abs_optQValue_sub_optQValue_saAbsorbing_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (c : ℝ) (q : 𝓢 × 𝓐) :
    |M.optQValue γ q - (M.saAbsorbing p c).optQValue γ q| ≤
      |M.optQValue γ p - γ * M.optValue γ p.1 - c| / (1 - γ) := by
  have h := abs_optQValue_saAbsorbing_sub_optQValue_saAbsorbing_le (p := p) hγ hR
    (M.optQValue γ p - γ * M.optValue γ p.1) c q
  rwa [optQValue_saAbsorbing_optQValue hγ hR] at h

/-- **Separation survives the modification**: with finitely many actions, bounded rewards and
`γ < 1`, let `d` be a deterministic policy separated by `ω` in `M`:
`Q* (s', a') + ω ≤ Q* (s', d s')` for every state `s'` and every action `a' ≠ d s'`. If the reward
`c` of the `p`-absorbing modification is such that `4 |c - (Q* p - γ v* s)| ≤ (1 - γ) ω`, for
`p = (s, a)`, then `d` is separated by `ω / 2` in the modification. -/
theorem optQValue_saAbsorbing_add_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {ω : ℝ}
    {d : 𝓢 → 𝓐}
    (hd : ∀ s' a', a' ≠ d s' → M.optQValue γ (s', a') + ω ≤ M.optQValue γ (s', d s'))
    (hc : 4 * |M.optQValue γ p - γ * M.optValue γ p.1 - c| ≤ (1 - γ) * ω) {s' : 𝓢} {a' : 𝓐}
    (ha' : a' ≠ d s') :
    (M.saAbsorbing p c).optQValue γ (s', a') + ω / 2 ≤
      (M.saAbsorbing p c).optQValue γ (s', d s') := by
  have h1γ : 0 < 1 - (γ : ℝ) := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  -- the optimal action values move by at most `ω / 4`
  have hQ (q : 𝓢 × 𝓐) : |M.optQValue γ q - (M.saAbsorbing p c).optQValue γ q| ≤ ω / 4 := by
    refine (abs_optQValue_sub_optQValue_saAbsorbing_le hγ hR c q).trans ?_
    rw [div_le_div_iff₀ h1γ four_pos]
    linarith
  have h₁ := abs_le.1 (hQ (s', a'))
  have h₂ := abs_le.1 (hQ (s', d s'))
  linarith [hd s' a' ha']

omit [Finite 𝓐] in
/-- **Separated optimal policies survive the modification**: with finitely many actions, bounded
rewards and `γ < 1`, let `d` be a deterministic policy separated by `ω > 0` in `M`:
`Q* (s', a') + ω ≤ Q* (s', d s')` for every state `s'` and every action `a' ≠ d s'`. If the reward
`c` of the `p`-absorbing modification is such that `4 |c - (Q* p - γ v* s)| ≤ (1 - γ) ω`, for
`p = (s, a)`, then the greedy policy for the optimal value of the modification is `d`. -/
theorem greedy_optValue_saAbsorbing_eq [Fintype 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {ω : ℝ} (hω : 0 < ω) {d : 𝓢 → 𝓐}
    (hd : ∀ s' a', a' ≠ d s' → M.optQValue γ (s', a') + ω ≤ M.optQValue γ (s', d s'))
    (hc : 4 * |M.optQValue γ p - γ * M.optValue γ p.1 - c| ≤ (1 - γ) * ω) :
    (M.saAbsorbing p c).greedy γ ((M.saAbsorbing p c).optValue γ) = d :=
  greedy_optValue_eq_of_forall_optQValue_lt hγ (ae_abs_saAbsorbing_R_le hR) fun _ _ ha' ↦ by
    linarith [optQValue_saAbsorbing_add_le hγ hR hd hc ha']

omit [Finite 𝓐] in
/-- **The net of modifications** [LWCGC24, Lemma 4]: with finitely many actions, bounded rewards
and `γ < 1`, let `d` be a deterministic policy separated by `ω > 0` in `M`:
`Q* (s', a') + ω ≤ Q* (s', d s')` for every state `s'` and every action `a' ≠ d s'`. Let `B` bound
`|Q* p - γ v* s|` for `p = (s, a)` (by `Learning.MDP.abs_optQValue_sub_mul_optValue_le`,
`B = (1 + γ) C / (1 - γ)` does). Then the uniform grid `-B + 2 B k / K`, `k ≤ K`, of rewards on
`[-B, B]`, with `0 < K` and `8 B ≤ (1 - γ) ω K`, contains a reward whose `p`-absorbing
modification has greedy optimal policy `d`. The grid depends on `B`, `K` only, and not on `M`.
By `Learning.MDP.greedy_optValue_eq_of_forall_optQValue_lt`, `d` is also the greedy optimal policy
of `M`. -/
theorem exists_greedy_optValue_saAbsorbing_eq [Fintype 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {ω : ℝ} (hω : 0 < ω) {d : 𝓢 → 𝓐}
    (hd : ∀ s' a', a' ≠ d s' → M.optQValue γ (s', a') + ω ≤ M.optQValue γ (s', d s')) {B : ℝ}
    (hB : |M.optQValue γ p - γ * M.optValue γ p.1| ≤ B) {K : ℕ} (hK : 0 < K)
    (hKω : 8 * B ≤ (1 - γ) * ω * K) :
    ∃ k : Fin (K + 1), (M.saAbsorbing p (-B + 2 * B * (k : ℕ) / K)).greedy γ
      ((M.saAbsorbing p (-B + 2 * B * (k : ℕ) / K)).optValue γ) = d := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  obtain ⟨k, hk⟩ := exists_abs_sub_grid_le (x := M.optQValue γ p - γ * M.optValue γ p.1) (c := 0)
    (Δ := B) (by rwa [sub_zero]) hK
  refine ⟨k, greedy_optValue_saAbsorbing_eq hγ hR hω hd ?_⟩
  rw [zero_sub] at hk
  -- the grid spacing `2 B / K` is at most `(1 - γ) ω / 4`
  have h : 4 * (2 * B / K) ≤ (1 - γ) * ω := by
    rw [mul_div_assoc', div_le_iff₀ hK']
    linarith
  linarith

end Optimal

end Real

end Learning.MDP
