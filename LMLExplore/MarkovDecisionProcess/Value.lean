/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Bellman
public import LMLExplore.MarkovDecisionProcess.MarkovPolicy
public import LMLExplore.Probability.Kernel.Resolvent

/-!
# Values of stationary policies in a discounted Markov decision process

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with mean reward `r = meanReward M.R` and transition kernel `P`, let
`π : Kernel 𝓢 𝓐` be a stationary policy and `0 ≤ γ < 1` a discount factor. The reward of `π` is
`r_π s = ∫ a, r (s, a) ∂(π s)`, and the states of a run of `π` form a Markov chain with transition
kernel `P_π = M.stateKernel π`. The value of `π` is the expected discounted sum of the rewards of
that chain,
`v^π s = ∑ n, γ ^ n * ∫ r_π ∂(P_π ^ n s)`,
its action value is `Q^π (s, a) = r (s, a) + γ * ∫ v^π ∂(P (s, a))`, the value of playing `a` first
and following `π` afterwards, and its advantage is `A^π (s, a) = Q^π (s, a) - v^π s`.

With rewards bounded by `C`, the series defining `v^π` converges, `v^π` is measurable and bounded by
`C / (1 - γ)`, and it satisfies the evaluation equations
`v^π = r_π + γ P_π v^π` and `v^π s = ∫ a, Q^π (s, a) ∂(π s)`. In terms of the evaluation operator
`M.bellmanEval γ π`, the value is its unique bounded measurable fixed point.

These are the objects in which the optimality theory of discounted MDPs is stated: an optimal
policy is one whose value dominates the value of every other policy, and the optimality equation
characterizes the largest such value.

## Main definitions

* `Learning.MDP.policyReward M π`: the mean reward `r_π` of the stationary policy `π`.
* `Learning.MDP.value M γ π`: the discounted value `v^π` of the stationary policy `π`.
* `Learning.MDP.qValue M γ π`: the action value `Q^π = r + γ P v^π`.
* `Learning.MDP.advantage M γ π`: the advantage `A^π (s, a) = Q^π (s, a) - v^π s`.

## Main statements

* `Learning.MDP.hasSum_value`: the series `∑ n, γ ^ n * ∫ r_π ∂(P_π ^ n s)` converges to `v^π s`.
* `Learning.MDP.value_eq_integral_resolvent`: `v^π = R_γ(P_π) r_π`, the resolvent
  `∑ n, γ ^ n P_π ^ n` of the state kernel applied to the reward.
* `Learning.MDP.abs_value_le`, `Learning.MDP.measurable_value`: `v^π` is measurable and
  `|v^π| ≤ C / (1 - γ)`; the same holds for `Q^π` (`Learning.MDP.abs_qValue_le`,
  `Learning.MDP.measurable_qValue`).
* `Learning.MDP.value_eq_policyReward_add`: the evaluation equation `v^π = r_π + γ P_π v^π`.
* `Learning.MDP.integral_qValue`: `v^π s = ∫ a, Q^π (s, a) ∂(π s)`, and
  `Learning.MDP.integral_advantage`: the advantage has mean zero under `π`.
* `Learning.MDP.bellmanEval_value`, `Learning.MDP.eq_value_of_bellmanEval_eq`: `v^π` is the
  unique bounded measurable fixed point of the evaluation operator of `π` [P, Theorem 6.1.1].
* `Learning.MDP.value_le_bellman`: the value of a measurable deterministic stationary policy is a
  subsolution of the optimality equation, `v^d ≤ T v^d`.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.1
* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], §1.1
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (π : Kernel 𝓢 𝓐) {v : 𝓢 → ℝ} {B C : ℝ}

/-! ### The reward of a stationary policy -/

/-- The mean reward `r_π s = ∫ a, r (s, a) ∂(π s)` of the stationary policy `π` in state `s`. -/
noncomputable def policyReward (s : 𝓢) : ℝ :=
  ∫ a, meanReward M.R (s, a) ∂(π s)

lemma policyReward_def (s : 𝓢) : M.policyReward π s = ∫ a, meanReward M.R (s, a) ∂(π s) :=
  (rfl)

variable {M γ π}

lemma measurable_policyReward [IsSFiniteKernel π] : Measurable (M.policyReward π) :=
  ((measurable_meanReward M.R).stronglyMeasurable.integral_kernel_prod_right' (κ := π)).measurable

/-- With rewards bounded by `C`, the reward of a stationary policy is bounded by `C`. -/
lemma abs_policyReward_le [IsMarkovKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    |M.policyReward π s| ≤ C :=
  abs_integral_le_of_abs_le fun a ↦ abs_meanReward_le hR (s, a)

/-- The reward of a deterministic stationary policy `d` is the mean reward of the action `d s`. -/
@[simp]
lemma policyReward_deterministic {d : 𝓢 → 𝓐} (hd : Measurable d) (s : 𝓢) :
    M.policyReward (Kernel.deterministic d hd) s = meanReward M.R (s, d s) := by
  rw [policyReward_def]
  exact Kernel.integral_deterministic' hd
    ((measurable_meanReward M.R).comp measurable_prodMk_left).stronglyMeasurable

/-- With bounded rewards, the evaluation operator of `π` at a bounded measurable `v` is
`r_π + γ P_π v`. -/
theorem bellmanEval_eq_policyReward_add [IsMarkovKernel π] (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (s : 𝓢) :
    M.bellmanEval γ π v s = M.policyReward π s + γ * ∫ s', v s' ∂(M.stateKernel π s) := by
  have hr : Integrable (fun a ↦ meanReward M.R (s, a)) (π s) :=
    integrable_of_abs_le (f := fun a ↦ meanReward M.R (s, a))
      ((measurable_meanReward M.R).comp measurable_prodMk_left)
      (fun a ↦ abs_meanReward_le hR (s, a)) _
  have hPv : Integrable (fun a ↦ ∫ s', v s' ∂(M.P (s, a))) (π s) :=
    integrable_of_abs_le ((hv.stronglyMeasurable.integral_kernel (κ := M.P)).measurable.comp
      measurable_prodMk_left) (fun _ ↦ abs_integral_le_of_abs_le hvB) _
  rw [bellmanEval_def, policyReward_def, integral_stateKernel (integrable_of_abs_le hv hvB _)]
  simp_rw [lookahead_def]
  rw [integral_add hr (hPv.const_mul _), integral_const_mul]

/-! ### The value of a stationary policy -/

variable (M γ π) in
/-- The discounted value `v^π s = ∑ n, γ ^ n * ∫ r_π ∂(P_π ^ n s)` of the stationary policy `π`:
the expected discounted sum of the rewards `r_π` along the Markov chain of states with kernel
`P_π = M.stateKernel π` started at `s`. The series converges when the rewards are bounded and
`γ < 1` (`Learning.MDP.hasSum_value`). -/
noncomputable def value (s : 𝓢) : ℝ :=
  ∑' n, (γ : ℝ) ^ n * ∫ s', M.policyReward π s' ∂((M.stateKernel π ^ n) s)

variable (M γ π) in
lemma value_def (s : 𝓢) :
    M.value γ π s = ∑' n, (γ : ℝ) ^ n * ∫ s', M.policyReward π s' ∂((M.stateKernel π ^ n) s) :=
  (rfl)

section Value

variable [IsMarkovKernel π]

private lemma abs_integral_policyReward_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (n : ℕ) (s : 𝓢) :
    |∫ s', M.policyReward π s' ∂((M.stateKernel π ^ n) s)| ≤ C :=
  abs_integral_le_of_abs_le (abs_policyReward_le hR)

/-- The terms of the series defining the value are bounded by `γ ^ n * C`. -/
private lemma norm_mul_integral_policyReward_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (n : ℕ)
    (s : 𝓢) :
    ‖(γ : ℝ) ^ n * ∫ s', M.policyReward π s' ∂((M.stateKernel π ^ n) s)‖ ≤ (γ : ℝ) ^ n * C := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow, NNReal.abs_eq]
  gcongr
  exact abs_integral_policyReward_le hR n s

/-- With rewards bounded by `C` and `γ < 1`, the series defining the value of `π` converges. -/
theorem hasSum_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    HasSum (fun n ↦ (γ : ℝ) ^ n * ∫ s', M.policyReward π s' ∂((M.stateKernel π ^ n) s))
      (M.value γ π s) :=
  (Summable.of_norm_bounded ((summable_geometric_of_lt_one γ.coe_nonneg hγ).mul_right C)
    (norm_mul_integral_policyReward_le hR · s)).hasSum

/-- With bounded rewards and `γ < 1`, the value of a stationary policy is the resolvent of its
state kernel applied to its reward: `v^π = R_γ(P_π) r_π`, where `R_γ(P_π) = ∑ n, γ ^ n P_π ^ n`. -/
theorem value_eq_integral_resolvent (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    M.value γ π s = ∫ s', M.policyReward π s' ∂(Kernel.resolvent γ (M.stateKernel π) s) := by
  have := Kernel.isFiniteKernel_resolvent (κ := M.stateKernel π) hγ
  rw [Kernel.integral_resolvent
    (integrable_of_abs_le measurable_policyReward (abs_policyReward_le hR) _), value_def]
  simp_rw [smul_eq_mul]

/-- With rewards bounded by `C` and `γ < 1`, the value of a stationary policy is bounded by
`C / (1 - γ)`. -/
theorem abs_value_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    |M.value γ π s| ≤ C / (1 - γ) := by
  rw [value_eq_integral_resolvent hγ hR]
  exact Kernel.abs_integral_resolvent_le hγ (abs_policyReward_le hR) s

/-- With bounded rewards and `γ < 1`, the value of a stationary policy is measurable. -/
theorem measurable_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Measurable (M.value γ π) := by
  rw [funext (value_eq_integral_resolvent hγ hR)]
  exact Kernel.measurable_integral_resolvent measurable_policyReward

/-- **Evaluation equation**: with bounded rewards and `γ < 1`, the value of a stationary policy
satisfies `v^π = r_π + γ P_π v^π`. -/
theorem value_eq_policyReward_add (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    M.value γ π s = M.policyReward π s + γ * ∫ s', M.value γ π s' ∂(M.stateKernel π s) := by
  simp_rw [value_eq_integral_resolvent hγ hR]
  exact Kernel.integral_resolvent_eq_add hγ measurable_policyReward (abs_policyReward_le hR) s

/-- With bounded rewards and `γ < 1`, the value of a stationary policy is a fixed point of its
evaluation operator. -/
theorem bellmanEval_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.bellmanEval γ π (M.value γ π) = M.value γ π := by
  ext s
  rw [bellmanEval_eq_policyReward_add hR (measurable_value hγ hR) (abs_value_le hγ hR),
    ← value_eq_policyReward_add hγ hR]

/-- **Policy evaluation** [P, Theorem 6.1.1]: with bounded rewards and `γ < 1`, the value of a
stationary policy is the unique bounded measurable fixed point of its evaluation operator. -/
theorem eq_value_of_bellmanEval_eq (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (h : M.bellmanEval γ π v = v) :
    v = M.value γ π := by
  rw [funext (value_eq_integral_resolvent hγ hR)]
  refine Kernel.eq_integral_resolvent_of_eq_add hγ measurable_policyReward
    (abs_policyReward_le hR) hv hvB fun s ↦ ?_
  rw [← bellmanEval_eq_policyReward_add hR hv hvB, h]

/-- With finitely many actions, bounded rewards and `γ < 1`, the value of a measurable
deterministic stationary policy `d` is below its image by the optimality operator:
`v^d ≤ T v^d`. -/
theorem value_le_bellman [Finite 𝓐] (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {d : 𝓢 → 𝓐} (hd : Measurable d) :
    M.value γ (Kernel.deterministic d hd) ≤
      M.bellman γ (M.value γ (Kernel.deterministic d hd)) := fun s ↦ by
  conv_lhs => rw [← bellmanEval_value hγ hR]
  rw [bellmanEval_deterministic (measurable_value hγ hR)]
  exact lookahead_le_bellman _ s _

end Value

/-! ### Action values and advantages -/

variable (M γ π) in
/-- The action value `Q^π (s, a) = r (s, a) + γ * ∫ v^π ∂(P (s, a))` of the stationary policy `π`:
the expected discounted return of playing `a` in state `s` and following `π` afterwards. -/
noncomputable def qValue (p : 𝓢 × 𝓐) : ℝ :=
  meanReward M.R p + γ * ∫ s', M.value γ π s' ∂(M.P p)

variable (M γ π) in
lemma qValue_def (p : 𝓢 × 𝓐) :
    M.qValue γ π p = meanReward M.R p + γ * ∫ s', M.value γ π s' ∂(M.P p) :=
  (rfl)

variable (M γ π) in
/-- The action value of `π` is the one-step lookahead of its value. -/
lemma qValue_eq_lookahead : M.qValue γ π = M.lookahead γ (M.value γ π) := by
  ext p
  rw [qValue_def, lookahead_def]

variable (M γ π) in
/-- The advantage `A^π (s, a) = Q^π (s, a) - v^π s` of playing `a` in state `s` over following
the stationary policy `π`. -/
noncomputable def advantage (p : 𝓢 × 𝓐) : ℝ :=
  M.qValue γ π p - M.value γ π p.1

variable (M γ π) in
lemma advantage_def (p : 𝓢 × 𝓐) : M.advantage γ π p = M.qValue γ π p - M.value γ π p.1 :=
  (rfl)

section QValue

variable [IsMarkovKernel π]

/-- With bounded rewards and `γ < 1`, the action value of a stationary policy is measurable. -/
theorem measurable_qValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Measurable (M.qValue γ π) := by
  rw [qValue_eq_lookahead]
  exact measurable_lookahead (measurable_value hγ hR)

/-- With rewards bounded by `C` and `γ < 1`, the action value of a stationary policy is bounded
by `C / (1 - γ)`. -/
theorem abs_qValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    |M.qValue γ π p| ≤ C / (1 - γ) := by
  have hγ' : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  rw [qValue_eq_lookahead]
  refine (abs_lookahead_le hR (abs_value_le hγ hR) p).trans_eq ?_
  field_simp
  ring

/-- **Evaluation equation**: with bounded rewards and `γ < 1`, the value of a stationary policy
is the mean under the policy of its action value: `v^π s = ∫ a, Q^π (s, a) ∂(π s)`. -/
theorem integral_qValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    ∫ a, M.qValue γ π (s, a) ∂(π s) = M.value γ π s := by
  rw [qValue_eq_lookahead, ← bellmanEval_def, bellmanEval_value hγ hR]

/-- With bounded rewards and `γ < 1`, the advantage of a stationary policy is measurable. -/
theorem measurable_advantage (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Measurable (M.advantage γ π) :=
  (measurable_qValue hγ hR).sub ((measurable_value hγ hR).comp measurable_fst)

/-- With rewards bounded by `C` and `γ < 1`, the advantage of a stationary policy is bounded by
`2 * C / (1 - γ)`. -/
theorem abs_advantage_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    |M.advantage γ π p| ≤ 2 * C / (1 - γ) := by
  rw [advantage_def, two_mul, add_div]
  exact (abs_sub _ _).trans (add_le_add (abs_qValue_le hγ hR p) (abs_value_le hγ hR p.1))

/-- With bounded rewards and `γ < 1`, the advantage of a stationary policy has mean zero under
the policy. -/
theorem integral_advantage (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    ∫ a, M.advantage γ π (s, a) ∂(π s) = 0 := by
  have hQ : Integrable (fun a ↦ M.qValue γ π (s, a)) (π s) :=
    integrable_of_abs_le ((measurable_qValue hγ hR).comp measurable_prodMk_left)
      (fun a ↦ abs_qValue_le hγ hR (s, a)) _
  simp_rw [advantage_def]
  rw [integral_sub hQ (integrable_const _), integral_qValue hγ hR, integral_const, probReal_univ,
    one_smul, sub_self]

end QValue

end Learning.MDP
