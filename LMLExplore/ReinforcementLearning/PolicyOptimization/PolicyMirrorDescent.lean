/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality
public import LMLExplore.MarkovDecisionProcess.PerformanceDifference
public import LMLExplore.OnlineLearning.MirrorDescent.Legendre
public import LMLExplore.ReinforcementLearning.PolicyOptimization.DirectPolicy

/-!
# Policy mirror descent

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a countable state space with finitely many actions and bounded
rewards, and let `0 ≤ γ < 1`. **Policy mirror descent** (PMD) with exact action values
[Xiao22, (37)], [JPR23, (4)] runs mirror descent in every state on the action values of the current
policy: with a mirror map `F : (𝓐 → ℝ) → ℝ`, step sizes `η k` and the directly parametrized
policies `π_k = directPolicy (p k)`, the probability vector of the next policy at `s` is

`p (k + 1) s ∈ argmin_{q ∈ Δ(𝓐)} -η k * ∑ a, Q^{π_k} (s, a) * q a + D_F(q, p k s)`,

where `D_F` is the Bregman divergence of `F`. For the negative entropy, `D_F` is the KL divergence
and PMD is natural policy gradient; for the squared Euclidean norm it is projected Q-ascent.
The iterates are described by the predicate `IsPolicyMirrorDescent`, whose steps are the mirror
descent steps `LMLExplore.OnlineLearning.IsMirrorDescentStep` for the losses `-Q^{π_k} (s, ·)`;
`exists_isPolicyMirrorDescent` builds them for a Legendre mirror map.

The analysis rests on the one-step inequality of mirror descent, in every state: for every
probability vector `u`,
`η k * ∑ a, Q^{π_k} (s, a) * (u a - p (k + 1) s a)
  ≤ D_F(u, p k s) - D_F(u, p (k + 1) s) - D_F(p (k + 1) s, p k s)`.
* For `u = p k s` it shows that `π_{k + 1}` is greedier than `π_k` for `Q^{π_k}`, so that the
  values increase [Xiao22, Lemma 7].
* For `u` supported on the maximizers of `Q^{π_k} (s, ·)`, with `D_F(u, p k s) ≤ η k * c k`, it
  shows that `π_{k + 1}` is `c k`-greedy for `v^{π_k}`. With the monotonicity of the values this
  gives `‖v* - v^{π_{k + 1}}‖ ≤ γ ‖v* - v^{π_k}‖ + c k`: PMD with step sizes adapted to the
  divergences to the greedy policies converges linearly at the rate `γ` of policy iteration
  [JPR23, Theorem 4.1].
* For `u` the action probabilities of a comparison policy `π`, together with the performance
  difference lemma along the state occupancy measure `d` of `π`, it gives the sublinear rate
  `∫ v^π dρ - ∫ v^{π_k} dρ ≤ (D₀ / (η (1 - γ)) + C / (1 - γ) ^ 2) / (k + 1)` on a finite state
  space, for a constant step `η` and rewards bounded by `C` with nonnegative means, where
  `D₀ = ∫ D_F(π s, p 0 s) dd(s)` [Xiao22, Theorem 8].

[Xiao22] and [JPR23] minimize costs; the statements here maximize rewards, which turns their
`argmin` of `η k * ⟨Q, q⟩ + D_F(q, p k s)` into the update above.

## Main definitions

* `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent M γ F F' η p`: the probability vectors
  `p k` are the iterates of policy mirror descent with mirror map `F`, derivative `F'` and step
  sizes `η`.

## Main statements

* `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.mul_sum_qValue_mul_sub_le`: the one-step
  inequality in every state [Xiao22, Lemma 6, (42)].
* `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.integral_advantage_nonneg`,
  `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.monotone_value`: the new policy has
  nonnegative mean advantage for the old one, and the values increase [Xiao22, Lemma 7].
* `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.optValue_sub_value_succ_le`: the
  one-step contraction `v* - v^{π_{k + 1}} ≤ γ ε + c k` for adapted step sizes.
* `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.optValue_sub_value_le`,
  `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.norm_optValue_sub_value_le`: the linear
  convergence `‖v* - v^{π_k}‖ ≤ γ ^ k ‖v* - v^{π_0}‖ + ∑ i < k, γ ^ (k - 1 - i) * c i`
  [JPR23, Theorem 4.1].
* `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.integral_value_sub_integral_value_le`,
  `LMLExplore.ReinforcementLearning.IsPolicyMirrorDescent.integral_optValue_sub_integral_value_le`:
  the sublinear convergence with a constant step on a finite state space [Xiao22, Theorem 8].
* `LMLExplore.ReinforcementLearning.exists_isPolicyMirrorDescent`: for a Legendre mirror map whose
  domain contains the simplex, policy mirror descent is well defined from every initial policy in
  the interior of the domain, with iterates in the interior.

## References

* [L. Xiao, *On the convergence rates of policy gradient methods*, JMLR 23 (2022),
  arXiv:2201.07443][Xiao22], (37), Lemmas 6–7, Theorem 8
* [E. Johnson, C. Pike-Burke and P. Rebeschini, *Optimal convergence rate for exact policy mirror
  descent in discounted Markov decision processes*, NeurIPS 2023, arXiv:2302.11381][JPR23],
  (4)–(6), Theorem 4.1
-/

public section

open MeasureTheory ProbabilityTheory Finset Learning Learning.MDP LMLExplore.OnlineLearning
open scoped NNReal

namespace LMLExplore.ReinforcementLearning

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Countable 𝓢]
  [MeasurableSingletonClass 𝓢] [Fintype 𝓐]

/-! ### The iterates -/

/-- The vectors `p k : 𝓢 → 𝓐 → ℝ` are the iterates of **policy mirror descent** [Xiao22, (37)],
[JPR23, (4)] with mirror map `F`, derivative `F'` of `F` and step sizes `η k`, for the MDP `M` and
the discount `γ`: the initial vectors are probability vectors, `F` has derivative `F' (p k s)`
within the simplex at every iterate, and in every state `s`, `p (k + 1) s` is a mirror descent step
on the simplex from `p k s` for the loss `q ↦ -∑ a, Q^{π_k} (s, a) * q a`, where
`π_k = directPolicy (p k)`. That is, `p (k + 1) s` minimizes over the simplex
`q ↦ -η k * ∑ a, Q^{π_k} (s, a) * q a + D_F(q, p k s)`. -/
structure IsPolicyMirrorDescent (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (F : (𝓐 → ℝ) → ℝ)
    (F' : (𝓐 → ℝ) → (𝓐 → ℝ) →L[ℝ] ℝ) (η : ℕ → ℝ) (p : ℕ → 𝓢 → 𝓐 → ℝ) : Prop where
  /-- The initial policy is given by probability vectors. -/
  mem_simplex_zero : ∀ s, p 0 s ∈ simplex 𝓐
  /-- The mirror map has derivative `F' (p k s)` within the simplex at every iterate. -/
  hasFDerivWithinAt : ∀ k s, HasFDerivWithinAt F (F' (p k s)) (simplex 𝓐) (p k s)
  /-- Every step is a mirror descent step on the simplex for the losses `-Q^{π_k} (s, ·)`. -/
  isMirrorDescentStep : ∀ k s, IsMirrorDescentStep (simplex 𝓐) F (η k)
    (-∑ a, M.qValue γ (directPolicy (p k)) (s, a) • (ContinuousLinearMap.proj a :
      (𝓐 → ℝ) →L[ℝ] ℝ)) (p k s) (F' (p k s)) (p (k + 1) s)

variable {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {F : (𝓐 → ℝ) → ℝ} {F' : (𝓐 → ℝ) → (𝓐 → ℝ) →L[ℝ] ℝ}
  {η : ℕ → ℝ} {p : ℕ → 𝓢 → 𝓐 → ℝ} {C : ℝ}

namespace IsPolicyMirrorDescent

section Iterates

variable (h : IsPolicyMirrorDescent M γ F F' η p)
include h

/-- The iterates of policy mirror descent are probability vectors. -/
lemma mem_simplex (k : ℕ) (s : 𝓢) : p k s ∈ simplex 𝓐 := by
  cases k with
  | zero => exact h.mem_simplex_zero s
  | succ k => exact (h.isMirrorDescentStep k s).mem

/-- The policies of policy mirror descent are Markov kernels. -/
lemma isMarkovKernel (k : ℕ) : IsMarkovKernel (directPolicy (p k)) :=
  isMarkovKernel_directPolicy (h.mem_simplex k)

/-- **The one-step inequality of policy mirror descent** [Xiao22, Lemma 6, (42)]: the three-point
descent lemma for the update in every state `s`. For every probability vector `u`,
`η k * ∑ a, Q^{π_k} (s, a) * (u a - p (k + 1) s a)
  ≤ D_F(u, p k s) - D_F(u, p (k + 1) s) - D_F(p (k + 1) s, p k s)`. -/
theorem mul_sum_qValue_mul_sub_le (k : ℕ) (s : 𝓢) {u : 𝓐 → ℝ} (hu : u ∈ simplex 𝓐) :
    η k * ∑ a, M.qValue γ (directPolicy (p k)) (s, a) * (u a - p (k + 1) s a) ≤
      bregDiv F u (p k s) (F' (p k s)) - bregDiv F u (p (k + 1) s) (F' (p (k + 1) s)) -
        bregDiv F (p (k + 1) s) (p k s) (F' (p k s)) := by
  have h_step := (h.isMirrorDescentStep k s).mul_apply_sub_le (convex_simplex 𝓐)
    (h.hasFDerivWithinAt (k + 1) s) hu
  refine le_of_eq_of_le ?_ h_step
  simp [mul_sub, sum_sub_distrib]

variable [MeasurableSingletonClass 𝓐]

/-- The mean of the action value of `π_k` under the policy `π_j`, in the state `s`, is the
weighted sum `∑ a, p j s a * Q^{π_k} (s, a)`. -/
private lemma integral_qValue_directPolicy (j k : ℕ) (s : 𝓢) :
    ∫ a, M.qValue γ (directPolicy (p k)) (s, a) ∂(directPolicy (p j) s) =
      ∑ a, p j s a * M.qValue γ (directPolicy (p k)) (s, a) := by
  simp only [integral_directPolicy (mem_simplex_iff.1 (h.mem_simplex j s)).1, smul_eq_mul]

/-- In every state, the value of `π_k` is the mean of its action value under `π_k`. -/
private lemma value_eq_sum (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (k : ℕ) (s : 𝓢) :
    M.value γ (directPolicy (p k)) s = ∑ a, p k s a * M.qValue γ (directPolicy (p k)) (s, a) := by
  have := h.isMarkovKernel k
  rw [← integral_qValue hγ hR s, h.integral_qValue_directPolicy]

variable (hF : ConvexOn ℝ (simplex 𝓐) F)
include hF

omit [MeasurableSingletonClass 𝓐] in
/-- The Bregman divergences of the mirror map at the iterates are nonnegative. -/
private lemma bregDiv_nonneg (k : ℕ) (s : 𝓢) {u : 𝓐 → ℝ} (hu : u ∈ simplex 𝓐) :
    0 ≤ bregDiv F u (p k s) (F' (p k s)) :=
  (h.hasFDerivWithinAt k s).hasSubgradientWithinAt hF (h.mem_simplex k s) u hu

/-- **Policy mirror descent is greedier than its current policy** [Xiao22, Lemma 7]: for positive
steps, in every state `s`, the mean of the action value of `π_k` under `π_{k + 1}` is at least
the value of `π_k`: `v^{π_k} s ≤ ∑ a, p (k + 1) s a * Q^{π_k} (s, a)`. -/
theorem value_le_sum_mul_qValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {k : ℕ}
    (hη : 0 < η k) (s : 𝓢) :
    M.value γ (directPolicy (p k)) s ≤
      ∑ a, p (k + 1) s a * M.qValue γ (directPolicy (p k)) (s, a) := by
  have h3 := h.mul_sum_qValue_mul_sub_le k s (h.mem_simplex k s)
  have h1 := h.bregDiv_nonneg hF (k + 1) s (h.mem_simplex k s)
  have h2 := h.bregDiv_nonneg hF k s (h.mem_simplex (k + 1) s)
  rw [bregDiv_self] at h3
  rw [h.value_eq_sum hγ hR]
  have h_neg : ∑ a, M.qValue γ (directPolicy (p k)) (s, a) * (p k s a - p (k + 1) s a) ≤ 0 :=
    nonpos_of_mul_nonpos_right (by linarith) hη
  simp only [mul_sub, sum_sub_distrib] at h_neg
  simp_rw [mul_comm (p _ s _)]
  linarith

/-- **Policy mirror descent improves the advantage** [Xiao22, Lemma 7]: for positive steps, in
every state `s`, the advantage of `π_k` has nonnegative mean under `π_{k + 1}`. -/
theorem integral_advantage_nonneg (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {k : ℕ}
    (hη : 0 < η k) (s : 𝓢) :
    0 ≤ ∫ a, M.advantage γ (directPolicy (p k)) (s, a) ∂(directPolicy (p (k + 1)) s) := by
  have := h.isMarkovKernel k
  have := h.isMarkovKernel (k + 1)
  rw [integral_advantage_eq_sum hγ hR _ s 0]
  simp only [measureReal_directPolicy_singleton (mem_simplex_iff.1 (h.mem_simplex (k + 1) s)).1,
    measureReal_directPolicy_singleton (mem_simplex_iff.1 (h.mem_simplex k s)).1, sub_zero,
    sub_mul, sum_sub_distrib, sub_nonneg]
  rw [← h.value_eq_sum hγ hR]
  exact h.value_le_sum_mul_qValue hF hγ hR hη s

/-- For positive steps, the value of `π_k` is at most the evaluation operator of `π_{k + 1}` at
this value: `v^{π_k} ≤ T^{π_{k + 1}} v^{π_k}`. -/
private lemma value_le_bellmanEval (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {k : ℕ}
    (hη : 0 < η k) :
    M.value γ (directPolicy (p k)) ≤
      M.bellmanEval γ (directPolicy (p (k + 1))) (M.value γ (directPolicy (p k))) := fun s ↦ by
  rw [bellmanEval_def, ← qValue_eq_lookahead, h.integral_qValue_directPolicy]
  exact h.value_le_sum_mul_qValue hF hγ hR hη s

variable [Nonempty 𝓢]

/-- **The values of policy mirror descent increase** [Xiao22, Lemma 7]: for positive steps,
`v^{π_k} ≤ v^{π_{k + 1}}` in every state. -/
theorem value_le_value_succ (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {k : ℕ}
    (hη : 0 < η k) (s : 𝓢) :
    M.value γ (directPolicy (p k)) s ≤ M.value γ (directPolicy (p (k + 1))) s := by
  have := h.isMarkovKernel k
  have := h.isMarkovKernel (k + 1)
  -- policy improvement: `v^{π_k} ≤ T^{π_{k + 1}} v^{π_k}` gives `v^{π_k} ≤ v^{π_{k + 1}}`
  exact le_value_of_le_bellmanEval hγ hR (measurable_value hγ hR) (abs_value_le hγ hR)
    (h.value_le_bellmanEval hF hγ hR hη) s

/-- **The values of policy mirror descent increase** [Xiao22, Lemma 7]: for positive steps, in
every state `s`, `k ↦ v^{π_k} s` is monotone. -/
theorem monotone_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hη : ∀ k, 0 < η k)
    (s : 𝓢) : Monotone fun k ↦ M.value γ (directPolicy (p k)) s :=
  monotone_nat_of_le_succ fun k ↦ h.value_le_value_succ hF hγ hR (hη k) s

/-! ### Linear convergence with adapted step sizes -/

/-- **One step of policy mirror descent with an adapted step size** [JPR23, proof of
Theorem 4.1]. Let `η k > 0`, and assume that in every state `s` some probability vector `u`,
supported on the maximizers of `Q^{π_k} (s, ·)`, has `D_F(u, p k s) ≤ η k * c`. If
`v* - v^{π_k} ≤ ε` in every state, then `v* - v^{π_{k + 1}} ≤ γ * ε + c` in every state. -/
theorem optValue_sub_value_succ_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {k : ℕ}
    (hη : 0 < η k) {c : ℝ}
    (hc : ∀ s, ∃ u ∈ simplex 𝓐, (∀ a, u a ≠ 0 → ∀ b, M.qValue γ (directPolicy (p k)) (s, b) ≤
      M.qValue γ (directPolicy (p k)) (s, a)) ∧ bregDiv F u (p k s) (F' (p k s)) ≤ η k * c)
    {ε : ℝ} (hε : ∀ s, M.optValue γ s - M.value γ (directPolicy (p k)) s ≤ ε) (s : 𝓢) :
    M.optValue γ s - M.value γ (directPolicy (p (k + 1))) s ≤ γ * ε + c := by
  have := h.isMarkovKernel k
  have := h.isMarkovKernel (k + 1)
  have := nonempty_of_mem_simplex (h.mem_simplex k s)
  obtain ⟨u, hu, hsupp, hD⟩ := hc s
  -- the policy `π_{k + 1}` is `c`-greedy for `v^{π_k}`, and its value is at least its evaluation
  -- operator at `v^{π_k}`
  set Q := M.qValue γ (directPolicy (p k))
  -- the step is `c`-greedy for `Q`: `∑ a, u a * Q (s, a) ≤ ∑ a, p (k + 1) s a * Q (s, a) + c`
  have h_greedy : ∑ a, u a * Q (s, a) ≤ ∑ a, p (k + 1) s a * Q (s, a) + c := by
    have h3 := h.mul_sum_qValue_mul_sub_le k s hu
    have h1 := h.bregDiv_nonneg hF (k + 1) s hu
    have h2 := h.bregDiv_nonneg hF k s (h.mem_simplex (k + 1) s)
    have h_le : η k * ∑ a, Q (s, a) * (u a - p (k + 1) s a) ≤ η k * c := by linarith
    have h_le' := le_of_mul_le_mul_left h_le hη
    simp only [mul_sub, sum_sub_distrib] at h_le'
    simp_rw [mul_comm (u _), mul_comm (p _ s _)]
    linarith
  -- policy improvement: `T^{π_{k + 1}} v^{π_k} ≤ v^{π_{k + 1}}`
  have h_succ : ∑ a, p (k + 1) s a * Q (s, a) ≤ M.value γ (directPolicy (p (k + 1))) s := by
    have h_imp := bellmanEval_le_value hγ hR (measurable_value hγ hR) (abs_value_le hγ hR)
      (h.value_le_bellmanEval hF hγ hR hη) s
    rwa [bellmanEval_def, ← qValue_eq_lookahead, h.integral_qValue_directPolicy] at h_imp
  -- `v* s = ⨆ a, Q* (s, a)` and `Q* ≤ Q + γ ε`
  have h_opt : M.optValue γ s ≤ ∑ a, u a * Q (s, a) + γ * ε := by
    rw [← iSup_optQValue hγ hR s]
    refine ciSup_le fun b ↦ ?_
    have := optQValue_sub_qValue_le_of_optValue_sub_value_le hγ hR hε (s, b)
    linarith [le_sum_mul_of_mem_simplex hu hsupp b]
  linarith

/-- **Linear convergence of policy mirror descent** [JPR23, Theorem 4.1], pointwise. Let the step
sizes be positive, and assume that in every state `s` and at every iteration `k`, some probability
vector `u`, supported on the maximizers of `Q^{π_k} (s, ·)`, has `D_F(u, p k s) ≤ η k * c k`. If
`v* - v^{π_0} ≤ B` in every state, then in every state
`v* - v^{π_k} ≤ γ ^ k * B + ∑ i < k, γ ^ (k - 1 - i) * c i`. For `γ > 0` this is
`γ ^ k * (B + ∑ i < k, γ ^ (-(i + 1)) * c i)`, the bound of [JPR23], which is that of policy
iteration up to the errors `c i`. -/
theorem optValue_sub_value_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hη : ∀ k, 0 < η k) {c : ℕ → ℝ}
    (hc : ∀ k s, ∃ u ∈ simplex 𝓐, (∀ a, u a ≠ 0 → ∀ b, M.qValue γ (directPolicy (p k)) (s, b) ≤
      M.qValue γ (directPolicy (p k)) (s, a)) ∧ bregDiv F u (p k s) (F' (p k s)) ≤ η k * c k)
    {B : ℝ} (hB : ∀ s, M.optValue γ s - M.value γ (directPolicy (p 0)) s ≤ B) (k : ℕ) (s : 𝓢) :
    M.optValue γ s - M.value γ (directPolicy (p k)) s ≤
      (γ : ℝ) ^ k * B + ∑ i ∈ range k, (γ : ℝ) ^ (k - 1 - i) * c i := by
  induction k generalizing s with
  | zero => simpa using hB s
  | succ k ih =>
    refine (h.optValue_sub_value_succ_le hF hγ hR (hη k) (hc k) ih s).trans_eq ?_
    rw [Finset.sum_range_succ, mul_add, Finset.mul_sum, ← mul_assoc, ← pow_succ', add_assoc]
    congr 2
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← mul_assoc, ← pow_succ']
      congr 2
      have := mem_range.1 hi
      omega
    · simp

/-- **Linear convergence of policy mirror descent** [JPR23, Theorem 4.1]. On a finite state space,
let the step sizes be positive, and assume that in every state `s` and at every iteration `k`,
some probability vector `u`, supported on the maximizers of `Q^{π_k} (s, ·)`, has
`D_F(u, p k s) ≤ η k * c k`. Then, in the sup norm,
`‖v* - v^{π_k}‖ ≤ γ ^ k * ‖v* - v^{π_0}‖ + ∑ i < k, γ ^ (k - 1 - i) * c i`. -/
theorem norm_optValue_sub_value_le [Fintype 𝓢] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hη : ∀ k, 0 < η k) {c : ℕ → ℝ}
    (hc : ∀ k s, ∃ u ∈ simplex 𝓐, (∀ a, u a ≠ 0 → ∀ b, M.qValue γ (directPolicy (p k)) (s, b) ≤
      M.qValue γ (directPolicy (p k)) (s, a)) ∧ bregDiv F u (p k s) (F' (p k s)) ≤ η k * c k)
    (k : ℕ) :
    ‖M.optValue γ - M.value γ (directPolicy (p k))‖ ≤
      (γ : ℝ) ^ k * ‖M.optValue γ - M.value γ (directPolicy (p 0))‖ +
        ∑ i ∈ range k, (γ : ℝ) ^ (k - 1 - i) * c i := by
  have h_nonneg (j : ℕ) (s : 𝓢) : 0 ≤ M.optValue γ s - M.value γ (directPolicy (p j)) s := by
    have := h.isMarkovKernel j
    exact sub_nonneg.2 (value_le_optValue hγ hR s)
  have h_le := h.optValue_sub_value_le hF hγ hR hη hc (B := ‖M.optValue γ -
    M.value γ (directPolicy (p 0))‖) (fun s ↦ by
      simpa [Real.norm_of_nonneg (h_nonneg 0 s)] using
        norm_le_pi_norm (M.optValue γ - M.value γ (directPolicy (p 0))) s) k
  obtain ⟨s₀⟩ := ‹Nonempty 𝓢›
  refine (pi_norm_le_iff_of_nonneg ((h_nonneg k s₀).trans (h_le s₀))).2 fun s ↦ ?_
  simpa [Real.norm_of_nonneg (h_nonneg k s)] using h_le s

end Iterates

/-! ### Sublinear convergence with a constant step size -/

section Sublinear

variable [MeasurableSingletonClass 𝓐] [Nonempty 𝓢] [Finite 𝓢] {η₀ : ℝ}

/-- **The one-step bound of policy mirror descent with a constant step** [Xiao22, proof of
Theorem 8]. Let `π` be a stationary policy, `d` its state occupancy measure from the probability
measure `ρ` and `D j s = D_F(π s, p j s)` the Bregman divergence from the iterates to the action
probabilities of `π`. Then
`(1 - γ) (∫ v^π dρ - ∫ v^{π_j} dρ) ≤ (∫ D j dd - ∫ D (j + 1) dd) / η₀
  + (∫ v^{π_{j + 1}} dd - ∫ v^{π_j} dd)`. -/
private lemma mul_integral_value_sub_le (h : IsPolicyMirrorDescent M γ F F' (fun _ ↦ η₀) p)
    (hF : ConvexOn ℝ (simplex 𝓐) F) (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hη : 0 < η₀) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (ρ : Measure 𝓢) [IsProbabilityMeasure ρ]
    (j : ℕ) :
    (1 - γ) * (∫ s, M.value γ π s ∂ρ - ∫ s, M.value γ (directPolicy (p j)) s ∂ρ) ≤
      (∫ s, bregDiv F (fun a ↦ (π s).real {a}) (p j s) (F' (p j s))
          ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst -
        ∫ s, bregDiv F (fun a ↦ (π s).real {a}) (p (j + 1) s) (F' (p (j + 1) s))
          ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst) / η₀ +
      (∫ s, M.value γ (directPolicy (p (j + 1))) s
          ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst -
        ∫ s, M.value γ (directPolicy (p j)) s
          ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst) := by
  have h1γ := one_sub_coe_pos hγ
  have := h.isMarkovKernel j
  have := h.isMarkovKernel (j + 1)
  have := isProbabilityMeasure_occupancy (M := M) (alg := Algorithm.markov fun _ ↦ π) (μ := ρ) hγ
  set d := (M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst
  set A := M.advantage γ (directPolicy (p j))
  have hu (s : 𝓢) := mem_simplex_measureReal_singleton (π s)
  -- in every state, the advantage of `π_j` under `π` is at most the decrease of the divergence
  -- plus the advantage of `π_j` under `π_{j + 1}`
  have h_state (s : 𝓢) : ∫ a, A (s, a) ∂(π s) ≤
      (bregDiv F (fun a ↦ (π s).real {a}) (p j s) (F' (p j s)) -
        bregDiv F (fun a ↦ (π s).real {a}) (p (j + 1) s) (F' (p (j + 1) s))) / η₀ +
      ∫ a, A (s, a) ∂(directPolicy (p (j + 1)) s) := by
    have h3 := h.mul_sum_qValue_mul_sub_le j s (hu s)
    have h0 := h.bregDiv_nonneg hF j s (h.mem_simplex (j + 1) s)
    have h_le : ∑ a, M.qValue γ (directPolicy (p j)) (s, a) *
        ((π s).real {a} - p (j + 1) s a) ≤
          (bregDiv F (fun a ↦ (π s).real {a}) (p j s) (F' (p j s)) -
            bregDiv F (fun a ↦ (π s).real {a}) (p (j + 1) s) (F' (p (j + 1) s))) / η₀ := by
      rw [le_div_iff₀ hη, mul_comm]
      linarith
    rw [integral_advantage_eq_sum hγ hR _ s 0, integral_advantage_eq_sum hγ hR _ s 0]
    simp only [mul_sub, sum_sub_distrib] at h_le
    simp only [measureReal_directPolicy_singleton (mem_simplex_iff.1 (h.mem_simplex (j + 1) s)).1,
      measureReal_directPolicy_singleton (mem_simplex_iff.1 (h.mem_simplex j s)).1, sub_zero,
      sub_mul, sum_sub_distrib]
    simp_rw [mul_comm (M.qValue γ (directPolicy (p j)) _)] at h_le
    linarith
  -- integrate against the state occupancy measure of `π`
  have h_int := integral_mono (μ := d) Integrable.of_finite Integrable.of_finite h_state
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_div,
    integral_sub Integrable.of_finite Integrable.of_finite] at h_int
  have h_imp := integral_integral_advantage_le_integral_value_sub (μ := d)
    (π := directPolicy (p j)) (π' := directPolicy (p (j + 1))) hγ hR
    (h.integral_advantage_nonneg hF hγ hR hη)
  rw [integral_value_sub_integral_value hγ hR (directPolicy (p j)) π, ← mul_assoc,
    mul_inv_cancel₀ h1γ.ne', one_mul]
  linarith

/-- **Sublinear convergence of policy mirror descent** [Xiao22, Theorem 8], against any stationary
policy. On a finite state space, with rewards bounded by `C` with nonnegative means and a
constant step `η₀ > 0`, let `π` be a stationary policy and `d` its state occupancy measure from the
probability measure `ρ`. Then, with `D₀ = ∫ D_F(π s, p 0 s) dd(s)` the mean divergence from the
initial policy to the action probabilities of `π`,
`∫ v^π dρ - ∫ v^{π_k} dρ ≤ (D₀ / (η₀ (1 - γ)) + C / (1 - γ) ^ 2) / (k + 1)`. -/
theorem integral_value_sub_integral_value_le
    (h : IsPolicyMirrorDescent M γ F F' (fun _ ↦ η₀) p) (hF : ConvexOn ℝ (simplex 𝓐) F)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hr : ∀ p, 0 ≤ meanReward M.R p)
    (hη : 0 < η₀) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (ρ : Measure 𝓢) [IsProbabilityMeasure ρ]
    (k : ℕ) :
    ∫ s, M.value γ π s ∂ρ - ∫ s, M.value γ (directPolicy (p k)) s ∂ρ ≤
      ((∫ s, bregDiv F (fun a ↦ (π s).real {a}) (p 0 s) (F' (p 0 s))
          ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst) / (η₀ * (1 - γ)) +
        C / (1 - γ) ^ 2) / (k + 1) := by
  have h1γ := one_sub_coe_pos hγ
  have := isProbabilityMeasure_occupancy (M := M) (alg := Algorithm.markov fun _ ↦ π) (μ := ρ) hγ
  set d := (M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst
  set D : ℕ → ℝ := fun j ↦ ∫ s, bregDiv F (fun a ↦ (π s).real {a}) (p j s) (F' (p j s)) ∂d
  set w : ℕ → ℝ := fun j ↦ ∫ s, M.value γ (directPolicy (p j)) s ∂d
  set e : ℕ → ℝ := fun j ↦ ∫ s, M.value γ π s ∂ρ - ∫ s, M.value γ (directPolicy (p j)) s ∂ρ
  -- the one-step bounds telescope
  have h_sum : (1 - γ) * ∑ j ∈ range (k + 1), e j ≤ (D 0 - D (k + 1)) / η₀ + (w (k + 1) - w 0) := by
    rw [mul_sum, ← sum_range_sub' D, sum_div, ← sum_range_sub w, ← sum_add_distrib]
    exact sum_le_sum fun j _ ↦ mul_integral_value_sub_le h hF hγ hR hη π ρ j
  have hD : 0 ≤ D (k + 1) := integral_nonneg fun s ↦ h.bregDiv_nonneg hF (k + 1) s
    (mem_simplex_measureReal_singleton (π s))
  have hw : w (k + 1) - w 0 ≤ C / (1 - γ) := by
    have := h.isMarkovKernel (k + 1)
    have := h.isMarkovKernel 0
    have h_up : w (k + 1) ≤ C / (1 - γ) := by
      refine (integral_mono Integrable.of_finite (integrable_const _)
        fun s ↦ (le_abs_self _).trans (abs_value_le hγ hR s)).trans_eq ?_
      simp
    have h_low : 0 ≤ w 0 := integral_nonneg fun s ↦ value_nonneg hγ hR hr s
    linarith
  -- the values increase, so the last iterate is the worst of the first `k + 1`
  have h_mono : (k + 1 : ℝ) * e k ≤ ∑ j ∈ range (k + 1), e j := by
    have h_card : (k + 1 : ℝ) * e k = ∑ _j ∈ range (k + 1), e k := by simp
    rw [h_card]
    refine sum_le_sum fun j hj ↦ sub_le_sub_left (integral_mono ?_ ?_ fun s ↦
      h.monotone_value hF hγ hR (fun _ ↦ hη) s (Nat.lt_succ_iff.1 (mem_range.1 hj))) _
    · have := h.isMarkovKernel j
      exact integrable_of_abs_le (measurable_value hγ hR) (abs_value_le hγ hR) ρ
    · have := h.isMarkovKernel k
      exact integrable_of_abs_le (measurable_value hγ hR) (abs_value_le hγ hR) ρ
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hD0 : D 0 / (η₀ * (1 - γ)) + C / (1 - γ) ^ 2 = (D 0 / η₀ + C / (1 - γ)) / (1 - γ) := by
    field_simp
  rw [hD0, le_div_iff₀ hk, le_div_iff₀ h1γ]
  have := div_le_div_of_nonneg_right (sub_le_self (D 0) hD) hη.le
  have := mul_le_mul_of_nonneg_left h_mono h1γ.le
  linarith

/-- **Sublinear convergence of policy mirror descent** [Xiao22, Theorem 8]. On a finite state
space, with rewards in `[0, 1]` and a constant step `η₀ > 0`, let `π*` be an optimal stationary
policy and `d*` its state occupancy measure from the probability measure `ρ`. Then, with
`D₀ = ∫ D_F(π* s, p 0 s) dd*(s)`,
`∫ v* dρ - ∫ v^{π_k} dρ ≤ (D₀ / (η₀ (1 - γ)) + 1 / (1 - γ) ^ 2) / (k + 1)`. -/
theorem integral_optValue_sub_integral_value_le
    (h : IsPolicyMirrorDescent M γ F F' (fun _ ↦ η₀) p) (hF : ConvexOn ℝ (simplex 𝓐) F)
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 1) (hη : 0 < η₀) (π : Kernel 𝓢 𝓐)
    [IsMarkovKernel π] (hπ : M.value γ π = M.optValue γ) (ρ : Measure 𝓢) [IsProbabilityMeasure ρ]
    (k : ℕ) :
    ∫ s, M.optValue γ s ∂ρ - ∫ s, M.value γ (directPolicy (p k)) s ∂ρ ≤
      ((∫ s, bregDiv F (fun a ↦ (π s).real {a}) (p 0 s) (F' (p 0 s))
          ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) ρ).fst) / (η₀ * (1 - γ)) +
        1 / (1 - γ) ^ 2) / (k + 1) := by
  have hR' : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ 1 :=
    fun p ↦ (hR p).mono fun x hx ↦ abs_le.2 ⟨by linarith [hx.1], hx.2⟩
  have hr (p : 𝓢 × 𝓐) : 0 ≤ meanReward M.R p := by
    rw [meanReward_def]
    exact integral_nonneg_of_ae ((hR p).mono fun _ hx ↦ hx.1)
  rw [← hπ]
  exact h.integral_value_sub_integral_value_le hF hγ hR' hr hη π ρ k

end Sublinear

end IsPolicyMirrorDescent

/-! ### Existence for Legendre mirror maps -/

/-- **Policy mirror descent is well defined for Legendre mirror maps.** Let `F` be a Legendre
function whose domain `D` contains the simplex, such as the negative entropy
`x ↦ ∑ a, x a * log (x a)` on the nonnegative orthant, and let the initial
probability vectors `p₀ s` lie in the interior of `D`. Then for all step sizes there are iterates
of policy mirror descent from `p₀` with the derivative `fderiv ℝ F`, and they all lie in the
interior of `D`, where `F` is differentiable. -/
theorem exists_isPolicyMirrorDescent {D : Set (𝓐 → ℝ)} (hF : IsLegendre F D)
    (hD : simplex 𝓐 ⊆ D) (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (η : ℕ → ℝ) {p₀ : 𝓢 → 𝓐 → ℝ}
    (hp₀ : ∀ s, p₀ s ∈ simplex 𝓐 ∩ interior D) :
    ∃ p, p 0 = p₀ ∧ IsPolicyMirrorDescent M γ F (fderiv ℝ F) η p ∧ ∀ k s, p k s ∈ interior D := by
  -- one step from every family of vectors, in every state
  have h_step (q : 𝓢 → 𝓐 → ℝ) (k : ℕ) (s : 𝓢) : ∃ x,
      IsMirrorDescentStep (simplex 𝓐) F (η k)
        (-∑ a, M.qValue γ (directPolicy q) (s, a) • (ContinuousLinearMap.proj a :
          (𝓐 → ℝ) →L[ℝ] ℝ)) (q s) (fderiv ℝ F (q s)) x ∧ x ∈ interior D :=
    hF.exists_isMirrorDescentStep_mem_interior (isClosed_simplex 𝓐) (convex_simplex 𝓐)
      (isCompact_simplex 𝓐).isBounded hD ⟨_, hp₀ s⟩ _ _ _ _
  choose f hf using h_step
  obtain ⟨p, hp0, hp_succ⟩ : ∃ p : ℕ → 𝓢 → 𝓐 → ℝ, p 0 = p₀ ∧ ∀ k, p (k + 1) = f (p k) k :=
    ⟨fun k ↦ Nat.rec p₀ (fun k q ↦ f q k) k, rfl, fun _ ↦ rfl⟩
  have h_int (k : ℕ) (s : 𝓢) : p k s ∈ interior D := by
    cases k with
    | zero => exact hp0 ▸ (hp₀ s).2
    | succ k => exact hp_succ k ▸ (hf (p k) k s).2
  refine ⟨p, hp0, ⟨fun s ↦ hp0 ▸ (hp₀ s).1,
    fun k s ↦ (hF.hasFDerivAt (h_int k s)).hasFDerivWithinAt, fun k s ↦ ?_⟩, h_int⟩
  rw [hp_succ k]
  exact (hf (p k) k s).1

end LMLExplore.ReinforcementLearning
