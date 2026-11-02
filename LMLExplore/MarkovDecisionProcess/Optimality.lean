/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Comparison
public import LMLExplore.MarkovDecisionProcess.ValueIteration

/-!
# The optimality equation of a discounted MDP

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢` with finitely many actions and
bounded rewards, and let `0 ≤ γ < 1`. Write `T` for the Bellman optimality operator
`M.bellman γ`, `v*` for the optimal value `M.optValue γ` (the supremum of the discounted values of
all history-dependent policies) and `Q* = r + γ P v*` for the optimal action value
`M.optQValue γ`.

The optimality equation `T v = v` has a unique bounded measurable solution, by Banach's fixed
point theorem on the bounded measurable functions (`Learning.MDP.exists_bellman_eq`), and every
bounded measurable solution is `v*`, by comparison with sub- and supersolutions
(`Learning.MDP.eq_optValue_of_bellman_eq`). This file draws the consequences for `v*` and for
the policies of `M`:
* `v*` is measurable and solves the optimality equation, so it is the unique bounded measurable
  fixed point of `T`;
* the deterministic stationary policy greedy for `v*` has value `v*`; its runs from every initial
  law `μ` have discounted value `∫ v* dμ`, the largest value of all algorithms from `μ`;
* `v*` is the largest value of a measurable deterministic stationary policy, attained by the
  greedy policy;
* a stationary policy is optimal if and only if its value solves the optimality equation;
* `v* s = ⨆ a, Q* (s, a)`, and `Q*` is the unique bounded measurable solution of
  `Q = r + γ P (s' ↦ ⨆ a, Q (s', a))`.

These are the statements of [P, §6.2] for finitely many actions, there for a countable state space,
here on a general measurable state space.

## Main statements

* `Learning.MDP.bellman_optValue`: `T v* = v*` [P, Theorem 6.2.5 (a)];
  `Learning.MDP.measurable_optValue`: `v*` is measurable.
* `Learning.MDP.value_greedy_optValue`: the greedy policy for `v*` has value `v*`
  [P, Theorem 6.2.7 (b)].
* `Learning.MDP.isGreatest_runValue`: from every initial law `μ`, `∫ v* dμ` is the largest
  discounted value of an algorithm, attained by the greedy policy for `v*`.
* `Learning.MDP.isGreatest_value`: `v*` is the largest value of a measurable deterministic
  stationary policy [P, Theorems 6.2.7 (c), 6.2.10 (a)].
* `Learning.MDP.value_eq_optValue_iff`: a stationary policy is optimal if and only if its value
  solves the optimality equation [P, Theorem 6.2.6].
* `Learning.MDP.iSup_optQValue`, `Learning.MDP.lookahead_iSup_optQValue`,
  `Learning.MDP.eq_optQValue_of_lookahead_iSup_eq`: the optimality equation for action values and
  the uniqueness of its bounded measurable solution.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.2
-/

public section

open MeasureTheory ProbabilityTheory Set Learning LMLExplore
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  [Nonempty 𝓐] {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C B : ℝ}

/-! ### The optimal value solves the optimality equation -/

section Finite

variable [Finite 𝓐]

/-- **The optimality equation** [P, Theorem 6.2.5 (a)]: with finitely many actions, bounded
rewards and `γ < 1`, the optimal value is a fixed point of the Bellman optimality operator. By
`Learning.MDP.eq_optValue_of_bellman_eq`, it is its only bounded measurable fixed point. -/
theorem bellman_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.bellman γ (M.optValue γ) = M.optValue γ := by
  obtain ⟨u, hu, huB, hu_eq⟩ := exists_bellman_eq (M := M) hγ hR
  rwa [← eq_optValue_of_bellman_eq hγ hR hu huB hu_eq]

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal value is measurable. -/
theorem measurable_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Measurable (M.optValue γ) := by
  obtain ⟨u, hu, huB, hu_eq⟩ := exists_bellman_eq (M := M) hγ hR
  rwa [← eq_optValue_of_bellman_eq hγ hR hu huB hu_eq]

/-- With finitely many actions, bounded rewards and `γ < 1`, the discounted value of every
algorithm from the probability measure `μ` is at most `∫ v* dμ`. -/
theorem runValue_le_integral_optValue {μ : Measure 𝓢} [IsProbabilityMeasure μ] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (alg : Algorithm 𝓢 𝓐 ℝ) :
    M.runValue γ alg μ ≤ ∫ s, M.optValue γ s ∂μ :=
  runValue_le_integral_of_lookahead_le hγ hR (measurable_optValue hγ hR) (abs_optValue_le hγ hR)
    (fun p ↦ (lookahead_le_bellman _ p.1 p.2).trans_eq (congrFun (bellman_optValue hγ hR) p.1))
    alg

end Finite

/-! ### The greedy policy for the optimal value -/

section Greedy

variable [Fintype 𝓐]

/-- **The greedy policy for the optimal value is optimal** [P, Theorem 6.2.7 (b)]: with finitely
many actions, bounded rewards and `γ < 1`, the value of the deterministic stationary policy greedy
for `v*` is `v*`. -/
theorem value_greedy_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hg : Measurable (M.greedy γ (M.optValue γ))) :
    M.value γ (Kernel.deterministic (M.greedy γ (M.optValue γ)) hg) = M.optValue γ := by
  refine (eq_value_of_bellmanEval_eq hγ hR (measurable_optValue hγ hR) (abs_optValue_le hγ hR)
    ?_).symm
  rw [bellmanEval_greedy (measurable_optValue hγ hR), bellman_optValue hγ hR]

/-- With finitely many actions, bounded rewards and `γ < 1`, the discounted value of the runs of
the deterministic stationary policy greedy for `v*` from the probability measure `μ` is
`∫ v* dμ`. -/
theorem runValue_policyAlg_greedy {μ : Measure 𝓢} [IsProbabilityMeasure μ] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hg : Measurable (M.greedy γ (M.optValue γ))) :
    M.runValue γ (policyAlg (M.greedy γ (M.optValue γ)) hg) μ = ∫ s, M.optValue γ s ∂μ := by
  rw [policyAlg_eq_markov, runValue_markov_const hγ hR, value_greedy_optValue hγ hR hg]

end Greedy

section Finite

variable [Finite 𝓐]

/-! ### Optimal policies -/

/-- **Optimality from every initial law**: with finitely many actions, bounded rewards and
`γ < 1`, from every probability measure `μ` the largest discounted value of an algorithm is
`∫ v* dμ`, attained by the deterministic stationary policy greedy for `v*`
(`Learning.MDP.runValue_policyAlg_greedy`). -/
theorem isGreatest_runValue {μ : Measure 𝓢} [IsProbabilityMeasure μ] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    IsGreatest (range fun alg : Algorithm 𝓢 𝓐 ℝ ↦ M.runValue γ alg μ)
      (∫ s, M.optValue γ s ∂μ) := by
  have := Fintype.ofFinite 𝓐
  exact ⟨⟨_, runValue_policyAlg_greedy hγ hR (measurable_greedy (measurable_optValue hγ hR))⟩,
    forall_mem_range.2 (runValue_le_integral_optValue hγ hR)⟩

/-- **Existence of an optimal deterministic stationary policy** [P, Theorems 6.2.7 (c),
6.2.10 (a)]: with finitely many actions, bounded rewards and `γ < 1`, the optimal value is the
largest value of a measurable deterministic stationary policy, attained by the policy greedy for
`v*` (`Learning.MDP.value_greedy_optValue`). -/
theorem isGreatest_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    IsGreatest (range fun d : {d : 𝓢 → 𝓐 // Measurable d} ↦
      M.value γ (Kernel.deterministic d d.2)) (M.optValue γ) := by
  have := Fintype.ofFinite 𝓐
  exact ⟨⟨⟨_, measurable_greedy (measurable_optValue hγ hR)⟩, value_greedy_optValue hγ hR _⟩,
    forall_mem_range.2 fun _ ↦ value_le_optValue hγ hR⟩

/-- **A stationary policy is optimal if and only if its value solves the optimality equation**
([P, Theorem 6.2.6], for stationary policies): with finitely many actions, bounded rewards and
`γ < 1`, the value of a stationary policy `π` is the optimal value if and only if it is a fixed
point of the Bellman optimality operator. -/
theorem value_eq_optValue_iff {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.value γ π = M.optValue γ ↔ M.bellman γ (M.value γ π) = M.value γ π := by
  refine ⟨fun h ↦ ?_, eq_optValue_of_bellman_eq hγ hR (measurable_value hγ hR) (abs_value_le hγ hR)⟩
  rw [h]
  exact bellman_optValue hγ hR

/-! ### The optimality equation for action values -/

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal action value is
measurable. -/
theorem measurable_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Measurable (M.optQValue γ) := by
  rw [optQValue_eq_lookahead]
  exact measurable_lookahead (measurable_optValue hγ hR)

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal action value is at most
the optimal value: `Q* (s, a) ≤ v* s`. -/
theorem optQValue_le_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) (a : 𝓐) :
    M.optQValue γ (s, a) ≤ M.optValue γ s := by
  rw [optQValue_eq_lookahead]
  exact (lookahead_le_bellman _ s a).trans_eq (congrFun (bellman_optValue hγ hR) s)

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal value at `s` is the
largest optimal action value at `s`: `v* s = ⨆ a, Q* (s, a)`. -/
theorem iSup_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    ⨆ a, M.optQValue γ (s, a) = M.optValue γ s := by
  rw [optQValue_eq_lookahead, ← bellman_def, bellman_optValue hγ hR]

/-- **The optimality equation for action values**: with finitely many actions, bounded rewards and
`γ < 1`, the optimal action value satisfies `Q* = r + γ P (s' ↦ ⨆ a, Q* (s', a))`. -/
theorem lookahead_iSup_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.lookahead γ (fun s ↦ ⨆ a, M.optQValue γ (s, a)) = M.optQValue γ := by
  rw [funext (iSup_optQValue hγ hR), optQValue_eq_lookahead]

/-- **Uniqueness in the optimality equation for action values**: with finitely many actions,
bounded rewards and `γ < 1`, a bounded measurable solution `Q` of
`Q = r + γ P (s' ↦ ⨆ a, Q (s', a))` is the optimal action value. -/
theorem eq_optQValue_of_lookahead_iSup_eq (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {Q : 𝓢 × 𝓐 → ℝ} (hQ : Measurable Q) (hQB : ∀ p, |Q p| ≤ B)
    (h : M.lookahead γ (fun s ↦ ⨆ a, Q (s, a)) = Q) :
    Q = M.optQValue γ := by
  -- `v s = ⨆ a, Q (s, a)` is a bounded measurable solution of the optimality equation, hence `v*`
  set v : 𝓢 → ℝ := fun s ↦ ⨆ a, Q (s, a)
  have hv : Measurable v := Measurable.iSup fun _ ↦ hQ.comp measurable_prodMk_right
  have hvB (s : 𝓢) : |v s| ≤ B := abs_ciSup_le fun a ↦ hQB (s, a)
  have hTv : M.bellman γ v = v := by
    ext s
    rw [bellman_def, h]
  rw [← h, eq_optValue_of_bellman_eq hγ hR hv hvB hTv, optQValue_eq_lookahead]

end Finite

end Learning.MDP
