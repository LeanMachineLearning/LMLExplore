/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality

/-!
# Value iteration: stopping rule and greedy policies

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢` with bounded rewards, and let
`0 ≤ γ < 1`. Write `T` for the Bellman optimality operator `M.bellman γ`, `T_π` for the evaluation
operator `M.bellmanEval γ π` of a stationary policy `π`, `v^π` for its value `M.value γ π` and `v*`
for the optimal value `M.optValue γ`. Value iteration computes the iterates `v n = T^[n] v₀` of a
bounded measurable `v₀`; they converge to `v*` (`Learning.MDP.abs_bellman_iterate_sub_le`).

This file turns value iteration into an algorithm returning a policy. A stationary policy `π` is
greedy for `w` when `T_π w = T w`; the deterministic policy `M.greedy γ w` is one
(`Learning.MDP.bellmanEval_greedy`). The results are the error bounds of [P, §6.3]:
* a posteriori bounds: `|v^π - w| ≤ D / (1 - γ)` when `|T_π w - w| ≤ D`, and
  `|v* - w| ≤ D / (1 - γ)` when `|T w - w| ≤ D`, so a policy greedy for `w` has
  `|v^π - v*| ≤ 2 D / (1 - γ)`;
* the policies greedy for the iterate `v n` have `|v^π - v*| ≤ 2 γ ^ n D / (1 - γ)`, where
  `|T v₀ - v₀| ≤ D` at every state;
* the stopping rule: if `|T v - v| ≤ δ` with `2 γ δ < ε (1 - γ)`, then `|T v - v*| < ε / 2` and
  every policy greedy for `T v` is `ε`-optimal. Since the increments of value iteration decay
  geometrically (`Learning.MDP.abs_bellman_iterate_succ_sub_le`), the stopping rule is eventually
  met.

Puterman states these bounds with the sup norm on a countable state space. Here they are
pointwise, with an explicit bound `D` or `δ` on the sup norm, on a general measurable state space.
The bounds involving `v*` assume finitely many actions, and the a posteriori bound for policy
evaluation none.

## Main statements

* `Learning.MDP.abs_value_sub_le`, `Learning.MDP.abs_optValue_sub_le`: the a posteriori bounds.
* `Learning.MDP.abs_value_sub_optValue_le_of_bellmanEval_eq`: the policies greedy for `w` are
  `2 D / (1 - γ)`-optimal.
* `Learning.MDP.abs_value_sub_optValue_le_of_bellmanEval_iterate_eq`: the policies greedy for the
  iterates [P, Theorem 6.3.3 (e)].
* `Learning.MDP.abs_bellman_sub_optValue_lt`, `Learning.MDP.abs_value_sub_optValue_lt`: the
  stopping rule of value iteration [P, Theorem 6.3.1 (c), (d)].

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.3
-/

public section

open MeasureTheory ProbabilityTheory Set Function LMLExplore Learning
open scoped ENNReal NNReal lp

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {v w : 𝓢 → ℝ} {B C D δ ε : ℝ}

/-! ### A posteriori bounds -/

/-- **A posteriori bound for policy evaluation**: with rewards bounded by `C` and `γ < 1`, if a
bounded measurable `w` moves by at most `D` under the evaluation operator of a stationary policy
`π`, `|T_π w - w| ≤ D`, then `w` is within `D / (1 - γ)` of the value of `π`. -/
theorem abs_value_sub_le {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hw : Measurable w) (hwB : ∀ s, |w s| ≤ B)
    (hD : ∀ s, |M.bellmanEval γ π w s - w s| ≤ D) (s : 𝓢) :
    |M.value γ π s - w s| ≤ D / (1 - γ) := by
  have hT := contractingWith_bellmanEvalOp (M := M) (γ := γ) (π := π) hR hγ
  set W := boundedMeasurable.mk w hw (bddAbove_def.2 ⟨B, forall_mem_range.2 hwB⟩)
  set V := boundedMeasurable.mk (M.value γ π) (measurable_value hγ hR)
    (bddAbove_def.2 ⟨C / (1 - γ), forall_mem_range.2 (abs_value_le hγ hR)⟩)
  have hV : V = ContractingWith.fixedPoint _ hT := hT.fixedPoint_unique
    (isFixedPt_bellmanEvalOp_mk (measurable_value hγ hR) (abs_value_le hγ hR)
      (bellmanEval_value hγ hR))
  have hWD : dist W (M.bellmanEvalOp γ π hR W) ≤ D :=
    boundedMeasurable.dist_le_of_forall_abs_sub_le ((abs_nonneg _).trans (hD s)) fun s ↦ by
      rw [coeFn_bellmanEvalOp, boundedMeasurable.coeFn_mk, abs_sub_comm]
      exact hD s
  calc |M.value γ π s - w s| = |⇑(V : ℓ^∞(𝓢, ℝ)) s - ⇑(W : ℓ^∞(𝓢, ℝ)) s| := by
        rw [boundedMeasurable.coeFn_mk, boundedMeasurable.coeFn_mk]
    _ ≤ dist W (ContractingWith.fixedPoint _ hT) := by
        rw [← hV, dist_comm]
        exact boundedMeasurable.abs_sub_apply_le_dist _ _ s
    _ ≤ dist W (M.bellmanEvalOp γ π hR W) / (1 - γ) := hT.dist_fixedPoint_le W
    _ ≤ D / (1 - γ) := by
        gcongr
        exact sub_nonneg.2 (NNReal.coe_le_one.2 hγ.le)

section OptimalValue

variable [Nonempty 𝓢] [Finite 𝓐] [Nonempty 𝓐]

/-- **A posteriori bound for the optimal value**: with finitely many actions, rewards bounded by
`C` and `γ < 1`, if a bounded measurable `w` moves by at most `D` under the Bellman optimality
operator, `|T w - w| ≤ D`, then `w` is within `D / (1 - γ)` of the optimal value. -/
theorem abs_optValue_sub_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hw : Measurable w)
    (hwB : ∀ s, |w s| ≤ B) (hD : ∀ s, |M.bellman γ w s - w s| ≤ D) (s : 𝓢) :
    |M.optValue γ s - w s| ≤ D / (1 - γ) := by
  rw [abs_sub_comm]
  simpa using abs_bellman_iterate_sub_le hγ hR hw hwB (measurable_optValue hγ hR)
    (abs_optValue_le hγ hR) (bellman_optValue hγ hR) hD 0 s

/-- **Greedy policies are nearly optimal**: with finitely many actions, rewards bounded by `C` and
`γ < 1`, if a bounded measurable `w` satisfies `|T w - w| ≤ D`, then every stationary policy `π`
greedy for `w`, `T_π w = T w`, has a value within `2 D / (1 - γ)` of the optimal value. -/
theorem abs_value_sub_optValue_le_of_bellmanEval_eq {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hw : Measurable w) (hwB : ∀ s, |w s| ≤ B)
    (hπ : M.bellmanEval γ π w = M.bellman γ w) (hD : ∀ s, |M.bellman γ w s - w s| ≤ D)
    (s : 𝓢) :
    |M.value γ π s - M.optValue γ s| ≤ 2 * D / (1 - γ) := by
  have h₁ := abs_value_sub_le hγ hR hw hwB (π := π) (fun s ↦ hπ ▸ hD s) s
  have h₂ := abs_optValue_sub_le hγ hR hw hwB hD s
  rw [abs_sub_comm] at h₂
  calc |M.value γ π s - M.optValue γ s|
      ≤ |M.value γ π s - w s| + |w s - M.optValue γ s| := abs_sub_le _ _ _
    _ ≤ D / (1 - γ) + D / (1 - γ) := add_le_add h₁ h₂
    _ = 2 * D / (1 - γ) := by ring

/-! ### Greedy policies for the iterates -/

/-- **Greedy policies for the iterates of value iteration** ([P, Theorem 6.3.3 (e)]): with finitely
many actions, rewards bounded by `C` and `γ < 1`, if a bounded measurable `v` satisfies
`|T v - v| ≤ D`, then every stationary policy `π` greedy for the iterate `T^[n] v` has a value
within `2 * γ ^ n * D / (1 - γ)` of the optimal value. -/
theorem abs_value_sub_optValue_le_of_bellmanEval_iterate_eq {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    {n : ℕ}
    (hπ : M.bellmanEval γ π ((M.bellman γ)^[n] v) = M.bellman γ ((M.bellman γ)^[n] v))
    (hD : ∀ s, |M.bellman γ v s - v s| ≤ D) (s : 𝓢) :
    |M.value γ π s - M.optValue γ s| ≤ 2 * γ ^ n * D / (1 - γ) := by
  obtain ⟨K, hK⟩ := exists_abs_bellman_iterate_le (M := M) (γ := γ) hR hvB n
  have h := abs_value_sub_optValue_le_of_bellmanEval_eq hγ hR (w := (M.bellman γ)^[n] v)
    (measurable_bellman_iterate hv n) hK hπ
    (fun s ↦ by
      rw [← iterate_succ_apply' (M.bellman γ)]
      exact abs_bellman_iterate_succ_sub_le hR hv hvB hD n s) s
  rwa [← mul_assoc] at h

/-! ### The stopping rule of value iteration -/

/-- With finitely many actions, rewards bounded by `C` and `γ < 1`, if a bounded measurable `v`
satisfies `|T v - v| ≤ δ`, then `T v` is within `γ * δ / (1 - γ)` of the optimal value. -/
theorem abs_bellman_sub_optValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hδ : ∀ s, |M.bellman γ v s - v s| ≤ δ) (s : 𝓢) :
    |M.bellman γ v s - M.optValue γ s| ≤ γ * δ / (1 - γ) := by
  simpa using abs_bellman_iterate_sub_le hγ hR hv hvB (measurable_optValue hγ hR)
    (abs_optValue_le hγ hR) (bellman_optValue hγ hR) hδ 1 s

/-- **The stopping rule of value iteration**, its bound on the iterate
([P, Theorem 6.3.1 (d)]): with finitely many actions, rewards bounded by `C` and `γ < 1`, if a
bounded measurable `v` satisfies `|T v - v| ≤ δ` with `2 * γ * δ < ε * (1 - γ)`, then `T v` is
within `ε / 2` of the optimal value. -/
theorem abs_bellman_sub_optValue_lt (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hδ : ∀ s, |M.bellman γ v s - v s| ≤ δ)
    (hε : 2 * γ * δ < ε * (1 - γ)) (s : 𝓢) :
    |M.bellman γ v s - M.optValue γ s| < ε / 2 := by
  have h1γ : 0 < 1 - (γ : ℝ) := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  refine (abs_bellman_sub_optValue_le hγ hR hv hvB hδ s).trans_lt ?_
  rw [div_lt_iff₀ h1γ]
  linarith

/-- **The stopping rule of value iteration**, its policy ([P, Theorem 6.3.1 (c)]): with finitely
many actions, rewards bounded by `C` and `γ < 1`, if a bounded measurable `v` satisfies
`|T v - v| ≤ δ` with `2 * γ * δ < ε * (1 - γ)`, then every stationary policy `π` greedy for `T v`
is `ε`-optimal: its value is within `ε` of the optimal value. -/
theorem abs_value_sub_optValue_lt {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hπ : M.bellmanEval γ π (M.bellman γ v) = M.bellman γ (M.bellman γ v))
    (hδ : ∀ s, |M.bellman γ v s - v s| ≤ δ) (hε : 2 * γ * δ < ε * (1 - γ)) (s : 𝓢) :
    |M.value γ π s - M.optValue γ s| < ε := by
  have h1γ : 0 < 1 - (γ : ℝ) := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  refine (abs_value_sub_optValue_le_of_bellmanEval_iterate_eq (n := 1) hγ hR hv hvB hπ hδ
    s).trans_lt ?_
  rw [pow_one, div_lt_iff₀ h1γ]
  linarith

end OptimalValue

end Learning.MDP
