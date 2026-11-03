/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
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
* the stopping rule: if `|T v - v| ≤ δ` with `2 γ δ < ε (1 - γ)`, then `|T v - v*| < ε / 2` and
  every policy greedy for `T v` is `ε`-optimal;
* the increments decay geometrically, `|v (n + 1) - v n| ≤ γ ^ n |v 1 - v 0|`, so the stopping rule
  is eventually met, and the policies greedy for `v n` have
  `|v^π - v*| ≤ 2 γ ^ n |v 1 - v 0| / (1 - γ)`;
* the iterates decrease (resp. increase) from the first one with `T v ≤ v` (resp. `v ≤ T v`).

Puterman states these bounds with the sup norm on a countable state space. Here they are
pointwise, with an explicit bound `D` or `δ` on the sup norm, on a general measurable state space.
The bounds involving `v*` assume finitely many actions, the bounds on the iterates countably many,
and the a posteriori bound for policy evaluation none.

## Main statements

* `Learning.MDP.abs_value_sub_le`, `Learning.MDP.abs_optValue_sub_le`: the a posteriori bounds.
* `Learning.MDP.abs_value_sub_optValue_le_of_bellmanEval_eq`: the policies greedy for `w` are
  `2 D / (1 - γ)`-optimal.
* `Learning.MDP.abs_bellman_sub_optValue_lt`, `Learning.MDP.abs_value_sub_optValue_lt`: the
  stopping rule of value iteration [P, Theorem 6.3.1 (c), (d)].
* `Learning.MDP.abs_bellman_iterate_succ_sub_le`: the increments decay geometrically.
* `Learning.MDP.abs_value_sub_optValue_le_of_bellmanEval_iterate_eq`: the policies greedy for the
  iterates [P, Theorem 6.3.3 (e)].
* `Learning.MDP.antitone_bellman_iterate`, `Learning.MDP.monotone_bellman_iterate`: monotone
  iterates [P, Proposition 6.3.2 (b)].

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
  have hWD : dist W (M.bellmanEvalOp γ π hR W) ≤ D := by
    rw [dist_eq_norm]
    refine boundedMeasurable.norm_le_of_forall_le ((abs_nonneg _).trans (hD s)) fun s ↦ ?_
    rw [boundedMeasurable.coeFn_sub, coeFn_bellmanEvalOp, boundedMeasurable.coeFn_mk,
      Pi.sub_apply, abs_sub_comm]
    exact hD s
  calc |M.value γ π s - w s| = |⇑((V - W : boundedMeasurable 𝓢) : ℓ^∞(𝓢, ℝ)) s| := by
        rw [boundedMeasurable.coeFn_sub, Pi.sub_apply, boundedMeasurable.coeFn_mk,
          boundedMeasurable.coeFn_mk]
    _ ≤ dist W (ContractingWith.fixedPoint _ hT) := by
        rw [← hV, dist_comm, dist_eq_norm]
        exact boundedMeasurable.abs_apply_le_norm _ s
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

/-! ### The stopping rule of value iteration -/

/-- With finitely many actions, rewards bounded by `C` and `γ < 1`, if a bounded measurable `v`
satisfies `|T v - v| ≤ δ`, then `T v` is within `γ * δ / (1 - γ)` of the optimal value. -/
theorem abs_bellman_sub_optValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hδ : ∀ s, |M.bellman γ v s - v s| ≤ δ) (s : 𝓢) :
    |M.bellman γ v s - M.optValue γ s| ≤ γ * δ / (1 - γ) := by
  have h := abs_bellman_sub_le (M := M) (γ := γ) (fun p ↦ integrable_of_abs_le hv hvB (M.P p))
    (fun p ↦ integrable_of_abs_le (measurable_optValue hγ hR) (abs_optValue_le hγ hR) (M.P p))
    (fun s ↦ by rw [abs_sub_comm]; exact abs_optValue_sub_le hγ hR hv hvB hδ s) s
  rwa [bellman_optValue hγ hR, ← mul_div_assoc] at h

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
  -- `T v` moves by at most `γ * δ` under `T`, since `T` is a `γ`-contraction
  have hTv (s : 𝓢) : |M.bellman γ (M.bellman γ v) s - M.bellman γ v s| ≤ γ * δ :=
    abs_bellman_sub_le
      (fun p ↦ integrable_of_abs_le (measurable_bellman hv) (abs_bellman_le hR hvB) (M.P p))
      (fun p ↦ integrable_of_abs_le hv hvB (M.P p)) hδ s
  refine (abs_value_sub_optValue_le_of_bellmanEval_eq hγ hR (measurable_bellman hv)
    (abs_bellman_le hR hvB) hπ hTv s).trans_lt ?_
  rw [div_lt_iff₀ h1γ]
  linarith

end OptimalValue

/-! ### Geometric decay of the increments -/

section Iterates

variable [Countable 𝓐] [Nonempty 𝓐]

/-- **The increments of value iteration decay geometrically**: with countably many actions and
rewards bounded by `C`, if a bounded measurable `v` satisfies `|T v - v| ≤ D`, then
`|T^[n + 1] v - T^[n] v| ≤ γ ^ n * D`. For `γ < 1` and `ε > 0`, the bound `δ = γ ^ n * D` meets
the stopping rule `2 * γ * δ < ε * (1 - γ)` of `Learning.MDP.abs_value_sub_optValue_lt` for all
large `n`, as in [P, Theorem 6.3.1 (b)]. -/
theorem abs_bellman_iterate_succ_sub_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hD : ∀ s, |M.bellman γ v s - v s| ≤ D) (n : ℕ) (s : 𝓢) :
    |(M.bellman γ)^[n + 1] v s - (M.bellman γ)^[n] v s| ≤ γ ^ n * D := by
  have hT := (isBlackwell_bellmanOp (γ := γ) hR).lipschitzWith
    boundedMeasurable.orderUnitNorm_one_eq_norm
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  have hVD : dist V (M.bellmanOp γ hR V) ≤ D := by
    rw [dist_eq_norm]
    refine boundedMeasurable.norm_le_of_forall_le ((abs_nonneg _).trans (hD s)) fun s ↦ ?_
    rw [boundedMeasurable.coeFn_sub, coeFn_bellmanOp, boundedMeasurable.coeFn_mk, Pi.sub_apply,
      abs_sub_comm]
    exact hD s
  calc |(M.bellman γ)^[n + 1] v s - (M.bellman γ)^[n] v s|
      = |⇑(((M.bellmanOp γ hR)^[n] V - (M.bellmanOp γ hR)^[n + 1] V : boundedMeasurable 𝓢) :
          ℓ^∞(𝓢, ℝ)) s| := by
        rw [boundedMeasurable.coeFn_sub, Pi.sub_apply, coeFn_bellmanOp_iterate,
          coeFn_bellmanOp_iterate, boundedMeasurable.coeFn_mk, abs_sub_comm]
    _ ≤ dist ((M.bellmanOp γ hR)^[n] V) ((M.bellmanOp γ hR)^[n + 1] V) := by
        rw [dist_eq_norm]
        exact boundedMeasurable.abs_apply_le_norm _ s
    _ ≤ dist V (M.bellmanOp γ hR V) * γ ^ n := hT.dist_iterate_succ_le_geometric V n
    _ ≤ γ ^ n * D := by
        rw [mul_comm]
        gcongr

/-- **Monotone iterates, decreasing case** ([P, Proposition 6.3.2 (b)]): with countably many
actions and bounded rewards, if a bounded measurable `v` satisfies `T v ≤ v`, then the iterates
`T^[n] v` decrease. Applied to an iterate `v = T^[N] v₀`, the iterates of value iteration decrease
from the first `N` with `T^[N + 1] v₀ ≤ T^[N] v₀`. -/
theorem antitone_bellman_iterate (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (h : M.bellman γ v ≤ v) :
    Antitone fun n ↦ (M.bellman γ)^[n] v := by
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  have hVv : ⇑(V : ℓ^∞(𝓢, ℝ)) = v := boundedMeasurable.coeFn_mk ..
  have hV : M.bellmanOp γ hR V ≤ V := boundedMeasurable.le_def.2 fun s ↦ by
    simpa only [coeFn_bellmanOp, hVv] using h s
  intro m n hmn s
  simpa only [coeFn_bellmanOp_iterate, hVv] using
    boundedMeasurable.le_def.1
      ((isBlackwell_bellmanOp hR).monotone.antitone_iterate_of_map_le hV hmn) s

/-- **Monotone iterates, increasing case** ([P, Proposition 6.3.2 (b)]): with countably many
actions and bounded rewards, if a bounded measurable `v` satisfies `v ≤ T v`, then the iterates
`T^[n] v` increase. Applied to an iterate `v = T^[N] v₀`, the iterates of value iteration increase
from the first `N` with `T^[N] v₀ ≤ T^[N + 1] v₀`. -/
theorem monotone_bellman_iterate (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (h : v ≤ M.bellman γ v) :
    Monotone fun n ↦ (M.bellman γ)^[n] v := by
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  have hVv : ⇑(V : ℓ^∞(𝓢, ℝ)) = v := boundedMeasurable.coeFn_mk ..
  have hV : V ≤ M.bellmanOp γ hR V := boundedMeasurable.le_def.2 fun s ↦ by
    simpa only [coeFn_bellmanOp, hVv] using h s
  intro m n hmn s
  simpa only [coeFn_bellmanOp_iterate, hVv] using
    boundedMeasurable.le_def.1
      ((isBlackwell_bellmanOp hR).monotone.monotone_iterate_of_le_map hV hmn) s

end Iterates

/-! ### Greedy policies for the iterates -/

/-- **Greedy policies for the iterates of value iteration** ([P, Theorem 6.3.3 (e)]): with finitely
many actions, rewards bounded by `C` and `γ < 1`, if a bounded measurable `v` satisfies
`|T v - v| ≤ D`, then every stationary policy `π` greedy for the iterate `T^[n] v` has a value
within `2 * γ ^ n * D / (1 - γ)` of the optimal value. -/
theorem abs_value_sub_optValue_le_of_bellmanEval_iterate_eq [Nonempty 𝓢] [Finite 𝓐] [Nonempty 𝓐]
    {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) {n : ℕ}
    (hπ : M.bellmanEval γ π ((M.bellman γ)^[n] v) = M.bellman γ ((M.bellman γ)^[n] v))
    (hD : ∀ s, |M.bellman γ v s - v s| ≤ D) (s : 𝓢) :
    |M.value γ π s - M.optValue γ s| ≤ 2 * γ ^ n * D / (1 - γ) := by
  set V := boundedMeasurable.mk v hv (bddAbove_def.2 ⟨B, forall_mem_range.2 hvB⟩)
  -- the iterate `T^[n] v` is bounded measurable, as an iterate of `M.bellmanOp γ hR`
  have hn : (M.bellman γ)^[n] v = ⇑((M.bellmanOp γ hR)^[n] V : ℓ^∞(𝓢, ℝ)) := by
    rw [coeFn_bellmanOp_iterate, boundedMeasurable.coeFn_mk]
  have h := abs_value_sub_optValue_le_of_bellmanEval_eq hγ hR (w := (M.bellman γ)^[n] v)
    (hn ▸ boundedMeasurable.measurable _) (hn ▸ boundedMeasurable.abs_apply_le_norm _) hπ
    (fun s ↦ by
      rw [← iterate_succ_apply' (M.bellman γ)]
      exact abs_bellman_iterate_succ_sub_le hR hv hvB hD n s) s
  rwa [← mul_assoc] at h

end Learning.MDP
