/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality

/-!
# Modified policy iteration for discounted Markov decision processes

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with bounded rewards and a discount factor `0 ≤ γ < 1`, and write
`T = M.bellman γ` for its Bellman optimality operator, `T_d` for the evaluation operator
`M.bellmanEval γ d` of a deterministic stationary policy `d`, `P_d` for its state kernel and `v*`
for the optimal value. *Modified policy iteration* with orders `m : ℕ → ℕ` starts from a value
function `v 0` and alternates

* *improvement*: choose a measurable deterministic policy `d k` greedy for `v k`, that is
  `T_{d k} v k = T v k`;
* *partial evaluation*: apply `m k + 1` steps of the evaluation operator of `d k`,
  `v (k + 1) = T_{d k}^[m k + 1] (v k)`.

For `m = 0` it is value iteration, `v k = T^[k] (v 0)`; for large `m k` the partial evaluation
approximates the value of `d k`, the fixed point of `T_{d k}`, which policy iteration computes
exactly. Each step expands as
`v (k + 1) = v k + ∑ j ≤ m k, (γ P_{d k}) ^ j (T v k - v k)` [P, Proposition 6.5.1].

Started from `v 0 ≤ T v 0`, for instance from the constant `c / (1 - γ)` for a lower bound `c` of
the mean rewards (`Learning.MDP.const_le_bellman_const`, [P, (6.5.8)]), modified policy iteration
increases monotonically to the optimal value at the geometric rate of value iteration:
`v k ≤ T v k ≤ v (k + 1)`, `T^[k] (v 0) ≤ v k ≤ v*` and `|v k - v*| ≤ γ ^ k * D` when
`|v 0 - v*| ≤ D`. These are the convergence results of [P, §6.5], here on a general measurable
state space. The monotonicity statements are the instance, on the bounded measurable functions
with the evaluation operators of the measurable deterministic stationary policies as decisions,
of the abstract dynamic programming of `LMLExplore.IsModifiedPolicyIteration`, and the rate is
`Learning.MDP.abs_sub_optValue_le_of_bellman_le_succ`.

## Main definitions

* `Learning.MDP.IsModifiedPolicyIteration M γ m d v`: `v` is a run of modified policy iteration
  with orders `m` and policies `d`.

## Main statements

* `Learning.MDP.IsModifiedPolicyIteration.eq_add_sum`: the expansion of a step of modified policy
  iteration [P, Proposition 6.5.1].
* `Learning.MDP.IsModifiedPolicyIteration.eq_bellman_iterate`: for `m = 0`, modified policy
  iteration is value iteration.
* `Learning.MDP.IsModifiedPolicyIteration.le_bellman`,
  `Learning.MDP.IsModifiedPolicyIteration.bellman_le_succ`,
  `Learning.MDP.IsModifiedPolicyIteration.monotone`: started from `v 0 ≤ T v 0`, the values satisfy
  `v k ≤ T v k ≤ v (k + 1)`, so they increase.
* `Learning.MDP.IsModifiedPolicyIteration.bellman_iterate_le`,
  `Learning.MDP.IsModifiedPolicyIteration.le_optValue`,
  `Learning.MDP.IsModifiedPolicyIteration.abs_sub_optValue_le`: started from `v 0 ≤ T v 0`, the
  values satisfy `T^[k] (v 0) ≤ v k ≤ v*` and `|v k - v*| ≤ γ ^ k * D` when `|v 0 - v*| ≤ D`.
* `Learning.MDP.exists_isModifiedPolicyIteration`: from every measurable value function and for
  all orders starts a run of modified policy iteration.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.5
-/

public section

open MeasureTheory ProbabilityTheory Function Set Learning
open scoped ENNReal NNReal lp

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {B C D : ℝ}

/-! ### Runs of modified policy iteration -/

variable (M γ) in
/-- `v` is a run of *modified policy iteration* in the MDP `M` with discount factor `γ`, orders
`m` and policies `d`: each `d k` is a measurable deterministic stationary policy greedy for `v k`,
and `v (k + 1)` is obtained from `v k` by `m k + 1` steps of the evaluation operator of `d k`. For
`m = 0` it is value iteration. -/
structure IsModifiedPolicyIteration (m : ℕ → ℕ) (d : ℕ → 𝓢 → 𝓐) (v : ℕ → 𝓢 → ℝ) : Prop where
  /-- The policies are measurable. -/
  measurable_policy (k : ℕ) : Measurable (d k)
  /-- The policy `d k` is greedy for `v k`. -/
  isGreedy (k : ℕ) : M.IsApproxGreedy γ 0 (v k) (d k)
  /-- The value `v (k + 1)` is obtained from `v k` by `m k + 1` steps of the evaluation operator
  of `d k`. -/
  eq_iterate (k : ℕ) :
    v (k + 1) =
      (M.bellmanEval γ (Kernel.deterministic (d k) (measurable_policy k)))^[m k + 1] (v k)

namespace IsModifiedPolicyIteration

variable {m : ℕ → ℕ} {d : ℕ → 𝓢 → 𝓐} {v : ℕ → 𝓢 → ℝ} (h : M.IsModifiedPolicyIteration γ m d v)
include h

/-- The values of modified policy iteration started from a measurable function are measurable. -/
theorem measurable (hv : Measurable (v 0)) (k : ℕ) : Measurable (v k) := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    rw [h.eq_iterate k]
    exact measurable_bellmanEval_iterate ih _

/-- With bounded rewards, the values of modified policy iteration started from a bounded function
are bounded. -/
theorem exists_abs_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hvB : ∀ s, |v 0 s| ≤ B) (k : ℕ) :
    ∃ B', ∀ s, |v k s| ≤ B' := by
  induction k with
  | zero => exact ⟨B, hvB⟩
  | succ k ih =>
    obtain ⟨B', hB'⟩ := ih
    rw [h.eq_iterate k]
    exact exists_abs_bellmanEval_iterate_le hR hB' _

/-- With bounded rewards and a bounded measurable `v 0`, the policy `d k` of modified policy
iteration attains the optimality operator at `v k`. -/
theorem bellmanEval_eq (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable (v 0))
    (hvB : ∀ s, |v 0 s| ≤ B) (k : ℕ) :
    M.bellmanEval γ (Kernel.deterministic (d k) (h.measurable_policy k)) (v k) =
      M.bellman γ (v k) :=
  (isApproxGreedy_zero_iff_bellmanEval_eq (h.measurable hv k) _
    (bddAbove_range_lookahead hR (h.exists_abs_le hR hvB k).choose_spec)).1 (h.isGreedy k)

/-- **The expansion of modified policy iteration** [P, Proposition 6.5.1]: with bounded rewards
and a bounded measurable `v 0`, each step of modified policy iteration is
`v (k + 1) = v k + ∑ j ≤ m k, γ ^ j P ^ j (T v k - v k)`, where `T` is the optimality operator and
`P` the state kernel of `d k`. -/
theorem eq_add_sum (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable (v 0))
    (hvB : ∀ s, |v 0 s| ≤ B) (k : ℕ) (s : 𝓢) :
    v (k + 1) s = v k s + ∑ j ∈ Finset.range (m k + 1), (γ : ℝ) ^ j *
      ∫ s', (M.bellman γ (v k) s' - v k s')
        ∂((M.stateKernel (Kernel.deterministic (d k) (h.measurable_policy k)) ^ j) s) := by
  obtain ⟨B', hB'⟩ := h.exists_abs_le hR hvB k
  rw [h.eq_iterate k, bellmanEval_iterate_eq_add_sum hR (h.measurable hv k) hB',
    h.bellmanEval_eq hR hv hvB k]

/-- **Value iteration is modified policy iteration of order `0`**: with bounded rewards and a
bounded measurable `v 0`, if `m k = 0` for all `k`, the values of modified policy iteration are the
iterates `T^[k] (v 0)` of the optimality operator. -/
theorem eq_bellman_iterate (hm : ∀ k, m k = 0) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable (v 0)) (hvB : ∀ s, |v 0 s| ≤ B) (k : ℕ) :
    v k = (M.bellman γ)^[k] (v 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [h.eq_iterate k, hm k, zero_add, iterate_one, h.bellmanEval_eq hR hv hvB k, ih,
      iterate_succ_apply']

/-! ### Convergence -/

section Convergence

variable (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable (v 0)) (hvB : ∀ s, |v 0 s| ≤ B)
include hR hv hvB

/-- The value `v k` of modified policy iteration, as an element of `boundedMeasurable 𝓢`. -/
private noncomputable def valueBM (k : ℕ) : LMLExplore.boundedMeasurable 𝓢 :=
  LMLExplore.boundedMeasurable.mk (v k) (h.measurable hv k)
    (bddAbove_def.2 ⟨(h.exists_abs_le hR hvB k).choose,
      forall_mem_range.2 (h.exists_abs_le hR hvB k).choose_spec⟩)

private lemma coeFn_valueBM (k : ℕ) : ⇑(h.valueBM hR hv hvB k : ℓ^∞(𝓢, ℝ)) = v k :=
  LMLExplore.boundedMeasurable.coeFn_mk ..

section Countable

variable [Countable 𝓐] [Nonempty 𝓐]

/-- On the bounded measurable functions, `v` is a run of the abstract modified policy iteration of
the evaluation operators of the measurable deterministic stationary policies. -/
private lemma isModifiedPolicyIteration_valueBM :
    LMLExplore.IsModifiedPolicyIteration
      (fun d : {d : 𝓢 → 𝓐 // Measurable d} ↦ M.bellmanEvalOp γ (Kernel.deterministic d d.2) hR)
      (M.bellmanOp γ hR) m (fun k ↦ ⟨d k, h.measurable_policy k⟩) (h.valueBM hR hv hvB) where
  map_eq k := LMLExplore.boundedMeasurable.ext fun s ↦ by
    simp only [coeFn_bellmanEvalOp, coeFn_bellmanOp, coeFn_valueBM, h.bellmanEval_eq hR hv hvB k]
  eq_iterate k := LMLExplore.boundedMeasurable.ext fun s ↦ by
    simp only [coeFn_bellmanEvalOp_iterate, coeFn_valueBM, h.eq_iterate k]

/-- `v 0 ≤ T v 0`, on the bounded measurable functions. -/
private lemma valueBM_zero_le (h₀ : v 0 ≤ M.bellman γ (v 0)) :
    h.valueBM hR hv hvB 0 ≤ M.bellmanOp γ hR (h.valueBM hR hv hvB 0) :=
  LMLExplore.boundedMeasurable.le_def.2 fun s ↦ by
    simpa only [coeFn_bellmanOp, coeFn_valueBM] using h₀ s

/-- Modified policy iteration started below its image by the optimality operator stays below its
image: `v k ≤ T v k`. -/
theorem le_bellman (h₀ : v 0 ≤ M.bellman γ (v 0)) (k : ℕ) : v k ≤ M.bellman γ (v k) :=
  fun s ↦ by
    simpa only [coeFn_bellmanOp, coeFn_valueBM] using LMLExplore.boundedMeasurable.le_def.1
      ((h.isModifiedPolicyIteration_valueBM hR hv hvB).le_map
        (fun _ ↦ (isBlackwell_bellmanEvalOp hR).monotone)
        (fun _ ↦ bellmanEvalOp_le_bellmanOp hR)
        (h.valueBM_zero_le hR hv hvB h₀) k) s

/-- **Improvement in modified policy iteration**: started below its image by the optimality
operator, each value of modified policy iteration is above the image of the previous one,
`T v k ≤ v (k + 1)`. -/
theorem bellman_le_succ (h₀ : v 0 ≤ M.bellman γ (v 0)) (k : ℕ) :
    M.bellman γ (v k) ≤ v (k + 1) := fun s ↦ by
  simpa only [coeFn_bellmanOp, coeFn_valueBM] using LMLExplore.boundedMeasurable.le_def.1
    ((h.isModifiedPolicyIteration_valueBM hR hv hvB).map_le
      (fun _ ↦ (isBlackwell_bellmanEvalOp hR).monotone) (fun _ ↦ bellmanEvalOp_le_bellmanOp hR)
      (h.valueBM_zero_le hR hv hvB h₀) k) s

/-- The values of modified policy iteration started below their image by the optimality operator
increase. -/
theorem monotone (h₀ : v 0 ≤ M.bellman γ (v 0)) : Monotone v :=
  monotone_nat_of_le_succ fun k ↦
    (h.le_bellman hR hv hvB h₀ k).trans (h.bellman_le_succ hR hv hvB h₀ k)

/-- The values of modified policy iteration started below their image by the optimality operator
are above the iterates of value iteration: `T^[k] (v 0) ≤ v k`. -/
theorem bellman_iterate_le (h₀ : v 0 ≤ M.bellman γ (v 0)) (k : ℕ) :
    (M.bellman γ)^[k] (v 0) ≤ v k := fun s ↦ by
  simpa only [coeFn_bellmanOp_iterate, coeFn_valueBM] using LMLExplore.boundedMeasurable.le_def.1
    ((h.isModifiedPolicyIteration_valueBM hR hv hvB).iterate_le
      (fun _ ↦ (isBlackwell_bellmanEvalOp hR).monotone)
      (fun _ ↦ bellmanEvalOp_le_bellmanOp hR) (isBlackwell_bellmanOp hR).monotone
      (h.valueBM_zero_le hR hv hvB h₀) k) s

end Countable

variable [Finite 𝓐] [Nonempty 𝓐] [Nonempty 𝓢]

/-- The values of modified policy iteration started below their image by the optimality operator
are below the optimal value. -/
theorem le_optValue (hγ : γ < 1) (h₀ : v 0 ≤ M.bellman γ (v 0)) (k : ℕ) :
    v k ≤ M.optValue γ := by
  obtain ⟨B', hB'⟩ := h.exists_abs_le hR hvB k
  exact le_optValue_of_le_bellman hγ hR (h.measurable hv k) hB' (h.le_bellman hR hv hvB h₀ k)

/-- **Convergence of modified policy iteration at a geometric rate** [P, §6.5]: started below its
image by the optimality operator and within `D` of the optimal value, modified policy iteration
is within `γ ^ k * D` of the optimal value after `k` steps. -/
theorem abs_sub_optValue_le (hγ : γ < 1) (h₀ : v 0 ≤ M.bellman γ (v 0))
    (hD : ∀ s, |v 0 s - M.optValue γ s| ≤ D) (k : ℕ) (s : 𝓢) :
    |v k s - M.optValue γ s| ≤ γ ^ k * D :=
  abs_sub_optValue_le_of_bellman_le_succ hγ hR (h.measurable hv) (h.exists_abs_le hR hvB)
    (h.le_optValue hR hv hvB hγ h₀) (h.bellman_le_succ hR hv hvB h₀) hD k s

end Convergence

end IsModifiedPolicyIteration

/-! ### Existence of runs -/

/-- **Existence of runs of modified policy iteration**: with finitely many actions, for all orders
`m` and every measurable `v₀`, there is a run of modified policy iteration with orders `m` started
from `v₀`, choosing the greedy policy `M.greedy γ (v k)` at every step. -/
theorem exists_isModifiedPolicyIteration [Finite 𝓐] [Nonempty 𝓐] (m : ℕ → ℕ) {v₀ : 𝓢 → ℝ}
    (hv₀ : Measurable v₀) :
    ∃ (d : ℕ → 𝓢 → 𝓐) (v : ℕ → 𝓢 → ℝ), M.IsModifiedPolicyIteration γ m d v ∧ v 0 = v₀ := by
  have := Fintype.ofFinite 𝓐
  -- the step `k` of modified policy iteration with the greedy policy, on measurable functions
  let step (k : ℕ) (w : {w : 𝓢 → ℝ // Measurable w}) : {w : 𝓢 → ℝ // Measurable w} :=
    ⟨(M.bellmanEval γ (Kernel.deterministic (M.greedy γ w.1) (measurable_greedy w.2)))^[m k + 1]
      w.1, measurable_bellmanEval_iterate w.2 _⟩
  let seq (k : ℕ) : {w : 𝓢 → ℝ // Measurable w} := Nat.rec ⟨v₀, hv₀⟩ step k
  -- `seq (k + 1) = step k (seq k)` holds by the defining equation of the recursor
  have hseq (k : ℕ) : seq (k + 1) = step k (seq k) := rfl
  refine ⟨fun k ↦ M.greedy γ (seq k).1, fun k ↦ (seq k).1,
    ⟨fun k ↦ measurable_greedy (seq k).2, fun k ↦ isApproxGreedy_greedy _, fun k ↦ ?_⟩, rfl⟩
  rw [hseq]

end Learning.MDP
