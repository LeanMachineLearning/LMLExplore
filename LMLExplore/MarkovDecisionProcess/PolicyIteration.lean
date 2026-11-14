/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality

/-!
# Policy iteration for discounted Markov decision processes

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with bounded rewards and a discount factor `0 ≤ γ < 1`, and write
`T = M.bellman γ` for its Bellman optimality operator, `T_π` for the evaluation operator
`M.bellmanEval γ π` of a stationary policy `π`, `v^π` for the value of `π` and `v*` for the
optimal value. *Policy iteration* starts from a measurable deterministic
stationary policy `d 0` and alternates

* *evaluation*: compute the value `v k = v^{d k}` of `d k`;
* *improvement*: choose `d (k + 1)` greedy for `v k`, that is `T_{d (k + 1)} v k = T v k`.

This file proves that policy iteration improves monotonically and converges to the optimal value
at the geometric rate `γ ^ k`, on a general measurable state space, and that it terminates on a
finite state space. The improvement holds for every action set, the comparison with value
iteration for countably many actions, and the statements about the optimal value for finitely
many actions.

The basic step is *policy improvement*, `LMLExplore.map_le_of_le_map` on the bounded measurable
functions: if `v ≤ B v` for a map `B`, and `d` is a policy whose evaluation operator `T_d`
(which satisfies Blackwell's conditions) agrees with `B` at `v`, then `B v ≤ v^d`. It is applied
with `B = T_{d (k + 1)}` and `v = v k`: since `v k = T_{d k} v k ≤ T v k = T_{d (k + 1)} v k`, it
gives `v k ≤ T v k ≤ v (k + 1)` for every action set, without the countability that makes `T`
preserve measurability. The Newton form and the stopping rules are proved directly from the
greediness and this improvement step.

The comparison with value iteration, the geometric rate and the finite termination are instances
of the abstract policy iteration `LMLExplore.IsPolicyIteration`, with the evaluation operators of
the measurable deterministic stationary policies as decisions. On the bounded measurable
functions, for countably many actions, it gives `T^[k] v 0 ≤ v k ≤ v*`
(`LMLExplore.IsPolicyIteration.iterate_le`), and for finitely many actions Blackwell's conditions
for `T` give `‖v k - v*‖ ≤ γ ^ k * ‖v 0 - v*‖` (`LMLExplore.IsPolicyIteration.norm_sub_le`),
stated here pointwise. These comparisons use the closedness of the pointwise order of the bounded
measurable functions. On a finite state space there are finitely many deterministic policies, and
`LMLExplore.IsPolicyIteration.exists_le_card_eq`, applied on the functions `𝓢 → ℝ`, shows that
the optimal value is reached after at most `|𝓐| ^ |𝓢|` improvements. When the improvement keeps
`d (k + 1) = d k` whenever `d k` is already greedy, as in Puterman's algorithm, the algorithm
stops (`d (k + 1) = d k`) exactly when `d k` is optimal.

Policy iteration is also Newton's method for the equation `T v - v = 0`: with the greedy policy
`d` for `v`, the map `u ↦ T u - u` lies above its affine minorant
`u ↦ T v - v + (γ P_d - I) (u - v)` (the *support inequality*
`Learning.MDP.bellman_sub_add_le_bellman_sub` [P, Proposition 6.4.3]), and the value of `d` is
`v + (I - γ P_d)⁻¹ (T_d v - v)`, the zero of that minorant, written with the Neumann series
`∑ n, γ ^ n P_d ^ n` (`Learning.MDP.value_eq_add_tsum`).

## Main definitions

* `Learning.MDP.IsPolicyIteration M γ d`: `d` is a run of policy iteration, a sequence of measurable
  deterministic stationary policies each greedy for the value of the previous one.
* `Learning.MDP.IsPolicyIteration.KeepsGreedy`: the run keeps the current policy whenever it is
  greedy for its own value.

## Main statements

* `Learning.MDP.IsPolicyIteration.bellman_le_value_succ`,
  `Learning.MDP.IsPolicyIteration.monotone_value`: policy iteration improves monotonically
  [P, Proposition 6.4.1].
* `Learning.MDP.IsPolicyIteration.value_succ_eq_add_tsum`: the Newton form of the improvement
  [P, Proposition 6.4.4].
* `Learning.MDP.IsPolicyIteration.bellman_iterate_le_value`,
  `Learning.MDP.IsPolicyIteration.abs_value_sub_optValue_le`: `T^[k] v 0 ≤ v k ≤ v*` and
  `|v k - v*| ≤ γ ^ k * D` when `|v 0 - v*| ≤ D` [P, Theorem 6.4.6].
* `Learning.MDP.IsPolicyIteration.value_succ_eq_iff`,
  `Learning.MDP.IsPolicyIteration.succ_eq_iff`: the values stop increasing, and with ties kept the
  policies stop changing, exactly at the optimal value.
* `Learning.MDP.IsPolicyIteration.exists_le_card_value_eq_optValue`,
  `Learning.MDP.IsPolicyIteration.exists_le_card_succ_eq`: on a finite state space, policy
  iteration reaches the optimal value, and with ties kept terminates, after at most `|𝓐| ^ |𝓢|`
  improvements [P, Theorem 6.4.2].
* `Learning.MDP.exists_isPolicyIteration`: from every measurable deterministic stationary policy
  starts a run of policy iteration that keeps the current policy whenever it is greedy.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.4
-/

public section

open MeasureTheory ProbabilityTheory Function Set Learning
open scoped ENNReal NNReal lp

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {B C D : ℝ} {u v : 𝓢 → ℝ}

/-! ### Runs of policy iteration -/

variable (M γ) in
/-- `d` is a run of *policy iteration* in the MDP `M` with discount factor `γ`: the `d k` are
measurable deterministic stationary policies, and each `d (k + 1)` is greedy for the value of
`d k`, that is, `d (k + 1) s` maximizes `a ↦ r (s, a) + γ * ∫ v^{d k} dP (s, a)` at every
state `s`. -/
structure IsPolicyIteration (d : ℕ → 𝓢 → 𝓐) : Prop where
  /-- The policies are measurable. -/
  measurable (k : ℕ) : Measurable (d k)
  /-- The policy `d (k + 1)` is greedy for the value of `d k`. -/
  isGreedy (k : ℕ) :
    M.IsApproxGreedy γ 0 (M.value γ (Kernel.deterministic (d k) (measurable k))) (d (k + 1))

namespace IsPolicyIteration

/-- The run `d` of policy iteration *keeps the current policy whenever it is greedy* for its own
value, as in Puterman's algorithm: `d (k + 1) = d k` as soon as `d k` is greedy for the value of
`d k`. -/
def KeepsGreedy {d : ℕ → 𝓢 → 𝓐} (h : M.IsPolicyIteration γ d) : Prop :=
  ∀ k, M.IsApproxGreedy γ 0 (M.value γ (Kernel.deterministic (d k) (h.measurable k))) (d k) →
    d (k + 1) = d k

lemma keepsGreedy_def {d : ℕ → 𝓢 → 𝓐} (h : M.IsPolicyIteration γ d) :
    h.KeepsGreedy ↔ ∀ k,
      M.IsApproxGreedy γ 0 (M.value γ (Kernel.deterministic (d k) (h.measurable k))) (d k) →
        d (k + 1) = d k :=
  (Iff.rfl)

variable {d : ℕ → 𝓢 → 𝓐} (h : M.IsPolicyIteration γ d) (hγ : γ < 1)
  (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
include h hγ hR

/-- The policy `d (k + 1)` of policy iteration attains the optimality operator at the value of
`d k`. -/
theorem bellmanEval_succ_value (k : ℕ) :
    M.bellmanEval γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1)))
      (M.value γ (Kernel.deterministic (d k) (h.measurable k))) =
      M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) := by
  exact (isApproxGreedy_zero_iff_bellmanEval_eq (measurable_value hγ hR) _
    (bddAbove_range_lookahead hR (abs_value_le hγ hR))).1 (h.isGreedy k)

/-- **Policy improvement** [P, Proposition 6.4.1]: the value of each policy of policy iteration is
above the image by the optimality operator of the value of the previous one. -/
theorem bellman_le_value_succ (k : ℕ) :
    M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) ≤
      M.value γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) := fun s ↦ by
  -- For uncountably many actions the optimality operator need not map bounded measurable
  -- functions to measurable ones. The abstract policy improvement step is applied with the
  -- evaluation operator of `d (k + 1)` in its place: the two agree at the value of `d k`.
  have hle := LMLExplore.map_le_of_le_map (D := {d : 𝓢 → 𝓐 // Measurable d})
    (T := fun d ↦ M.bellmanEvalOp γ (Kernel.deterministic d d.2) hR)
    (B := M.bellmanEvalOp γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) hR)
    (x := M.valueBM γ (Kernel.deterministic (d k) (h.measurable k)) hγ hR)
    (d := ⟨d (k + 1), h.measurable (k + 1)⟩)
    LMLExplore.boundedMeasurable.orderUnitNorm_one_eq_norm
    (fun _ ↦ isBlackwell_bellmanEvalOp hR) hγ
    (LMLExplore.boundedMeasurable.le_def.2 fun t ↦ by
      simpa only [coeFn_bellmanEvalOp, coeFn_valueBM, h.bellmanEval_succ_value hγ hR k] using
        value_le_bellman hγ hR (h.measurable k) t)
    rfl (isFixedPt_bellmanEvalOp_valueBM hγ hR)
  simpa only [coeFn_bellmanEvalOp, coeFn_valueBM, h.bellmanEval_succ_value hγ hR k] using
    LMLExplore.boundedMeasurable.le_def.1 hle s

/-- **Policy improvement** [P, Proposition 6.4.1]: the values of policy iteration are
nondecreasing. -/
theorem monotone_value :
    Monotone fun k ↦ M.value γ (Kernel.deterministic (d k) (h.measurable k)) :=
  monotone_nat_of_le_succ fun k ↦
    (value_le_bellman hγ hR (h.measurable k)).trans (h.bellman_le_value_succ hγ hR k)

/-- **Newton form of policy iteration** [P, Proposition 6.4.4]: the value of `d (k + 1)` is
`v k + ∑ n, γ ^ n P ^ n (T v k - v k)`, where `v k` is the value of `d k`, `T` the optimality
operator and `P` the state kernel of `d (k + 1)`; that is,
`v (k + 1) = v k + (I - γ P)⁻¹ (T v k - v k)`. -/
theorem value_succ_eq_add_tsum [Nonempty 𝓢] (k : ℕ) (s : 𝓢) :
    M.value γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) s =
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) s + ∑' n, (γ : ℝ) ^ n *
        ∫ s', (M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) s' -
          M.value γ (Kernel.deterministic (d k) (h.measurable k)) s')
          ∂((M.stateKernel (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) ^ n) s) := by
  rw [value_eq_add_tsum hγ hR
    (measurable_value (π := Kernel.deterministic (d k) (h.measurable k)) hγ hR)
    (abs_value_le hγ hR) s, h.bellmanEval_succ_value hγ hR k]

/-- **Stopping rule**: the value of policy iteration does not change at step `k` if and only if
the value of `d k` is the optimal value. -/
theorem value_succ_eq_iff [Nonempty 𝓢] [Finite 𝓐] [Nonempty 𝓐] (k : ℕ) :
    M.value γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) =
        M.value γ (Kernel.deterministic (d k) (h.measurable k)) ↔
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  refine ⟨fun heq ↦ ?_, fun heq ↦ le_antisymm ?_ (h.monotone_value hγ hR k.le_succ)⟩
  · refine eq_optValue_of_bellman_eq hγ hR (measurable_value hγ hR) (abs_value_le hγ hR)
      (le_antisymm ?_ (value_le_bellman hγ hR (h.measurable k)))
    exact (h.bellman_le_value_succ hγ hR k).trans heq.le
  · exact (value_le_optValue (π := Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) hγ
      hR).trans heq.ge

/-- **Stopping rule with ties kept**: if policy iteration keeps the current policy whenever it is
greedy for its own value, as in Puterman's algorithm, then the policy does not change at step `k`
if and only if `d k` is optimal. -/
theorem succ_eq_iff [Nonempty 𝓢] [Finite 𝓐] [Nonempty 𝓐] (hkeep : h.KeepsGreedy) (k : ℕ) :
    d (k + 1) = d k ↔
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  rw [← h.value_succ_eq_iff hγ hR k]
  refine ⟨fun heq ↦ ?_, fun heq ↦ (h.keepsGreedy_def.1 hkeep) k ?_⟩
  · -- the value of a deterministic policy only depends on the policy
    have : Kernel.deterministic (d (k + 1)) (h.measurable (k + 1)) =
        Kernel.deterministic (d k) (h.measurable k) := by
      ext1 s; simp [Kernel.deterministic_apply, heq]
    rw [this]
  · -- `d k` is greedy for its value `v k`, since `v k ≤ T v k ≤ v (k + 1) = v k`
    have hT : M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) =
        M.value γ (Kernel.deterministic (d k) (h.measurable k)) :=
      le_antisymm ((h.bellman_le_value_succ hγ hR k).trans heq.le)
        (value_le_bellman hγ hR (h.measurable k))
    rw [isApproxGreedy_zero_iff_bellmanEval_eq (measurable_value hγ hR) (h.measurable k)
      (bddAbove_range_lookahead hR (abs_value_le hγ hR)), bellmanEval_value hγ hR, hT]

section Convergence

variable [Countable 𝓐] [Nonempty 𝓐]

/-- On the bounded measurable functions, the values of `d` are a run of the abstract policy
iteration of the evaluation operators of the measurable deterministic stationary policies. -/
private lemma isPolicyIteration_valueBM :
    LMLExplore.IsPolicyIteration
      (fun d : {d : 𝓢 → 𝓐 // Measurable d} ↦ M.bellmanEvalOp γ (Kernel.deterministic d d.2) hR)
      (M.bellmanOp γ hR) (fun k ↦ ⟨d k, h.measurable k⟩)
      (fun k ↦ M.valueBM γ (Kernel.deterministic (d k) (h.measurable k)) hγ hR) where
  isFixedPt _ := isFixedPt_bellmanEvalOp_valueBM hγ hR
  map_eq k := LMLExplore.boundedMeasurable.ext fun s ↦ by
    simp only [coeFn_bellmanEvalOp, coeFn_bellmanOp, coeFn_valueBM,
      h.bellmanEval_succ_value hγ hR k]

/-- **Convergence of policy iteration** [P, Theorem 6.4.6]: the values of policy iteration are
above the iterates of the optimality operator from the value of `d 0`. Together with
`Learning.MDP.value_le_optValue`, `T^[k] v 0 ≤ v k ≤ v*`. -/
theorem bellman_iterate_le_value (k : ℕ) :
    (M.bellman γ)^[k] (M.value γ (Kernel.deterministic (d 0) (h.measurable 0))) ≤
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) := fun s ↦ by
  simpa only [coeFn_bellmanOp_iterate, coeFn_valueBM] using LMLExplore.boundedMeasurable.le_def.1
    ((h.isPolicyIteration_valueBM hγ hR).iterate_le
      LMLExplore.boundedMeasurable.orderUnitNorm_one_eq_norm (fun _ ↦ isBlackwell_bellmanEvalOp hR)
      hγ (fun _ ↦ bellmanEvalOp_le_bellmanOp hR) (isBlackwell_bellmanOp hR).monotone k) s

end Convergence

/-- **Convergence of policy iteration at a geometric rate** (the norm convergence of
[P, Theorem 6.4.6], with its rate): if the value of `d 0` is within `D` of the optimal value, then
the value of `d k` is within `γ ^ k * D` of it. -/
theorem abs_value_sub_optValue_le [Nonempty 𝓢] [Finite 𝓐] [Nonempty 𝓐]
    (hD : ∀ s, |M.value γ (Kernel.deterministic (d 0) (h.measurable 0)) s - M.optValue γ s| ≤ D)
    (k : ℕ) (s : 𝓢) :
    |M.value γ (Kernel.deterministic (d k) (h.measurable k)) s - M.optValue γ s| ≤ γ ^ k * D := by
  have hnorm := (h.isPolicyIteration_valueBM hγ hR).norm_sub_le
    LMLExplore.boundedMeasurable.orderUnitNorm_one_eq_norm (fun _ ↦ isBlackwell_bellmanEvalOp hR)
    hγ (fun _ ↦ bellmanEvalOp_le_bellmanOp hR) (isBlackwell_bellmanOp hR)
    (isFixedPt_bellmanOp_optValueBM hγ hR) k
  simpa only [coeFn_valueBM, coeFn_optValueBM] using
    LMLExplore.boundedMeasurable.abs_sub_apply_le_mul_of_norm_sub_le (pow_nonneg γ.coe_nonneg k)
      hnorm (by simpa only [coeFn_valueBM, coeFn_optValueBM] using hD) s

/-- **Finite termination of policy iteration** [P, Theorem 6.4.2]: on a finite state space, the
value of policy iteration reaches the optimal value after at most `|𝓐| ^ |𝓢|` improvements. -/
theorem exists_le_card_value_eq_optValue [Nonempty 𝓢] [Finite 𝓢] [MeasurableSingletonClass 𝓢]
    [Finite 𝓐] [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] :
    ∃ k ≤ Nat.card 𝓐 ^ Nat.card 𝓢,
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  have := Fintype.ofFinite 𝓢
  have hpi : LMLExplore.IsPolicyIteration
      (fun d : {d : 𝓢 → 𝓐 // Measurable d} ↦ M.bellmanEval γ (Kernel.deterministic d d.2))
      (M.bellman γ) (fun k ↦ ⟨d k, h.measurable k⟩)
      (fun k ↦ M.value γ (Kernel.deterministic (d k) (h.measurable k))) :=
    ⟨fun _ ↦ bellmanEval_value hγ hR, h.bellmanEval_succ_value hγ hR⟩
  obtain ⟨k, hk, hv⟩ := hpi.exists_le_card_eq LMLExplore.orderUnitNorm_one_eq_norm
    (fun _ ↦ isBlackwell_bellmanEval hR) hγ
    (fun _ _ ↦ bellmanEval_le_bellman (fun _ ↦ .of_finite) fun _ ↦ Finite.bddAbove_range _)
    isBlackwell_bellman
    (bellman_optValue hγ hR)
  refine ⟨k, hk.trans ?_, hv⟩
  rw [← Nat.card_fun]
  exact Finite.card_subtype_le _

/-- **Finite termination of policy iteration with ties kept** [P, Theorem 6.4.2]: on a finite
state space, if policy iteration keeps the current policy whenever it is greedy for its own value,
then it stops, with an optimal policy, after at most `|𝓐| ^ |𝓢|` improvements. -/
theorem exists_le_card_succ_eq [Nonempty 𝓢] [Finite 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐]
    [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] (hkeep : h.KeepsGreedy) :
    ∃ k ≤ Nat.card 𝓐 ^ Nat.card 𝓢, d (k + 1) = d k ∧
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  obtain ⟨k, hk, hv⟩ := h.exists_le_card_value_eq_optValue hγ hR
  exact ⟨k, hk, (h.succ_eq_iff hγ hR hkeep k).2 hv, hv⟩

end IsPolicyIteration

/-- **Existence of runs of policy iteration**: with finitely many actions, bounded rewards and
`γ < 1`, from every measurable deterministic stationary policy `d₀` starts a run of policy
iteration that keeps the current policy whenever it is greedy for its own value. -/
theorem exists_isPolicyIteration [Finite 𝓐] [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {d₀ : 𝓢 → 𝓐} (hd₀ : Measurable d₀) :
    ∃ (d : ℕ → 𝓢 → 𝓐) (h : M.IsPolicyIteration γ d), d 0 = d₀ ∧ h.KeepsGreedy := by
  classical
  have := Fintype.ofFinite 𝓐
  -- one improvement step, keeping the current policy when it is greedy for its value
  let step (d : {d : 𝓢 → 𝓐 // Measurable d}) : {d : 𝓢 → 𝓐 // Measurable d} :=
    if M.IsApproxGreedy γ 0 (M.value γ (Kernel.deterministic d d.2)) d.1 then d
    else ⟨M.greedy γ (M.value γ (Kernel.deterministic d d.2)), measurable_greedy
      (measurable_value hγ hR)⟩
  let seq (k : ℕ) := step^[k] ⟨d₀, hd₀⟩
  have hseq (k : ℕ) : seq (k + 1) = step (seq k) := iterate_succ_apply' _ _ _
  refine ⟨fun k ↦ (seq k).1, ⟨fun k ↦ (seq k).2, fun k ↦ ?_⟩, rfl,
    (IsPolicyIteration.keepsGreedy_def _).2 fun k hk ↦ ?_⟩
  · simp only [hseq, step]
    split_ifs with hc
    · exact hc
    · exact isApproxGreedy_greedy _
  · simp only [hseq, step]
    split_ifs with hc
    · rfl
    · exact absurd hk hc

end Learning.MDP
