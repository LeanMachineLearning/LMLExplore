/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Comparison
public import LMLExplore.MarkovDecisionProcess.ValueIteration

/-!
# Policy iteration for discounted Markov decision processes

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with bounded rewards, finitely many actions and a discount factor
`0 ≤ γ < 1`, and write `T = M.bellman γ` for its Bellman optimality operator, `T_π` for the
evaluation operator `M.bellmanEval γ π` of a stationary policy `π`, `v^π` for the value of `π`
and `v*` for the optimal value. *Policy iteration* starts from a measurable deterministic
stationary policy `d 0` and alternates

* *evaluation*: compute the value `v k = v^{d k}` of `d k`;
* *improvement*: choose `d (k + 1)` greedy for `v k`, that is `T_{d (k + 1)} v k = T v k`.

This file proves that policy iteration improves monotonically and converges to the optimal value
at the geometric rate `γ ^ k`, on a general measurable state space, and that it terminates on a
finite state space.

The basic step is *policy improvement*: if `v ≤ T_π v` for a bounded measurable `v`, then
`T_π v ≤ v^π`. Since `v k = T_{d k} v k ≤ T v k = T_{d (k + 1)} v k`, it gives
`v k ≤ T v k ≤ v (k + 1) ≤ v*`, hence `T^[k] v 0 ≤ v k ≤ v*`, and the contraction property of `T`
gives `|v k - v*| ≤ γ ^ k * sup |v 0 - v*|`. On a finite state space there are finitely many
deterministic policies, and the abstract dynamic programming of
`LMLExplore.IsPolicyIteration.exists_le_card_eq` shows that the optimal value is reached after at
most `|𝓐| ^ |𝓢|` improvements. When the improvement keeps `d (k + 1) = d k` whenever `d k` is
already greedy, as in Puterman's algorithm, the algorithm stops (`d (k + 1) = d k`) exactly when
`d k` is optimal.

Policy iteration is also Newton's method for the equation `T v - v = 0`: with the greedy policy
`d` for `v`, the map `u ↦ T u - u` lies above its affine minorant
`u ↦ T v - v + (γ P_d - I) (u - v)` (the *support inequality*), and the value of `d` is
`v + (I - γ P_d)⁻¹ (T_d v - v)`, the zero of that minorant, written here with the Neumann series
`∑ n, γ ^ n P_d ^ n`.

## Main definitions

* `Learning.MDP.IsPolicyIteration M γ d`: `d` is a run of policy iteration, a sequence of measurable
  deterministic stationary policies each greedy for the value of the previous one.

## Main statements

* `Learning.MDP.value_eq_add_tsum`: for every stationary policy `π` and bounded measurable `v`,
  `v^π = v + ∑ n, γ ^ n P_π ^ n (T_π v - v)`.
* `Learning.MDP.bellmanEval_le_value`: policy improvement, `v ≤ T_π v → T_π v ≤ v^π`.
* `Learning.MDP.bellman_sub_add_le_bellman_sub`: the support inequality [P, Proposition 6.4.3].
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

/-! ### Policy improvement and the Newton form of the value -/

section Improvement

variable [Nonempty 𝓢] {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

/-- **Newton form of the value**: with bounded rewards and `γ < 1`, for every bounded measurable
`v`, the value of the stationary policy `π` is
`v^π = v + ∑ n, γ ^ n P_π ^ n (T_π v - v)`, where `T_π` is the evaluation operator of `π` and
`P_π` its state kernel; that is, `v^π = v + (I - γ P_π)⁻¹ (T_π v - v)`. -/
theorem value_eq_add_tsum (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (s : 𝓢) :
    M.value γ π s = v s + ∑' n, (γ : ℝ) ^ n *
      ∫ s', (M.bellmanEval γ π v s' - v s') ∂((M.stateKernel π ^ n) s) := by
  have h := runValue_markov_const_eq_integral_add_tsum (μ := Measure.dirac s) (π := π) hγ hR hv
    hvB
  rw [runValue_markov_const hγ hR, integral_dirac' _ s (measurable_value hγ hR).stronglyMeasurable,
    integral_dirac' _ s hv.stronglyMeasurable] at h
  simpa only [Measure.dirac_bind (Kernel.measurable _)] using h

/-- **Policy improvement**: with bounded rewards and `γ < 1`, if a bounded measurable `v`
satisfies `v ≤ T_π v`, where `T_π` is the evaluation operator of the stationary policy `π`, then
`T_π v ≤ v^π`. -/
theorem bellmanEval_le_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hle : v ≤ M.bellmanEval γ π v) :
    M.bellmanEval γ π v ≤ M.value γ π :=
  (bellmanEval_mono hR hv hvB (measurable_value hγ hR) (abs_value_le hγ hR)
    (le_value_of_le_bellmanEval hγ hR hv hvB hle)).trans_eq (bellmanEval_value hγ hR)

end Improvement

/-- **Support inequality** [P, Proposition 6.4.3]: if the action `a` is greedy for `v` at the
state `s`, then `T u s - u s ≥ T v s - v s + (γ P_a (u - v) s - (u s - v s))`, where `T` is the
Bellman optimality operator and `P_a (u - v) s = ∫ (u - v) dP (s, a)`. In other words,
`u ↦ T u - u` lies above the affine map `u ↦ T v - v + (γ P_d - I) (u - v)` for a policy `d` greedy
for `v`, which is tangent to it at `v`. -/
theorem bellman_sub_add_le_bellman_sub [Finite 𝓐] {s : 𝓢} {a : 𝓐}
    (hu : Integrable u (M.P (s, a))) (hv : Integrable v (M.P (s, a)))
    (ha : M.lookahead γ v (s, a) = M.bellman γ v s) :
    M.bellman γ v s - v s + ((γ : ℝ) * ∫ s', (u s' - v s') ∂(M.P (s, a)) - (u s - v s)) ≤
      M.bellman γ u s - u s := by
  have hle := lookahead_le_bellman (M := M) (γ := γ) u s a
  rw [lookahead_def] at hle ha
  rw [integral_sub hu hv, ← ha]
  linarith

/-- With finitely many actions, bounded rewards and `γ < 1`, the optimal value is measurable and
is a fixed point of the optimality operator. -/
private lemma measurable_optValue_and_bellman_optValue [Nonempty 𝓢] [Finite 𝓐] [Nonempty 𝓐]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Measurable (M.optValue γ) ∧ M.bellman γ (M.optValue γ) = M.optValue γ := by
  obtain ⟨u, hu, huB, hTu⟩ := exists_bellman_eq hγ hR
  obtain rfl := eq_optValue_of_bellman_eq hγ hR hu huB hTu
  exact ⟨hu, hTu⟩

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
  lookahead_eq (k : ℕ) (s : 𝓢) :
    M.lookahead γ (M.value γ (Kernel.deterministic (d k) (measurable k))) (s, d (k + 1) s) =
      M.bellman γ (M.value γ (Kernel.deterministic (d k) (measurable k))) s

namespace IsPolicyIteration

variable {d : ℕ → 𝓢 → 𝓐} (h : M.IsPolicyIteration γ d) (hγ : γ < 1)
  (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
include h hγ hR

/-- The bounded measurable value of `d k`, as an element of `boundedMeasurable 𝓢`. -/
private noncomputable def valueBM (k : ℕ) : LMLExplore.boundedMeasurable 𝓢 :=
  LMLExplore.boundedMeasurable.mk (M.value γ (Kernel.deterministic (d k) (h.measurable k)))
    (measurable_value hγ hR)
    (bddAbove_def.2 ⟨C / (1 - γ), forall_mem_range.2 (abs_value_le hγ hR)⟩)

private lemma coeFn_valueBM (k : ℕ) :
    ⇑(h.valueBM hγ hR k : ℓ^∞(𝓢, ℝ)) = M.value γ (Kernel.deterministic (d k) (h.measurable k)) :=
  LMLExplore.boundedMeasurable.coeFn_mk ..

/-- The policy `d (k + 1)` of policy iteration attains the optimality operator at the value of
`d k`. -/
theorem bellmanEval_succ_value (k : ℕ) :
    M.bellmanEval γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1)))
      (M.value γ (Kernel.deterministic (d k) (h.measurable k))) =
      M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) := by
  ext s
  rw [bellmanEval_deterministic (measurable_value hγ hR), h.lookahead_eq]

variable [Finite 𝓐]

/-- The value of each policy of policy iteration is below its image by the optimality
operator. -/
theorem value_le_bellman (k : ℕ) :
    M.value γ (Kernel.deterministic (d k) (h.measurable k)) ≤
      M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) := fun s ↦ by
  conv_lhs => rw [← bellmanEval_value hγ hR]
  rw [bellmanEval_deterministic (measurable_value hγ hR)]
  exact lookahead_le_bellman _ s _

variable [Nonempty 𝓢]

/-- **Policy improvement** [P, Proposition 6.4.1]: the value of each policy of policy iteration is
above the image by the optimality operator of the value of the previous one. -/
theorem bellman_le_value_succ (k : ℕ) :
    M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) ≤
      M.value γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) := by
  rw [← h.bellmanEval_succ_value hγ hR k]
  refine bellmanEval_le_value hγ hR (measurable_value hγ hR) (abs_value_le hγ hR) ?_
  rw [h.bellmanEval_succ_value hγ hR k]
  exact h.value_le_bellman hγ hR k

/-- **Policy improvement** [P, Proposition 6.4.1]: the values of policy iteration are
nondecreasing. -/
theorem monotone_value :
    Monotone fun k ↦ M.value γ (Kernel.deterministic (d k) (h.measurable k)) :=
  monotone_nat_of_le_succ fun k ↦
    (h.value_le_bellman hγ hR k).trans (h.bellman_le_value_succ hγ hR k)

omit [Finite 𝓐] in
/-- **Newton form of policy iteration** [P, Proposition 6.4.4]: the value of `d (k + 1)` is
`v k + ∑ n, γ ^ n P ^ n (T v k - v k)`, where `v k` is the value of `d k`, `T` the optimality
operator and `P` the state kernel of `d (k + 1)`; that is,
`v (k + 1) = v k + (I - γ P)⁻¹ (T v k - v k)`. -/
theorem value_succ_eq_add_tsum (k : ℕ) (s : 𝓢) :
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
theorem value_succ_eq_iff [Nonempty 𝓐] (k : ℕ) :
    M.value γ (Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) =
        M.value γ (Kernel.deterministic (d k) (h.measurable k)) ↔
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  refine ⟨fun heq ↦ ?_, fun heq ↦ le_antisymm ?_ (h.monotone_value hγ hR k.le_succ)⟩
  · refine eq_optValue_of_bellman_eq hγ hR (measurable_value hγ hR) (abs_value_le hγ hR)
      (le_antisymm ?_ (h.value_le_bellman hγ hR k))
    exact (h.bellman_le_value_succ hγ hR k).trans heq.le
  · exact (value_le_optValue (π := Kernel.deterministic (d (k + 1)) (h.measurable (k + 1))) hγ
      hR).trans heq.ge

/-- **Stopping rule with ties kept**: if policy iteration keeps the current policy whenever it is
greedy for its own value, as in Puterman's algorithm, then the policy does not change at step `k`
if and only if `d k` is optimal. -/
theorem succ_eq_iff [Nonempty 𝓐]
    (hkeep : ∀ k, (∀ s, M.lookahead γ (M.value γ (Kernel.deterministic (d k) (h.measurable k)))
      (s, d k s) = M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) s) →
      d (k + 1) = d k) (k : ℕ) :
    d (k + 1) = d k ↔
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  rw [← h.value_succ_eq_iff hγ hR k]
  refine ⟨fun heq ↦ ?_, fun heq ↦ hkeep k fun s ↦ ?_⟩
  · -- the value of a deterministic policy only depends on the policy
    have : Kernel.deterministic (d (k + 1)) (h.measurable (k + 1)) =
        Kernel.deterministic (d k) (h.measurable k) := by
      ext1 s; simp [Kernel.deterministic_apply, heq]
    rw [this]
  · -- `d k` is greedy for its value `v k`, since `v k ≤ T v k ≤ v (k + 1) = v k`
    have hT : M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) =
        M.value γ (Kernel.deterministic (d k) (h.measurable k)) :=
      le_antisymm ((h.bellman_le_value_succ hγ hR k).trans heq.le) (h.value_le_bellman hγ hR k)
    rw [← bellmanEval_deterministic (measurable_value hγ hR) (h.measurable k),
      bellmanEval_value hγ hR, hT]

section Convergence

variable [Nonempty 𝓐]

/-- The values of policy iteration, as bounded measurable functions, satisfy
`T (v k) ≤ v (k + 1)` for the optimality operator `T` on bounded measurable functions. -/
private lemma bellmanOp_valueBM_le (k : ℕ) :
    M.bellmanOp γ hR (h.valueBM hγ hR k) ≤ h.valueBM hγ hR (k + 1) :=
  LMLExplore.boundedMeasurable.le_def.2 fun s ↦ by
    rw [coeFn_bellmanOp, coeFn_valueBM, coeFn_valueBM]
    exact h.bellman_le_value_succ hγ hR k s

/-- **Convergence of policy iteration** [P, Theorem 6.4.6]: the values of policy iteration are
above the iterates of the optimality operator from the value of `d 0`. Together with
`Learning.MDP.value_le_optValue`, `T^[k] v 0 ≤ v k ≤ v*`. -/
theorem bellman_iterate_le_value (k : ℕ) :
    (M.bellman γ)^[k] (M.value γ (Kernel.deterministic (d 0) (h.measurable 0))) ≤
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) := fun s ↦ by
  have hle := LMLExplore.boundedMeasurable.le_def.1
    ((isBlackwell_bellmanOp hR).monotone.iterate_le_of_map_le_succ (h.bellmanOp_valueBM_le hγ hR)
      k) s
  rwa [coeFn_bellmanOp_iterate, coeFn_valueBM, coeFn_valueBM] at hle

/-- **Convergence of policy iteration at a geometric rate** (the norm convergence of
[P, Theorem 6.4.6], with its rate): if the value of `d 0` is within `D` of the optimal value, then
the value of `d k` is within `γ ^ k * D` of it. -/
theorem abs_value_sub_optValue_le
    (hD : ∀ s, |M.value γ (Kernel.deterministic (d 0) (h.measurable 0)) s - M.optValue γ s| ≤ D)
    (k : ℕ) (s : 𝓢) :
    |M.value γ (Kernel.deterministic (d k) (h.measurable k)) s - M.optValue γ s| ≤ γ ^ k * D := by
  obtain ⟨hmeas, hfix⟩ := measurable_optValue_and_bellman_optValue (M := M) hγ hR
  set Y := LMLExplore.boundedMeasurable.mk (M.optValue γ) hmeas
    (bddAbove_def.2 ⟨C / (1 - γ), forall_mem_range.2 (abs_optValue_le hγ hR)⟩) with hYdef
  have hY : IsFixedPt (M.bellmanOp γ hR) Y :=
    isFixedPt_bellmanOp_mk hmeas (abs_optValue_le hγ hR) hfix
  have hnorm := (isBlackwell_bellmanOp hR).norm_sub_le_of_map_le_succ
    LMLExplore.boundedMeasurable.orderUnitNorm_one_eq_norm hY (u := h.valueBM hγ hR)
    (fun k ↦ LMLExplore.boundedMeasurable.le_def.2 fun s ↦ by
      rw [coeFn_valueBM, hYdef, LMLExplore.boundedMeasurable.coeFn_mk]
      exact value_le_optValue hγ hR s)
    (h.bellmanOp_valueBM_le hγ hR) k
  -- the coordinates of `valueBM k - Y` are the differences between the values and `v*`
  have hcoe (k : ℕ) (s : 𝓢) :
      ⇑((h.valueBM hγ hR k - Y : LMLExplore.boundedMeasurable 𝓢) : ℓ^∞(𝓢, ℝ)) s =
        M.value γ (Kernel.deterministic (d k) (h.measurable k)) s - M.optValue γ s := by
    rw [LMLExplore.boundedMeasurable.coeFn_sub, Pi.sub_apply, coeFn_valueBM, hYdef,
      LMLExplore.boundedMeasurable.coeFn_mk]
  have h0 : ‖h.valueBM hγ hR 0 - Y‖ ≤ D :=
    LMLExplore.boundedMeasurable.norm_le_of_forall_le ((abs_nonneg _).trans (hD s)) fun s ↦ by
      rw [hcoe]
      exact hD s
  calc |M.value γ (Kernel.deterministic (d k) (h.measurable k)) s - M.optValue γ s|
      ≤ ‖h.valueBM hγ hR k - Y‖ := by
        rw [← hcoe]
        exact LMLExplore.boundedMeasurable.abs_apply_le_norm _ s
    _ ≤ γ ^ k * D := hnorm.trans (by gcongr)

end Convergence

/-- **Finite termination of policy iteration** [P, Theorem 6.4.2]: on a finite state space, the
value of policy iteration reaches the optimal value after at most `|𝓐| ^ |𝓢|` improvements. -/
theorem exists_le_card_value_eq_optValue [Finite 𝓢] [MeasurableSingletonClass 𝓢]
    [MeasurableSingletonClass 𝓐] [Nonempty 𝓐] :
    ∃ k ≤ Nat.card 𝓐 ^ Nat.card 𝓢,
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  have := Fintype.ofFinite 𝓢
  have hpi : LMLExplore.IsPolicyIteration
      (fun d : {d : 𝓢 → 𝓐 // Measurable d} ↦ M.bellmanEval γ (Kernel.deterministic d d.2))
      (M.bellman γ) (fun k ↦ ⟨d k, h.measurable k⟩)
      (fun k ↦ M.value γ (Kernel.deterministic (d k) (h.measurable k))) :=
    ⟨fun _ ↦ bellmanEval_value hγ hR, h.bellmanEval_succ_value hγ hR⟩
  obtain ⟨k, hk, hv⟩ := hpi.exists_le_card_eq LMLExplore.orderUnitNorm_one_eq_norm
    (fun _ ↦ isBlackwell_bellmanEval hR) hγ (fun _ ↦ isGreatest_bellmanEval .of_discrete)
    (measurable_optValue_and_bellman_optValue hγ hR).2
  refine ⟨k, hk.trans ?_, hv⟩
  rw [← Nat.card_fun]
  exact Finite.card_subtype_le _

/-- **Finite termination of policy iteration with ties kept** [P, Theorem 6.4.2]: on a finite
state space, if policy iteration keeps the current policy whenever it is greedy for its own value,
then it stops, with an optimal policy, after at most `|𝓐| ^ |𝓢|` improvements. -/
theorem exists_le_card_succ_eq [Finite 𝓢] [MeasurableSingletonClass 𝓢]
    [MeasurableSingletonClass 𝓐] [Nonempty 𝓐]
    (hkeep : ∀ k, (∀ s, M.lookahead γ (M.value γ (Kernel.deterministic (d k) (h.measurable k)))
      (s, d k s) = M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) s) →
      d (k + 1) = d k) :
    ∃ k ≤ Nat.card 𝓐 ^ Nat.card 𝓢, d (k + 1) = d k ∧
      M.value γ (Kernel.deterministic (d k) (h.measurable k)) = M.optValue γ := by
  obtain ⟨k, hk, hv⟩ := h.exists_le_card_value_eq_optValue hγ hR
  exact ⟨k, hk, (h.succ_eq_iff hγ hR hkeep k).2 hv, hv⟩

end IsPolicyIteration

/-- **Existence of runs of policy iteration**: with finitely many actions, bounded rewards and
`γ < 1`, from every measurable deterministic stationary policy `d₀` starts a run of policy
iteration that keeps the current policy whenever it is greedy for its own value, and otherwise
moves to the greedy policy `Learning.MDP.greedy`. -/
theorem exists_isPolicyIteration [Finite 𝓐] [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {d₀ : 𝓢 → 𝓐} (hd₀ : Measurable d₀) :
    ∃ (d : ℕ → 𝓢 → 𝓐) (h : M.IsPolicyIteration γ d), d 0 = d₀ ∧ ∀ k,
      (∀ s, M.lookahead γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) (s, d k s) =
        M.bellman γ (M.value γ (Kernel.deterministic (d k) (h.measurable k))) s) →
      d (k + 1) = d k := by
  classical
  have := Fintype.ofFinite 𝓐
  -- one improvement step, keeping the current policy when it is greedy for its value
  let step (d : {d : 𝓢 → 𝓐 // Measurable d}) : {d : 𝓢 → 𝓐 // Measurable d} :=
    if ∀ s, M.lookahead γ (M.value γ (Kernel.deterministic d d.2)) (s, d.1 s) =
        M.bellman γ (M.value γ (Kernel.deterministic d d.2)) s then d
    else ⟨M.greedy γ (M.value γ (Kernel.deterministic d d.2)), measurable_greedy
      (measurable_value hγ hR)⟩
  let seq (k : ℕ) := step^[k] ⟨d₀, hd₀⟩
  have hseq (k : ℕ) : seq (k + 1) = step (seq k) := iterate_succ_apply' _ _ _
  refine ⟨fun k ↦ (seq k).1, ⟨fun k ↦ (seq k).2, fun k s ↦ ?_⟩, rfl, fun k hk ↦ ?_⟩
  · simp only [hseq, step]
    split_ifs with hc
    · exact hc s
    · exact lookahead_greedy _ s
  · simp only [hseq, step]
    split_ifs with hc
    · rfl
    · exact absurd hk hc

end Learning.MDP
