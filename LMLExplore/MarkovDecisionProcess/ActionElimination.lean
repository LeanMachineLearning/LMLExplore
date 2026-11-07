/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality
public import LMLExplore.MarkovDecisionProcess.ValueIteration.Bounds

/-!
# Action elimination in discounted MDPs

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢` with finitely many actions and
bounded rewards, and let `0 ≤ γ < 1`. Write `T` for the Bellman optimality operator
`M.bellman γ`, `v*` for the optimal value `M.optValue γ`, `Q* = r + γ P v*` for the optimal action
value `M.optQValue γ` and `v^π` for the value of a stationary policy `π`.

An action `a` is *suboptimal* in the state `s` when `Q* (s, a) < v* s`. Since
`v^π s ≤ ∫ a, Q* (s, a) ∂(π s) ≤ v* s`, a stationary policy that plays suboptimal actions in `s`
with positive probability is not optimal in `s`; conversely, a stationary policy is optimal if and
only if, in every state, it plays almost surely actions that are not suboptimal. Suboptimal actions
can therefore be discarded by algorithms that search for an optimal policy, such as value
iteration and policy iteration.

The optimal action value is not known while the algorithm runs, but bounds on `v*` give a test:
if `vL s ≤ v* s` and `v* ≤ vU`, then `Q* (s, a) ≤ r (s, a) + γ ∫ vU dP (s, a)`, so `a` is
suboptimal in `s` as soon as `r (s, a) + γ ∫ vU dP (s, a) < vL s`. One step of value iteration
from a bounded measurable `v` with `α ≤ T v - v ≤ β` provides the bounds
`T v + γ α / (1 - γ) ≤ v* ≤ T v + γ β / (1 - γ)` ([P, Corollary 6.6.4],
`Learning.MDP.bellman_add_le_optValue`, `Learning.MDP.optValue_le_bellman_add`).

Puterman states these results on a finite state space. Here the state space is a general
measurable space, and the policies are stationary, possibly randomized.

## Main statements

* `Learning.MDP.value_le_integral_optQValue`: `v^π s ≤ ∫ a, Q* (s, a) ∂(π s)`.
* `Learning.MDP.value_lt_optValue_of_measure_ne_zero`,
  `Learning.MDP.value_deterministic_lt_optValue`: a stationary policy that plays a suboptimal
  action in `s` with positive probability is not optimal in `s` [P, Proposition 6.7.1,
  Corollary 6.7.2].
* `Learning.MDP.value_eq_optValue_iff_ae_optQValue_eq`: a stationary policy is optimal if and only
  if it plays almost surely, in every state `s`, actions with `Q* (s, a) = v* s`.
* `Learning.MDP.optQValue_lt_optValue_of_lookahead_lt`,
  `Learning.MDP.value_deterministic_lt_optValue_of_lookahead_lt`: the elimination test with
  bounds `vL s ≤ v* s` and `v* ≤ vU` [P, Proposition 6.7.3].
* `Learning.MDP.optQValue_lt_optValue_of_lookahead_bellman_add_lt`: the elimination test with
  the bounds given by one step of value iteration.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §6.7
-/

public section

open MeasureTheory ProbabilityTheory Set Function LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  [Nonempty 𝓐] [Finite 𝓐] {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C : ℝ}

/-! ### Suboptimal actions and stationary policies -/

section Stationary

variable {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

/-- With finitely many actions, bounded rewards and `γ < 1`, the value of a stationary policy `π`
in the state `s` is at most the mean under `π s` of the optimal action value:
`v^π s ≤ ∫ a, Q* (s, a) ∂(π s)`. -/
theorem value_le_integral_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    M.value γ π s ≤ ∫ a, M.optQValue γ (s, a) ∂(π s) := by
  rw [← integral_qValue hγ hR s]
  exact integral_mono (integrable_qValue_prodMk_left hγ hR s _)
    (integrable_optQValue_prodMk_left hγ hR s _) fun a ↦ qValue_le_optQValue hγ hR (s, a)

/-- The gap `∫ a, (v* s - Q* (s, a)) ∂(π s)` is the difference between `v* s` and the mean of the
optimal action value. -/
private lemma integral_optValue_sub_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (s : 𝓢) :
    ∫ a, (M.optValue γ s - M.optQValue γ (s, a)) ∂(π s) =
      M.optValue γ s - ∫ a, M.optQValue γ (s, a) ∂(π s) := by
  rw [integral_sub (integrable_const _) (integrable_optQValue_prodMk_left hγ hR s _),
    integral_const, probReal_univ, one_smul]

/-- **Elimination of suboptimal actions** ([P, Proposition 6.7.1, Corollary 6.7.2], for
stationary randomized policies): with finitely many actions, bounded rewards and `γ < 1`, if a
stationary policy `π` gives positive probability in the state `s` to the actions `a` with
`Q* (s, a) < v* s`, then `π` is not optimal in `s`: `v^π s < v* s`. -/
theorem value_lt_optValue_of_measure_ne_zero (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {s : 𝓢} (h : π s {a | M.optQValue γ (s, a) < M.optValue γ s} ≠ 0) :
    M.value γ π s < M.optValue γ s := by
  -- the gap `v* s - Q* (s, ·)` is nonnegative, and positive exactly on the suboptimal actions
  have hnonneg : 0 ≤ fun a ↦ M.optValue γ s - M.optQValue γ (s, a) :=
    fun a ↦ sub_nonneg.2 (optQValue_le_optValue hγ hR s a)
  have hsupp : support (fun a ↦ M.optValue γ s - M.optQValue γ (s, a)) =
      {a | M.optQValue γ (s, a) < M.optValue γ s} := by
    ext a
    simp only [mem_support, mem_ofPred_eq, sub_ne_zero]
    exact ⟨fun ha ↦ (optQValue_le_optValue hγ hR s a).lt_of_ne ha.symm, fun ha ↦ ha.ne'⟩
  have hpos := (integral_pos_iff_support_of_nonneg hnonneg
    ((integrable_const _).sub (integrable_optQValue_prodMk_left hγ hR s _))).2
    (by rw [hsupp]; exact pos_iff_ne_zero.2 h)
  rw [integral_optValue_sub_optQValue hγ hR] at hpos
  linarith [value_le_integral_optQValue (π := π) hγ hR s]

/-- **Optimal stationary policies play optimal actions**: with finitely many actions, bounded
rewards and `γ < 1`, a stationary policy `π` is optimal if and only if, in every state `s`, it
plays almost surely actions `a` with `Q* (s, a) = v* s`. -/
theorem value_eq_optValue_iff_ae_optQValue_eq (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.value γ π = M.optValue γ ↔ ∀ s, ∀ᵐ a ∂(π s), M.optQValue γ (s, a) = M.optValue γ s := by
  refine ⟨fun h s ↦ ?_, fun h ↦ ?_⟩
  · -- by elimination, `π s` gives no mass to the suboptimal actions
    have hnull : π s {a | M.optQValue γ (s, a) < M.optValue γ s} = 0 := by
      by_contra hne
      exact (value_lt_optValue_of_measure_ne_zero hγ hR hne).ne (congrFun h s)
    exact ae_iff.2 (measure_mono_null
      (fun a ha ↦ (optQValue_le_optValue hγ hR s a).lt_of_ne ha) hnull)
  · -- `v*` is a fixed point of the evaluation operator of `π`, hence its value
    refine (eq_value_of_bellmanEval_eq hγ hR (measurable_optValue hγ hR) (abs_optValue_le hγ hR)
      (funext fun s ↦ ?_)).symm
    rw [bellmanEval_def, ← optQValue_eq_lookahead, integral_congr_ae (h s), integral_const,
      probReal_univ, one_smul]

/-- **Elimination of suboptimal actions** for deterministic policies [P, Proposition 6.7.1,
Corollary 6.7.2]: with finitely many actions, bounded rewards and `γ < 1`, if the action `d s` of
a measurable deterministic stationary policy `d` has `Q* (s, d s) < v* s`, then `d` is not optimal
in `s`: `v^d s < v* s`. -/
theorem value_deterministic_lt_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {d : 𝓢 → 𝓐} (hd : Measurable d) {s : 𝓢} (h : M.optQValue γ (s, d s) < M.optValue γ s) :
    M.value γ (Kernel.deterministic d hd) s < M.optValue γ s := by
  refine value_lt_optValue_of_measure_ne_zero hγ hR ?_
  rw [Kernel.deterministic_apply, Measure.dirac_apply_of_mem h]
  exact one_ne_zero

end Stationary

/-! ### Elimination tests from bounds on the optimal value -/

/-- **The action elimination test** [P, Proposition 6.7.3]: with finitely many actions, bounded
rewards and `γ < 1`, let `vU` be an upper bound of `v*`, integrable for `P (s, a)`, and let `vL s`
be a lower bound of `v* s`. If `r (s, a) + γ ∫ vU dP (s, a) < vL s`, then the action `a` is
suboptimal in `s`: `Q* (s, a) < v* s`. -/
theorem optQValue_lt_optValue_of_lookahead_lt (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {vL vU : 𝓢 → ℝ} {s : 𝓢} {a : 𝓐} (hU : M.optValue γ ≤ vU) (hU_int : Integrable vU (M.P (s, a)))
    (hL : vL s ≤ M.optValue γ s) (h : M.lookahead γ vU (s, a) < vL s) :
    M.optQValue γ (s, a) < M.optValue γ s := by
  rw [optQValue_eq_lookahead]
  exact ((lookahead_mono (integrable_of_abs_le (measurable_optValue hγ hR)
    (abs_optValue_le hγ hR) _) hU_int hU).trans_lt h).trans_le hL

/-- **The action elimination test** for deterministic policies [P, Proposition 6.7.3]: with
finitely many actions, bounded rewards and `γ < 1`, let `vU` be an upper bound of `v*`, integrable
for `P (s, d s)`, and let `vL s` be a lower bound of `v* s`. If a measurable deterministic
stationary policy `d` has `r (s, d s) + γ ∫ vU dP (s, d s) < vL s`, then `d` is not optimal in `s`:
`v^d s < v* s`. -/
theorem value_deterministic_lt_optValue_of_lookahead_lt (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {vL vU : 𝓢 → ℝ} {d : 𝓢 → 𝓐} (hd : Measurable d) {s : 𝓢}
    (hU : M.optValue γ ≤ vU) (hU_int : Integrable vU (M.P (s, d s)))
    (hL : vL s ≤ M.optValue γ s) (h : M.lookahead γ vU (s, d s) < vL s) :
    M.value γ (Kernel.deterministic d hd) s < M.optValue γ s :=
  value_deterministic_lt_optValue hγ hR hd
    (optQValue_lt_optValue_of_lookahead_lt hγ hR hU hU_int hL h)

/-- **The action elimination test after one step of value iteration**: with finitely many actions,
bounded rewards and `γ < 1`, let `v` be a bounded measurable function with `α ≤ T v - v ≤ β`.
The bounds `T v + γ α / (1 - γ) ≤ v* ≤ T v + γ β / (1 - γ)` of [P, Corollary 6.6.4] in the test
`Learning.MDP.optQValue_lt_optValue_of_lookahead_lt` show that, if
`r (s, a) + γ ∫ T v dP (s, a) + γ * (γ β / (1 - γ)) < T v s + γ α / (1 - γ)`, then the action `a` is
suboptimal in `s`: `Q* (s, a) < v* s`. -/
theorem optQValue_lt_optValue_of_lookahead_bellman_add_lt (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {v : 𝓢 → ℝ} {B α β : ℝ} (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (hα : ∀ s, α ≤ M.bellman γ v s - v s)
    (hβ : ∀ s, M.bellman γ v s - v s ≤ β) {s : 𝓢} {a : 𝓐}
    (h : M.lookahead γ (M.bellman γ v) (s, a) + γ * (γ * β / (1 - γ)) <
      M.bellman γ v s + γ * α / (1 - γ)) :
    M.optQValue γ (s, a) < M.optValue γ s := by
  have hTv : Integrable (M.bellman γ v) (M.P (s, a)) :=
    integrable_of_abs_le (measurable_bellman hv) (abs_bellman_le hR hvB) _
  refine optQValue_lt_optValue_of_lookahead_lt (vL := fun s ↦ M.bellman γ v s + γ * α / (1 - γ))
    (vU := M.bellman γ v + fun _ ↦ γ * β / (1 - γ)) hγ hR
    (fun s' ↦ optValue_le_bellman_add hγ hR hv hvB hβ s') (hTv.add (integrable_const _))
    (bellman_add_le_optValue hγ hR hv hvB hα s) ?_
  rwa [lookahead_add_const hTv]

end Learning.MDP
