/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality

/-!
# Bellman operators on bounded measurable action values

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP on a measurable state space `𝓢`, with rewards bounded by `C`, and
let `0 ≤ γ < 1`. The Bellman operators of `Learning.MDP.bellmanOp` and
`Learning.MDP.bellmanEvalOp` act on value functions `v : 𝓢 → ℝ`. This file defines their
counterparts on action values `Q : 𝓢 × 𝓐 → ℝ`, as maps of the Banach space
`LMLExplore.boundedMeasurable (𝓢 × 𝓐)` of bounded measurable functions with the sup norm:
* the optimality operator `M.qBellman γ hR`, `Q ↦ r + γ P (s' ↦ ⨆ a', Q (s', a'))`, for countably
  many actions;
* the evaluation operator `M.qBellmanEval γ π hR` of a stationary policy `π`, the affine map
  `Q ↦ r + γ P^π_SA Q`, where the state-action kernel `P^π_SA = M.saKernel π` acts by
  `Kernel.integralCLM`.

They are linked to the operators on values by the lookahead `M.lookaheadOp γ hR`,
`v ↦ r + γ P v`, which maps values to action values: the optimality operator on action values
is the lookahead after the maximum over the actions, and the optimality operator on values is the
maximum over the actions after the lookahead, so that `qBellman ∘ lookahead = lookahead ∘ bellman`.

Both operators satisfy Blackwell's conditions for the constant function `1`, so they are
`γ`-contractions, as the operators on values are [P, Proposition 6.2.4]. Their fixed points are
the action values:
* the optimal action value `Q* = M.optQValue γ` is the unique fixed point of `M.qBellman γ hR`;
* the action value `Q^π = M.qValue γ π` of a stationary policy is the unique fixed point of
  `M.qBellmanEval γ π hR`, and `Q^π = (1 - γ P^π_SA)⁻¹ r` in the Banach algebra of continuous
  linear maps of `boundedMeasurable (𝓢 × 𝓐)`, as `v^π = (1 - γ P_π)⁻¹ r_π` for values
  (`Learning.MDP.ringInverse_apply_policyRewardBM`).

The contraction of `M.qBellman γ hR` for the sup norm is the property of the Bellman operator on
which the convergence of Q-learning rests [Tsi94].

## Main definitions

* `Learning.MDP.meanRewardBM M hR`: the mean reward as an element of
  `boundedMeasurable (𝓢 × 𝓐)`.
* `Learning.MDP.lookaheadOp M γ hR`: the lookahead `v ↦ r + γ P v`, from bounded measurable values
  to bounded measurable action values.
* `Learning.MDP.qBellman M γ hR`: the optimality operator on bounded measurable action values.
* `Learning.MDP.qBellmanEval M γ π hR`: the evaluation operator `Q ↦ r + γ P^π_SA Q` of the
  stationary policy `π`.
* `Learning.MDP.optQValueBM M γ hγ hR`, `Learning.MDP.qValueBM M γ π hγ hR`: the action values
  `Q*` and `Q^π` as elements of `boundedMeasurable (𝓢 × 𝓐)`.

## Main statements

* `Learning.MDP.qBellman_lookaheadOp`: `qBellman (r + γ P v) = r + γ P (bellman v)`;
  `Learning.MDP.coeFn_bellmanOp_apply`: `bellman v s = ⨆ a, (r + γ P v) (s, a)`.
* `Learning.MDP.isBlackwell_qBellman`, `Learning.MDP.contractingWith_qBellman`,
  `Learning.MDP.isBlackwell_qBellmanEval`, `Learning.MDP.contractingWith_qBellmanEval`: the
  operators satisfy Blackwell's conditions and are `γ`-contractions of
  `boundedMeasurable (𝓢 × 𝓐)`.
* `Learning.MDP.abs_lookahead_iSup_sub_le`: the contraction of the optimality operator, stated
  pointwise for bounded measurable action values.
* `Learning.MDP.isFixedPt_qBellman_iff`: `Q*` is the unique fixed point of the optimality
  operator.
* `Learning.MDP.isFixedPt_qBellmanEval_iff`, `Learning.MDP.ringInverse_apply_meanRewardBM`: `Q^π`
  is the unique fixed point of the evaluation operator, and `Q^π = (1 - γ P^π_SA)⁻¹ r`.

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §§6.1–6.2
* [J. N. Tsitsiklis, *Asynchronous stochastic approximation and Q-learning*, 1994][Tsi94]
-/

public section

open MeasureTheory ProbabilityTheory Set Function LMLExplore Learning
open scoped ENNReal NNReal lp

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {B B' C D : ℝ}

/-! ### The mean reward and the lookahead -/

section Lookahead

variable (M) in
/-- The mean reward `r` of `M`, for rewards bounded by `C`, as a bounded measurable function on
the state-action pairs. -/
noncomputable def meanRewardBM (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    boundedMeasurable (𝓢 × 𝓐) :=
  boundedMeasurable.mk (meanReward M.R) (measurable_meanReward M.R)
    (bddAbove_def.2 ⟨C, forall_mem_range.2 (abs_meanReward_le hR)⟩)

@[simp]
lemma coeFn_meanRewardBM (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    ⇑(M.meanRewardBM hR : ℓ^∞(𝓢 × 𝓐, ℝ)) = meanReward M.R :=
  boundedMeasurable.coeFn_mk ..

variable (M γ) in
/-- The lookahead `v ↦ r + γ P v` of `M`, for rewards bounded by `C`, as an affine map from the
bounded measurable functions on `𝓢` to the bounded measurable functions on `𝓢 × 𝓐`, where the
transition kernel `P = M.P` acts by `Kernel.integralCLM`. Pointwise, it is `M.lookahead γ`
(`Learning.MDP.coeFn_lookaheadOp`). -/
noncomputable def lookaheadOp (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    boundedMeasurable (𝓢 × 𝓐) :=
  M.meanRewardBM hR + (γ : ℝ) • M.P.integralCLM v

lemma lookaheadOp_def (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    M.lookaheadOp γ hR v = M.meanRewardBM hR + (γ : ℝ) • M.P.integralCLM v :=
  (rfl)

@[simp]
lemma coeFn_lookaheadOp (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (v : boundedMeasurable 𝓢) :
    ⇑(M.lookaheadOp γ hR v : ℓ^∞(𝓢 × 𝓐, ℝ)) = M.lookahead γ ⇑(v : ℓ^∞(𝓢, ℝ)) := by
  ext p
  simp only [lookaheadOp_def, boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, coeFn_meanRewardBM, Kernel.integralCLM_apply,
    lookahead_def]

end Lookahead

/-! ### The optimality operator on action values -/

section Optimality

/-- The maximum over the actions of a bounded measurable action value is measurable. -/
private lemma measurable_iSup_apply [Countable 𝓐] (Q : boundedMeasurable (𝓢 × 𝓐)) :
    Measurable fun s ↦ ⨆ a, ⇑(Q : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a) :=
  Measurable.iSup fun _ ↦ (boundedMeasurable.measurable Q).comp measurable_prodMk_right

/-- The maximum over the actions of a bounded measurable action value is bounded by its norm. -/
private lemma abs_iSup_apply_le [Nonempty 𝓐] (Q : boundedMeasurable (𝓢 × 𝓐)) (s : 𝓢) :
    |⨆ a, ⇑(Q : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a)| ≤ ‖Q‖ :=
  abs_ciSup_le fun a ↦ boundedMeasurable.abs_apply_le_norm Q (s, a)

private lemma bddAbove_range_apply (Q : boundedMeasurable (𝓢 × 𝓐)) (s : 𝓢) :
    BddAbove (range fun a ↦ ⇑(Q : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a)) :=
  bddAbove_def.2 ⟨‖Q‖, forall_mem_range.2 fun a ↦
    (le_abs_self _).trans (boundedMeasurable.abs_apply_le_norm Q (s, a))⟩

variable [Countable 𝓐] [Nonempty 𝓐]

variable (M γ) in
/-- The Bellman optimality operator on action values,
`Q ↦ r + γ P (s' ↦ ⨆ a', Q (s', a'))`, for countably many actions and rewards bounded by `C`, as a
map of the bounded measurable functions on `𝓢 × 𝓐`. -/
noncomputable def qBellman (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (Q : boundedMeasurable (𝓢 × 𝓐)) :
    boundedMeasurable (𝓢 × 𝓐) :=
  boundedMeasurable.mk (M.lookahead γ fun s ↦ ⨆ a, ⇑(Q : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a))
    (measurable_lookahead (measurable_iSup_apply Q))
    (bddAbove_def.2 ⟨C + γ * ‖Q‖, forall_mem_range.2 (abs_lookahead_le hR (abs_iSup_apply_le Q))⟩)

variable (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)

@[simp]
lemma coeFn_qBellman (Q : boundedMeasurable (𝓢 × 𝓐)) :
    ⇑(M.qBellman γ hR Q : ℓ^∞(𝓢 × 𝓐, ℝ)) =
      M.lookahead γ fun s ↦ ⨆ a, ⇑(Q : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a) :=
  boundedMeasurable.coeFn_mk ..

/-- The optimality operator on values is the maximum over the actions of the lookahead:
`M.bellman γ v s = ⨆ a, (r + γ P v) (s, a)`. -/
lemma coeFn_bellmanOp_apply (v : boundedMeasurable 𝓢) (s : 𝓢) :
    ⇑(M.bellmanOp γ hR v : ℓ^∞(𝓢, ℝ)) s = ⨆ a, ⇑(M.lookaheadOp γ hR v : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a) := by
  rw [coeFn_bellmanOp, coeFn_lookaheadOp, bellman_def]

/-- **The optimality operators on values and on action values are conjugate by the lookahead**:
`qBellman (r + γ P v) = r + γ P (bellman v)`. -/
theorem qBellman_lookaheadOp (v : boundedMeasurable 𝓢) :
    M.qBellman γ hR (M.lookaheadOp γ hR v) = M.lookaheadOp γ hR (M.bellmanOp γ hR v) :=
  boundedMeasurable.ext fun p ↦ by
    rw [coeFn_qBellman, coeFn_lookaheadOp, coeFn_lookaheadOp, coeFn_bellmanOp]
    congr 1
    exact funext fun s ↦ (bellman_def M γ _ s).symm

/-- With bounded rewards and countably many actions, the optimality operator on action values
satisfies Blackwell's conditions on the bounded measurable functions, for the constant
function `1`. -/
theorem isBlackwell_qBellman : IsBlackwell 1 γ (M.qBellman γ hR) where
  monotone Q Q' hQQ' := boundedMeasurable.le_def.2 fun p ↦ by
    simp only [coeFn_qBellman]
    refine lookahead_mono
      (integrable_of_abs_le (measurable_iSup_apply Q) (abs_iSup_apply_le Q) _)
      (integrable_of_abs_le (measurable_iSup_apply Q') (abs_iSup_apply_le Q') _) fun s ↦ ?_
    exact ciSup_mono (bddAbove_range_apply Q' s) fun a ↦ boundedMeasurable.le_def.1 hQQ' (s, a)
  map_add_smul_le Q c _ := le_of_eq <| boundedMeasurable.ext fun p ↦ by
    have h : (fun s ↦ ⨆ a, ⇑((Q + c • 1 : boundedMeasurable (𝓢 × 𝓐)) : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a)) =
        (fun s ↦ ⨆ a, ⇑(Q : ℓ^∞(𝓢 × 𝓐, ℝ)) (s, a)) + fun _ ↦ c := by
      ext s
      simp only [boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul,
        boundedMeasurable.coeFn_one, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
        mul_one]
      exact ((OrderIso.addRight c).map_ciSup (bddAbove_range_apply Q s)).symm
    rw [coeFn_qBellman, h, lookahead_add_const
      (integrable_of_abs_le (measurable_iSup_apply Q) (abs_iSup_apply_le Q) _)]
    simp only [boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul,
      boundedMeasurable.coeFn_one, coeFn_qBellman, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, mul_one]

/-- With bounded rewards, countably many actions and `γ < 1`, the optimality operator on action
values is a `γ`-contraction of the bounded measurable functions with the sup norm. -/
theorem contractingWith_qBellman (hγ : γ < 1) : ContractingWith γ (M.qBellman γ hR) :=
  (isBlackwell_qBellman hR).contractingWith boundedMeasurable.orderUnitNorm_one_eq_norm hγ

variable {hR}

/-- With bounded rewards and countably many actions, the optimality operator on action values is
a `γ`-contraction for the sup norm, stated pointwise: if bounded measurable action values `Q` and
`Q'` satisfy `|Q - Q'| ≤ D`, then their images `r + γ P (s' ↦ ⨆ a', Q (s', a'))` differ by at most
`γ * D`. -/
theorem abs_lookahead_iSup_sub_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {Q Q' : 𝓢 × 𝓐 → ℝ}
    (hQ : Measurable Q) (hQB : ∀ p, |Q p| ≤ B) (hQ' : Measurable Q') (hQ'B : ∀ p, |Q' p| ≤ B')
    (hD : ∀ p, |Q p - Q' p| ≤ D) (p : 𝓢 × 𝓐) :
    |M.lookahead γ (fun s ↦ ⨆ a, Q (s, a)) p - M.lookahead γ (fun s ↦ ⨆ a, Q' (s, a)) p| ≤
      γ * D :=
  boundedMeasurable.abs_sub_apply_le_of_isBlackwell_of_coeFn_eq (isBlackwell_qBellman hR)
    (t := fun Q ↦ M.lookahead γ fun s ↦ ⨆ a, Q (s, a)) (coeFn_qBellman hR) hQ hQB hQ' hQ'B hD p

/-! ### The optimal action value is the fixed point -/

variable [Nonempty 𝓢]

variable (M γ) in
/-- With countably many actions, rewards bounded by `C` and `γ < 1`, the optimal action value
`Q* = M.optQValue γ` as an element of `boundedMeasurable (𝓢 × 𝓐)`. It is the unique fixed point of
the optimality operator on action values (`Learning.MDP.isFixedPt_qBellman_iff`). -/
noncomputable def optQValueBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    boundedMeasurable (𝓢 × 𝓐) :=
  boundedMeasurable.mk (M.optQValue γ) (measurable_optQValue hγ hR)
    (bddAbove_def.2 ⟨C / (1 - γ), forall_mem_range.2 (abs_optQValue_le hγ hR)⟩)

@[simp]
lemma coeFn_optQValueBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    ⇑(M.optQValueBM γ hγ hR : ℓ^∞(𝓢 × 𝓐, ℝ)) = M.optQValue γ :=
  boundedMeasurable.coeFn_mk ..

/-- The optimal action value is the lookahead of the optimal value: `Q* = r + γ P v*`. -/
lemma lookaheadOp_optValueBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.lookaheadOp γ hR (M.optValueBM γ hγ hR) = M.optQValueBM γ hγ hR :=
  boundedMeasurable.ext fun p ↦ by
    rw [coeFn_lookaheadOp, coeFn_optValueBM, coeFn_optQValueBM, optQValue_eq_lookahead]

/-- **The optimality equation for action values**: with countably many actions, bounded rewards
and `γ < 1`, a bounded measurable action value is a fixed point of the optimality operator on
action values if and only if it is the optimal action value `Q*`. -/
theorem isFixedPt_qBellman_iff (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {Q : boundedMeasurable (𝓢 × 𝓐)} :
    IsFixedPt (M.qBellman γ hR) Q ↔ Q = M.optQValueBM γ hγ hR := by
  have hQstar : IsFixedPt (M.qBellman γ hR) (M.optQValueBM γ hγ hR) := by
    rw [← lookaheadOp_optValueBM hγ hR, IsFixedPt, qBellman_lookaheadOp,
      isFixedPt_bellmanOp_optValueBM hγ hR]
  exact ⟨fun h ↦ (contractingWith_qBellman hR hγ).fixedPoint_unique' h hQstar, fun h ↦ h ▸ hQstar⟩

end Optimality

/-! ### The evaluation operators and the values of a stationary policy -/

section Evaluation

variable {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

variable (M γ π) in
/-- The evaluation operator of the stationary policy `π` on action values, for rewards bounded by
`C`, as the affine map `Q ↦ r + γ P^π_SA Q` of the bounded measurable functions on `𝓢 × 𝓐`, where
the state-action kernel `P^π_SA = M.saKernel π` acts by `Kernel.integralCLM`. -/
noncomputable def qBellmanEval (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (Q : boundedMeasurable (𝓢 × 𝓐)) : boundedMeasurable (𝓢 × 𝓐) :=
  M.meanRewardBM hR + (γ : ℝ) • (M.saKernel π).integralCLM Q

lemma qBellmanEval_def (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (Q : boundedMeasurable (𝓢 × 𝓐)) :
    M.qBellmanEval γ π hR Q = M.meanRewardBM hR + (γ : ℝ) • (M.saKernel π).integralCLM Q :=
  (rfl)

variable (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)

@[simp]
lemma coeFn_qBellmanEval (Q : boundedMeasurable (𝓢 × 𝓐)) :
    ⇑(M.qBellmanEval γ π hR Q : ℓ^∞(𝓢 × 𝓐, ℝ)) =
      fun p ↦ meanReward M.R p + γ * ∫ q, ⇑(Q : ℓ^∞(𝓢 × 𝓐, ℝ)) q ∂(M.saKernel π p) := by
  ext p
  simp only [qBellmanEval_def, boundedMeasurable.coeFn_add, boundedMeasurable.coeFn_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, coeFn_meanRewardBM, Kernel.integralCLM_apply]

/-- With bounded rewards, the evaluation operator of a stationary policy on action values satisfies
Blackwell's conditions on the bounded measurable functions, for the constant function `1`. -/
theorem isBlackwell_qBellmanEval : IsBlackwell 1 γ (M.qBellmanEval γ π hR) where
  monotone Q Q' hQQ' := by
    simp only [qBellmanEval_def]
    gcongr
    exact Kernel.monotone_integralCLM hQQ'
  map_add_smul_le Q c _ := le_of_eq <| by
    simp only [qBellmanEval_def, map_add, map_smul, Kernel.integralCLM_one]
    module

/-- With bounded rewards and `γ < 1`, the evaluation operator of a stationary policy on action
values is a `γ`-contraction of the bounded measurable functions with the sup norm. -/
theorem contractingWith_qBellmanEval (hγ : γ < 1) :
    ContractingWith γ (M.qBellmanEval γ π hR) :=
  (isBlackwell_qBellmanEval hR).contractingWith boundedMeasurable.orderUnitNorm_one_eq_norm hγ

variable {hR}

variable (M γ π) in
/-- With rewards bounded by `C` and `γ < 1`, the action value `Q^π = M.qValue γ π` of the
stationary policy `π` as an element of `boundedMeasurable (𝓢 × 𝓐)`. It is the unique fixed point
of the evaluation operator of `π` on action values (`Learning.MDP.isFixedPt_qBellmanEval_iff`). -/
noncomputable def qValueBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    boundedMeasurable (𝓢 × 𝓐) :=
  boundedMeasurable.mk (M.qValue γ π) (measurable_qValue hγ hR)
    (bddAbove_def.2 ⟨C / (1 - γ), forall_mem_range.2 (abs_qValue_le hγ hR)⟩)

@[simp]
lemma coeFn_qValueBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    ⇑(M.qValueBM γ π hγ hR : ℓ^∞(𝓢 × 𝓐, ℝ)) = M.qValue γ π :=
  boundedMeasurable.coeFn_mk ..

/-- The action value of a stationary policy is the lookahead of its value: `Q^π = r + γ P v^π`. -/
lemma lookaheadOp_valueBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.lookaheadOp γ hR (M.valueBM γ π hγ hR) = M.qValueBM γ π hγ hR :=
  boundedMeasurable.ext fun p ↦ by
    rw [coeFn_lookaheadOp, coeFn_valueBM, coeFn_qValueBM, qValue_eq_lookahead]

/-- With bounded rewards and `γ < 1`, the action value of a stationary policy is a fixed point of
its evaluation operator on action values. -/
lemma isFixedPt_qBellmanEval_qValueBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    IsFixedPt (M.qBellmanEval γ π hR) (M.qValueBM γ π hγ hR) :=
  boundedMeasurable.ext fun p ↦ by
    rw [coeFn_qBellmanEval, coeFn_qValueBM]
    exact (qValue_eq_meanReward_add hγ hR p).symm

/-- **The action value is the resolvent of the mean reward**: with bounded rewards and `γ < 1`,
`Q^π = (1 - γ P^π_SA)⁻¹ r` in the Banach algebra of continuous linear maps of
`boundedMeasurable (𝓢 × 𝓐)`. -/
theorem ringInverse_apply_meanRewardBM (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Ring.inverse (1 - (γ : ℝ) • (M.saKernel π).integralCLM) (M.meanRewardBM hR) =
      M.qValueBM γ π hγ hR := by
  rw [Kernel.ringInverse_one_sub_smul_integralCLM_apply_eq_iff hγ, ← qBellmanEval_def]
  exact (isFixedPt_qBellmanEval_qValueBM hγ hR).symm

/-- **Evaluation of action values**: with bounded rewards and `γ < 1`, a bounded measurable action
value is a fixed point of the evaluation operator of a stationary policy `π` on action values if
and only if it is the action value `Q^π` of `π`. -/
theorem isFixedPt_qBellmanEval_iff (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {Q : boundedMeasurable (𝓢 × 𝓐)} :
    IsFixedPt (M.qBellmanEval γ π hR) Q ↔ Q = M.qValueBM γ π hγ hR := by
  rw [← ringInverse_apply_meanRewardBM hγ hR, eq_comm,
    Kernel.ringInverse_one_sub_smul_integralCLM_apply_eq_iff hγ, IsFixedPt, qBellmanEval_def,
    eq_comm]

end Evaluation

end Learning.MDP
