/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import LMLExplore.MarkovDecisionProcess.PerformanceDifference

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import LMLExplore.Analysis.Calculus.FDeriv.Mul

/-!
# The policy gradient theorem

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with finite state and action spaces and bounded rewards, let
`0 ≤ γ < 1` and let `μ` be a probability measure on the states. A *parametrization* is a family
`θ ↦ π_θ` of stationary policies indexed by a real normed space `E`. Write `V(θ) = ∫ v^{π_θ} dμ`
for the discounted value of `π_θ` from `μ`, `d_θ` for the state marginal of its occupancy measure
from `μ` and `Q^{π_θ}` for its action value. The **policy gradient theorem** [SMSM99],
[AJKS, Theorem 11.4] states that if the action probabilities `θ ↦ π_θ (a | s)` are differentiable
at `θ` with derivatives `∇π_θ (a | s)`, then so is `V`, with

`∇V(θ) = (1 - γ)⁻¹ * 𝔼_{s ∼ d_θ} ∑ a, Q^{π_θ} (s, a) * ∇π_θ (a | s)`.

Because the action probabilities sum to one, any *baseline* `b : 𝓢 → ℝ` may be subtracted from
the action values without changing the gradient: `∇V(θ)` is also
`(1 - γ)⁻¹ * 𝔼_{s ∼ d_θ} ∑ a, (Q^{π_θ} (s, a) - b s) * ∇π_θ (a | s)`. The baseline `b = v^{π_θ}`
gives the **advantage form**, with the advantage `A^{π_θ} = Q^{π_θ} - v^{π_θ}` in place of the
action value.

The derivatives are taken within an arbitrary set of parameters (`HasFDerivWithinAt`), so that
the theorem applies both to parametrizations differentiable on an open set and to the direct
parametrization, whose parameters are the action probabilities themselves and range over a product
of simplices. No differentiability of the occupancy measures is assumed: the theorem is the
statement that the first-order change of the value is the change of the action probabilities,
weighted by the action values and by the occupancy measure of the current policy.

## Main statements

* `Learning.MDP.hasFDerivWithinAt_integral_value_baseline`: the policy gradient theorem with a
  baseline `b`, for derivatives within a set;
* `Learning.MDP.hasFDerivWithinAt_integral_value`: the policy gradient theorem, with the action
  values;
* `Learning.MDP.hasFDerivWithinAt_integral_value_advantage`: its advantage form;
* `Learning.MDP.hasFDerivAt_integral_value_baseline`, `Learning.MDP.hasFDerivAt_integral_value`,
  `Learning.MDP.hasFDerivAt_integral_value_advantage`: the same for derivatives at a point.

## Implementation notes

The proof goes through the performance difference lemma rather than through the derivative of the
resolvent `(1 - γ P_π)⁻¹`. The lemma gives
`V(θ') - V(θ) = (1 - γ)⁻¹ * ∑ s, d_θ' {s} * ∑ a, (π_θ' (a | s) - π_θ (a | s)) * Q^{π_θ} (s, a)`.
In this identity the weights `d_θ' {s}` depend continuously on `θ'`, because occupancy measures
depend continuously on the policy in total variation (`Learning.MDP.tendsto_tvDist_fst_occupancy`),
and the inner sums vanish at `θ' = θ`. The product rule with a continuous factor
(`HasFDerivWithinAt.smul_of_eq_zero`) then differentiates it.

## References

* [R. S. Sutton, D. McAllester, S. Singh and Y. Mansour, *Policy gradient methods for
  reinforcement learning with function approximation*, NeurIPS 1999][SMSM99], Theorem 1
* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Theorem 11.4
-/

public section

open MeasureTheory ProbabilityTheory Learning LMLExplore Filter Topology
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Fintype 𝓐]
  [MeasurableSingletonClass 𝓐] {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C : ℝ}

variable {E : Type*} [NormedAddCommGroup E] {π : E → Kernel 𝓢 𝓐} [∀ θ, IsMarkovKernel (π θ)]
  {t : Set E} {θ : E}

variable [Finite 𝓢] [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] {μ : Measure 𝓢}
  [IsProbabilityMeasure μ]

variable [NormedSpace ℝ E] {π' : 𝓢 → 𝓐 → E →L[ℝ] ℝ}

/-- **Policy gradient theorem with a baseline** [SMSM99, Theorem 1], [AJKS, Theorem 11.4]: on
finite state and action spaces, with bounded rewards and `γ < 1`, if the action probabilities
`θ' ↦ π θ' s {a}` of a family of stationary policies have derivatives `π' s a` at `θ` within `t`,
then for every baseline `b : 𝓢 → ℝ` the value `θ' ↦ ∫ v^{π θ'} dμ` has derivative
`(1 - γ)⁻¹ • ∫ s, ∑ a, (Q^{π θ} (s, a) - b s) • π' s a ∂d` at `θ` within `t`, where `d` is the
state marginal of the occupancy measure of `π θ` from `μ`. -/
theorem hasFDerivWithinAt_integral_value_baseline (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hπ : ∀ s a, HasFDerivWithinAt (fun θ' ↦ (π θ' s).real {a}) (π' s a) t θ) (b : 𝓢 → ℝ) :
    HasFDerivWithinAt (fun θ' ↦ ∫ s, M.value γ (π θ') s ∂μ)
      ((1 - γ : ℝ)⁻¹ • ∫ s, ∑ a, (M.qValue γ (π θ) (s, a) - b s) • π' s a
        ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π θ) μ).fst) t θ := by
  have := Fintype.ofFinite 𝓢
  set d : E → Measure 𝓢 := fun θ' ↦ (M.occupancy γ (Algorithm.markov fun _ ↦ π θ') μ).fst
  -- the change of the action probabilities at `s`, weighted by the action values of `π θ`
  set g : 𝓢 → E → ℝ := fun s θ' ↦
    ∑ a, ((π θ' s).real {a} - (π θ s).real {a}) * (M.qValue γ (π θ) (s, a) - b s)
  -- the performance difference lemma against `π θ`
  have hV (θ' : E) : ∫ s, M.value γ (π θ') s ∂μ =
      ∫ s, M.value γ (π θ) s ∂μ + (1 - γ : ℝ)⁻¹ * ∑ s, (d θ').real {s} • g s θ' := by
    rw [← sub_eq_iff_eq_add', integral_value_sub_integral_value hγ hR (π θ) (π θ'),
      integral_fintype .of_finite]
    refine congrArg _ (Finset.sum_congr rfl fun s _ ↦ ?_)
    rw [integral_advantage_eq_sum hγ hR (π θ') s (b s)]
  have hg (s : 𝓢) : HasFDerivWithinAt (g s) (∑ a, (M.qValue γ (π θ) (s, a) - b s) • π' s a)
      t θ :=
    HasFDerivWithinAt.fun_sum fun a _ ↦ ((hπ s a).sub_const _).mul_const _
  have hg0 (s : 𝓢) : g s θ = 0 := by simp [g]
  have hd (s : 𝓢) : ContinuousWithinAt (fun θ' ↦ (d θ').real {s}) t θ :=
    tendsto_measureReal_fst_occupancy hγ (fun s a ↦ (hπ s a).continuousWithinAt.tendsto) s
  have hsum := (HasFDerivWithinAt.fun_sum (u := Finset.univ) fun s _ ↦
    (hg s).smul_of_eq_zero (hg0 s) (hd s)).const_mul (1 - γ : ℝ)⁻¹
  rw [integral_fintype .of_finite]
  exact (hsum.const_add (∫ s, M.value γ (π θ) s ∂μ)).congr_of_eventuallyEq
    (Eventually.of_forall hV) (hV θ)

/-- **Policy gradient theorem** [SMSM99, Theorem 1], [AJKS, Theorem 11.4]: on finite state and
action spaces, with bounded rewards and `γ < 1`, if the action probabilities `θ' ↦ π θ' s {a}`
of a family of stationary policies have derivatives `π' s a` at `θ` within `t`, then the value
`θ' ↦ ∫ v^{π θ'} dμ` has derivative `(1 - γ)⁻¹ • ∫ s, ∑ a, Q^{π θ} (s, a) • π' s a ∂d` at `θ`
within `t`, where `d` is the state marginal of the occupancy measure of `π θ` from `μ`. -/
theorem hasFDerivWithinAt_integral_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hπ : ∀ s a, HasFDerivWithinAt (fun θ' ↦ (π θ' s).real {a}) (π' s a) t θ) :
    HasFDerivWithinAt (fun θ' ↦ ∫ s, M.value γ (π θ') s ∂μ)
      ((1 - γ : ℝ)⁻¹ • ∫ s, ∑ a, M.qValue γ (π θ) (s, a) • π' s a
        ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π θ) μ).fst) t θ := by
  simpa using hasFDerivWithinAt_integral_value_baseline (μ := μ) hγ hR hπ 0

/-- **Policy gradient theorem, advantage form** [AJKS, Theorem 11.4]: on finite state and action
spaces, with bounded rewards and `γ < 1`, if the action probabilities `θ' ↦ π θ' s {a}` of a
family of stationary policies have derivatives `π' s a` at `θ` within `t`, then the value
`θ' ↦ ∫ v^{π θ'} dμ` has derivative `(1 - γ)⁻¹ • ∫ s, ∑ a, A^{π θ} (s, a) • π' s a ∂d` at `θ`
within `t`, where `A^{π θ}` is the advantage of `π θ` and `d` is the state marginal of its
occupancy measure from `μ`. -/
theorem hasFDerivWithinAt_integral_value_advantage (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hπ : ∀ s a, HasFDerivWithinAt (fun θ' ↦ (π θ' s).real {a}) (π' s a) t θ) :
    HasFDerivWithinAt (fun θ' ↦ ∫ s, M.value γ (π θ') s ∂μ)
      ((1 - γ : ℝ)⁻¹ • ∫ s, ∑ a, M.advantage γ (π θ) (s, a) • π' s a
        ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π θ) μ).fst) t θ := by
  simpa [advantage_def] using
    hasFDerivWithinAt_integral_value_baseline (μ := μ) hγ hR hπ (M.value γ (π θ))

/-- **Policy gradient theorem with a baseline** [SMSM99, Theorem 1], [AJKS, Theorem 11.4], for
derivatives at a point: see `Learning.MDP.hasFDerivWithinAt_integral_value_baseline`. -/
theorem hasFDerivAt_integral_value_baseline (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hπ : ∀ s a, HasFDerivAt (fun θ' ↦ (π θ' s).real {a}) (π' s a) θ) (b : 𝓢 → ℝ) :
    HasFDerivAt (fun θ' ↦ ∫ s, M.value γ (π θ') s ∂μ)
      ((1 - γ : ℝ)⁻¹ • ∫ s, ∑ a, (M.qValue γ (π θ) (s, a) - b s) • π' s a
        ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π θ) μ).fst) θ :=
  hasFDerivWithinAt_univ.1 <|
    hasFDerivWithinAt_integral_value_baseline hγ hR (fun s a ↦ (hπ s a).hasFDerivWithinAt) b

/-- **Policy gradient theorem** [SMSM99, Theorem 1], [AJKS, Theorem 11.4], for derivatives at a
point: see `Learning.MDP.hasFDerivWithinAt_integral_value`. -/
theorem hasFDerivAt_integral_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hπ : ∀ s a, HasFDerivAt (fun θ' ↦ (π θ' s).real {a}) (π' s a) θ) :
    HasFDerivAt (fun θ' ↦ ∫ s, M.value γ (π θ') s ∂μ)
      ((1 - γ : ℝ)⁻¹ • ∫ s, ∑ a, M.qValue γ (π θ) (s, a) • π' s a
        ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π θ) μ).fst) θ :=
  hasFDerivWithinAt_univ.1 <|
    hasFDerivWithinAt_integral_value hγ hR (fun s a ↦ (hπ s a).hasFDerivWithinAt)

/-- **Policy gradient theorem, advantage form** [AJKS, Theorem 11.4], for derivatives at a point:
see `Learning.MDP.hasFDerivWithinAt_integral_value_advantage`. -/
theorem hasFDerivAt_integral_value_advantage (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hπ : ∀ s a, HasFDerivAt (fun θ' ↦ (π θ' s).real {a}) (π' s a) θ) :
    HasFDerivAt (fun θ' ↦ ∫ s, M.value γ (π θ') s ∂μ)
      ((1 - γ : ℝ)⁻¹ • ∫ s, ∑ a, M.advantage γ (π θ) (s, a) • π' s a
        ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π θ) μ).fst) θ :=
  hasFDerivWithinAt_univ.1 <|
    hasFDerivWithinAt_integral_value_advantage hγ hR (fun s a ↦ (hπ s a).hasFDerivWithinAt)

end Learning.MDP
