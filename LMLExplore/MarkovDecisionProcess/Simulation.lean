/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality
public import LMLExplore.MarkovDecisionProcess.ReturnVariance
public import LMLExplore.MeasureTheory.Measure.TotalVariation.Basic

/-!
# The simulation lemma

Let `M` and `M'` be two MDPs on the same state and action spaces, with mean rewards `r` and `r'`
and transition kernels `P` and `P'`; typically `M'` is a model of `M` estimated from samples of its
rewards and transitions. For a stationary policy `π` and `0 ≤ γ < 1`, the action values of `π` in
the two models are the resolvents of their state-action kernels applied to their mean rewards,
`Q^π_M = R_γ(P^π_SA) r` and `Q^π_M' = R_γ(P'^π_SA) r'`. The simulation identity for resolvents
with two rewards (`ProbabilityTheory.Kernel.integral_resolvent_sub_integral_resolvent`) compares
them through the reward error and the one-step difference of the transition kernels acting on the
value of `π` in `M`:

`Q^π_M - Q^π_M' = R_γ(P'^π_SA) ((r - r') + γ (P - P') v^π_M)`.

Since `R_γ(P'^π_SA)` has mass `(1 - γ)⁻¹`, a reward error of at most `δ`, `|r - r'| ≤ δ`, and an
error of at most `ε` in the one-step predictions `|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε`
of the model result in an error of at most `δ / (1 - γ) + γ ε / (1 - γ)` in the action values and
the values of `π`. This is the basic tool for planning with an estimated model: errors in the
transitions are measured only through the value of the policy, not uniformly over all functions.

With finitely many actions, the same comparison holds for the optimal action values, as
componentwise bounds. Let `π*` be an optimal stationary policy of `M` and `π'*` one of `M'`, and
write `v*` for the optimal value of `M`. Then

`R_γ(P'^π'*_SA) ((r - r') + γ (P - P') v*) ≤ Q*_M - Q*_M'` and
`Q*_M - Q*_M' ≤ R_γ(P'^π*_SA) ((r - r') + γ (P - P') v*)`.

The upper bound is the simulation lemma for `π*`, since `π*` is suboptimal in `M'`. The lower
bound compares `Q*_M - Q*_M'` with the solution of the resolvent equation of `P'^π'*_SA`: it is a
supersolution, because `π'*` is suboptimal in `M`. Only the fixed function `v*` of `M` enters the
transition error, so that a reward error of at most `δ` and an error of at most `ε` in the
one-step predictions of `v*` result in an error of at most `δ / (1 - γ) + γ ε / (1 - γ)` in the
optimal action values and the optimal values.

When the transition kernels are within `η` in total variation, `tvDist (P (s, a)) (P' (s, a)) ≤ η`
(Mathlib's `tvDist`, with values in `[0, 2]`), and the rewards of `M` satisfy `|r| ≤ C`, the
one-step predictions of every function bounded by `C / (1 - γ)`, such as `v^π_M` and `v*`, differ
by at most `C η / (1 - γ)` (`MeasureTheory.norm_integral_sub_integral_le_mul_tvDist`). The action
values, values, optimal action values and optimal values of the two MDPs then differ by at most
`δ / (1 - γ) + γ C η / (1 - γ) ^ 2`. This is the form in which the simulation lemma is used for a
model estimated from samples, whose kernels concentrate in total variation around the true ones.
Models with the true mean reward, such as the empirical MDP of a generative model, are the case
`δ = 0`.

A variance-aware version [AJKS, §2.4] holds for two MDPs with the same mean rewards and rewards
bounded by `C`. If the one-step predictions of `v*` satisfy the Bernstein-type bound
`|∫ v* dP q - ∫ v* dP' q| ≤ a √(Var_{P' q}(v*)) + b`, the componentwise bounds express
`Q*_M - Q*_M'` through the resolvents `R_γ(P'^π_SA)` of an optimal policy `π` of `M` and of an
optimal policy of `M'`, applied to these one-step errors. The standard deviation of `v*` is within
`‖v* - v'^π‖` of the standard deviation of the value `v'^π` of `π` in `M'`, and the total-variance
lemma (`Learning.MDP.integral_sqrt_variance_value_resolvent_le`) in `M'` bounds the resolvent of
the latter by `C √(2 / (1 - γ) ^ 3)`. The leading term of the resulting bound on `|Q*_M - Q*_M'|`
is `γ a C √(2 / (1 - γ) ^ 3)`, a factor `√(1 - γ)` better than the one given by the uniform bound
`√(Var_{P' q}(v*)) ≤ C / (1 - γ)`.

The same argument applies to the action values of a stationary policy `π` [AKY20, Lemma 10], with
the variances under the transitions `P` of `M`. If a function `u` within `ε` of the value `v'^π` of
`π` in `M'` satisfies `|∫ u dP q - ∫ u dP' q| ≤ a √(Var_{P q}(u)) + b`, the simulation lemma
expresses `Q^π_M' - Q^π_M` through the resolvent of `P^π_SA` in `M`, the standard deviation of `u`
is within `ε + ‖Q^π_M - Q^π_M'‖` of that of `v^π_M`, and the total-variance lemma in `M` applies.
This bounds `‖Q^π_M - Q^π_M'‖` by a constant plus `α ‖Q^π_M - Q^π_M'‖`, with
`α = γ a / (1 - γ)`, so that for `α < 1` it is at most
`γ (a C √(2 / (1 - γ) ^ 3) + ((2 + a) ε + b) / (1 - γ)) / (1 - α)`. Applied to an optimal policy
`π'` of `M`, with `u = v'^π'`, and to a policy `π` whose value in `M'` is within `ε` of the optimal
value `v'*` of `M'`, with `u = v'*`, this shows that the near-optimal policies of `M'` are
near-optimal in `M` [AKY20, Lemma 2]. This is the deterministic part of the analysis of the
plug-in policy of a generative model.

## Main statements

* `Learning.MDP.qValue_sub_qValue`: **the simulation lemma** [AJKS, Lemma 2.2] with a reward
  error [KS02], `Q^π_M - Q^π_M' = R_γ(P'^π_SA) ((r - r') + γ (P - P') v^π_M)`.
* `Learning.MDP.abs_value_sub_value_le_of_abs_qValue_sub_qValue_le`: a bound on the differences
  of the action values of `π` at `s`, uniform in the action, bounds the difference of its values
  at `s`.
* `Learning.MDP.abs_qValue_sub_qValue_le`, `Learning.MDP.abs_value_sub_value_le`: if
  `|r - r'| ≤ δ` and `|(P - P') v^π_M| ≤ ε`, the action values and the values of `π` in the two
  models differ by at most `δ / (1 - γ) + γ ε / (1 - γ)`.
* `Learning.MDP.optQValue_sub_optQValue_le`, `Learning.MDP.le_optQValue_sub_optQValue`:
  **the componentwise bounds** [AJKS, Lemma 2.5] on `Q*_M - Q*_M'`, with a reward error.
* `Learning.MDP.abs_optQValue_sub_optQValue_le`, `Learning.MDP.abs_optValue_sub_optValue_le`: if
  `|r - r'| ≤ δ` and `|(P - P') v*| ≤ ε`, the optimal action values and the optimal values of the
  two models differ by at most `δ / (1 - γ) + γ ε / (1 - γ)`.
* `Learning.MDP.abs_qValue_sub_qValue_le_of_tvDist_le`,
  `Learning.MDP.abs_value_sub_value_le_of_tvDist_le`,
  `Learning.MDP.abs_optQValue_sub_optQValue_le_of_tvDist_le`,
  `Learning.MDP.abs_optValue_sub_optValue_le_of_tvDist_le`: if `|r - r'| ≤ δ`, the transition
  kernels are within `η` in total variation and `|r| ≤ C`, these four pairs differ by at most
  `δ / (1 - γ) + γ C η / (1 - γ) ^ 2`.
* `Learning.MDP.abs_optQValue_sub_optQValue_le_of_le_sqrt_variance`: the variance-aware bound on
  the optimal action values [AJKS, §2.4], for two MDPs with the same mean rewards.
* `Learning.MDP.abs_qValue_sub_qValue_le_of_le_sqrt_variance`,
  `Learning.MDP.abs_value_sub_value_le_of_le_sqrt_variance`: the variance-aware bounds on the
  action values and the values of a policy [AKY20, Lemma 10].
* `Learning.MDP.optQValue_sub_qValue_le_of_le_sqrt_variance`,
  `Learning.MDP.optValue_sub_value_le_of_le_sqrt_variance`: the near-optimal policies of `M'` are
  near-optimal in `M` [AKY20, Lemmas 2 and 10].

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemmas 2.2 and 2.5 and §2.4
* [A. Agarwal, S. Kakade and L. F. Yang, *Model-based reinforcement learning with a generative
  model is minimax optimal*, COLT 2020][AKY20], Lemmas 2 and 10
* [M. Kearns and S. Singh, *Near-optimal reinforcement learning in polynomial time*, Machine
  Learning 49, 2002][KS02]
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M M' : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] {C C' δ ε : ℝ}

/-- **The simulation lemma** [AJKS, Lemma 2.2], with a reward error [KS02]: for two MDPs `M` and
`M'` with bounded rewards, `γ < 1` and a stationary policy `π`, the action values of `π` differ by
the resolvent of the state-action kernel of `π` in `M'` applied to the difference of the mean
rewards plus the discounted one-step difference of the transition kernels acting on the value of
`π` in `M`: `Q^π_M - Q^π_M' = R_γ(P'^π_SA) ((r - r') + γ (P - P') v^π_M)`. -/
theorem qValue_sub_qValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (p : 𝓢 × 𝓐) :
    M.qValue γ π p - M'.qValue γ π p =
      ∫ q, (meanReward M.R q - meanReward M'.R q +
        γ * (∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q)))
        ∂(Kernel.resolvent γ (M'.saKernel π) p) := by
  have h := Kernel.integral_resolvent_sub_integral_resolvent (κ := M.saKernel π) (M'.saKernel π)
    hγ (measurable_meanReward M.R) (abs_meanReward_le hR) (measurable_meanReward M'.R)
    (abs_meanReward_le hR') p
  simpa only [← qValue_eq_integral_resolvent hγ hR, ← qValue_eq_integral_resolvent hγ hR',
    integral_qValue_saKernel _ hγ hR] using h

/-- For two MDPs `M` and `M'` with bounded rewards, `γ < 1` and a stationary policy `π`, if the
action values of `π` at a state `s` differ by at most `B` for every action, then so do its values
at `s`. -/
theorem abs_value_sub_value_le_of_abs_qValue_sub_qValue_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') {s : 𝓢} {B : ℝ}
    (h : ∀ a, |M.qValue γ π (s, a) - M'.qValue γ π (s, a)| ≤ B) :
    |M.value γ π s - M'.value γ π s| ≤ B := by
  rw [← integral_qValue hγ hR, ← integral_qValue hγ hR',
    ← integral_sub (integrable_qValue_prodMk_left hγ hR s _)
      (integrable_qValue_prodMk_left hγ hR' s _)]
  exact abs_integral_le_of_abs_le h

/-- **The simulation bound**, with a reward error: for two MDPs `M` and `M'` with bounded
rewards, `γ < 1` and a stationary policy `π`, if the mean rewards differ by at most `δ` and the
one-step predictions of the value of `π` in `M` differ by at most `ε`,
`|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε`, then the action values of `π` differ by at most
`δ / (1 - γ) + γ ε / (1 - γ)`. -/
theorem abs_qValue_sub_qValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ)
    (hε : ∀ q, |∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q)| ≤ ε)
    (p : 𝓢 × 𝓐) :
    |M.qValue γ π p - M'.qValue γ π p| ≤ δ / (1 - γ) + γ * ε / (1 - γ) := by
  rw [qValue_sub_qValue hγ hR hR']
  exact Kernel.abs_integral_resolvent_add_mul_le hγ hδ hε p

/-- For two MDPs `M` and `M'` with bounded rewards, `γ < 1` and a stationary policy `π`, if the
mean rewards differ by at most `δ` and the one-step predictions of the value of `π` in `M` differ
by at most `ε`, `|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε`, then the values of `π` differ by at
most `δ / (1 - γ) + γ ε / (1 - γ)`. -/
theorem abs_value_sub_value_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ)
    (hε : ∀ q, |∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q)| ≤ ε) (s : 𝓢) :
    |M.value γ π s - M'.value γ π s| ≤ δ / (1 - γ) + γ * ε / (1 - γ) :=
  abs_value_sub_value_le_of_abs_qValue_sub_qValue_le hγ hR hR' fun a ↦
    abs_qValue_sub_qValue_le hγ hR hR' hδ hε (s, a)

/-! ### Bounds in total variation -/

/-- If the transition kernels of `M` and `M'` are within `η` in total variation, the one-step
predictions of a measurable function bounded by `B` differ by at most `B * η`. -/
private lemma abs_integral_sub_integral_le_of_tvDist_le {v : 𝓢 → ℝ} {B η : ℝ}
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η)
    (q : 𝓢 × 𝓐) :
    |∫ s, v s ∂(M.P q) - ∫ s, v s ∂(M'.P q)| ≤ B * η :=
  (norm_integral_sub_integral_le_mul_tvDist hv.aestronglyMeasurable hv.aestronglyMeasurable
    (.of_forall hvB) (.of_forall hvB)).trans
    (mul_le_mul_of_nonneg_left (hη q) ((abs_nonneg _).trans (hvB q.1)))

/-- **The simulation bound in total variation**, a consequence of the simulation lemma
[AJKS, Lemma 2.2]: for two MDPs `M` and `M'` with bounded rewards, `|r| ≤ C` for `M`, `γ < 1` and
a stationary policy `π`, if the mean rewards differ by at most `δ` and the transition kernels are
within `η` in total variation, `tvDist (P (s, a)) (P' (s, a)) ≤ η`, then the action values of `π`
differ by at most `δ / (1 - γ) + γ C η / (1 - γ) ^ 2`. -/
theorem abs_qValue_sub_qValue_le_of_tvDist_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ)
    {η : ℝ} (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (p : 𝓢 × 𝓐) :
    |M.qValue γ π p - M'.qValue γ π p| ≤ δ / (1 - γ) + γ * C * η / (1 - γ) ^ 2 :=
  (abs_qValue_sub_qValue_le hγ hR hR' hδ (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_value hγ hR) (abs_value_le hγ hR) hη) p).trans_eq (by rw [sq, ← div_div]; ring)

/-- **The simulation bound in total variation**, for values: for two MDPs `M` and `M'` with
bounded rewards, `|r| ≤ C` for `M`, `γ < 1` and a stationary policy `π`, if the mean rewards
differ by at most `δ` and the transition kernels are within `η` in total variation, then the
values of `π` differ by at most `δ / (1 - γ) + γ C η / (1 - γ) ^ 2`. -/
theorem abs_value_sub_value_le_of_tvDist_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ)
    {η : ℝ} (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (s : 𝓢) :
    |M.value γ π s - M'.value γ π s| ≤ δ / (1 - γ) + γ * C * η / (1 - γ) ^ 2 :=
  (abs_value_sub_value_le hγ hR hR' hδ (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_value hγ hR) (abs_value_le hγ hR) hη) s).trans_eq (by rw [sq, ← div_div]; ring)

/-! ### Componentwise bounds on the optimal action values -/

section Optimal

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐] {π' : Kernel 𝓢 𝓐} [IsMarkovKernel π']

/-- **Componentwise upper bound** [AJKS, Lemma 2.5], with a reward error: for two MDPs `M` and
`M'` with finitely many actions, bounded rewards and `γ < 1`, and an optimal stationary policy `π`
of `M`, the optimal action values satisfy
`Q*_M - Q*_M' ≤ R_γ(P'^π_SA) ((r - r') + γ (P - P') v*_M)`. -/
theorem optQValue_sub_optQValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hπ : M.value γ π = M.optValue γ) (p : 𝓢 × 𝓐) :
    M.optQValue γ p - M'.optQValue γ p ≤
      ∫ q, (meanReward M.R q - meanReward M'.R q +
        γ * (∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)))
        ∂(Kernel.resolvent γ (M'.saKernel π) p) := by
  rw [← hπ, ← qValue_eq_optQValue hπ, ← qValue_sub_qValue hγ hR hR' p]
  exact sub_le_sub_left (qValue_le_optQValue hγ hR' p) _

/-- **Componentwise lower bound** [AJKS, Lemma 2.5], with a reward error: for two MDPs `M` and
`M'` with finitely many actions, bounded rewards and `γ < 1`, and an optimal stationary policy
`π'` of `M'`, the optimal action values satisfy
`R_γ(P'^π'_SA) ((r - r') + γ (P - P') v*_M) ≤ Q*_M - Q*_M'`. -/
theorem le_optQValue_sub_optQValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hπ' : M'.value γ π' = M'.optValue γ) (p : 𝓢 × 𝓐) :
    ∫ q, (meanReward M.R q - meanReward M'.R q +
        γ * (∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)))
        ∂(Kernel.resolvent γ (M'.saKernel π') p) ≤
      M.optQValue γ p - M'.optQValue γ p := by
  have hv := measurable_optValue hγ hR
  have hvB := abs_optValue_le hγ hR
  have hQ := measurable_optQValue hγ hR
  have hQ' := measurable_optQValue hγ hR'
  -- `Q*_M - Q*_M'` is a supersolution of the resolvent equation
  -- `u = (r - r') + γ (P - P') v* + γ P'^π'_SA u`
  refine Kernel.integral_resolvent_le_of_add_le hγ
    (B := C + C' + γ * (C / (1 - γ) + C / (1 - γ)))
    (u := fun q ↦ M.optQValue γ q - M'.optQValue γ q)
    (((measurable_meanReward M.R).sub (measurable_meanReward M'.R)).add
      (((hv.stronglyMeasurable.integral_kernel (κ := M.P)).measurable.sub
        (hv.stronglyMeasurable.integral_kernel (κ := M'.P)).measurable).const_mul _))
    (fun q ↦ ?_) (hQ.sub hQ')
    (fun q ↦ (abs_sub _ _).trans
      (add_le_add (abs_optQValue_le hγ hR q) (abs_optQValue_le hγ hR' q)))
    (fun q ↦ ?_) p
  · refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
      (add_le_add (abs_meanReward_le hR q) (abs_meanReward_le hR' q))) ?_)
    rw [abs_mul, NNReal.abs_eq]
    gcongr
    exact (abs_sub _ _).trans
      (add_le_add (abs_integral_le_of_abs_le hvB) (abs_integral_le_of_abs_le hvB))
  have hint := integrable_of_abs_le hQ (abs_optQValue_le hγ hR) (M'.saKernel π' q)
  have hint' := integrable_of_abs_le hQ' (abs_optQValue_le hγ hR') (M'.saKernel π' q)
  -- `π'` is suboptimal in `M`: `P'^π'_SA Q*_M ≤ P' v*_M`
  have h₁ := integral_optQValue_saKernel_le (π := π') M' hγ hR q
  -- `π'` is optimal in `M'`: `P'^π'_SA Q*_M' = P' v*_M'`
  have h₂ : ∫ w, M'.optQValue γ w ∂(M'.saKernel π' q) = ∫ s, M'.optValue γ s ∂(M'.P q) := by
    rw [← qValue_eq_optQValue hπ', integral_qValue_saKernel M' hγ hR' q, hπ']
  have h₃ := mul_le_mul_of_nonneg_left h₁ γ.coe_nonneg
  rw [integral_sub hint hint', h₂, optQValue_def M γ q, optQValue_def M' γ q]
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

/-- For two MDPs `M` and `M'` with finitely many actions, bounded rewards and `γ < 1`, if the mean
rewards differ by at most `δ` and the one-step predictions of the optimal value `v*` of `M` differ
by at most `ε`, `|∫ v* dP (s, a) - ∫ v* dP' (s, a)| ≤ ε`, then the optimal action values of the two
MDPs differ by at most `δ / (1 - γ) + γ ε / (1 - γ)`. -/
theorem abs_optQValue_sub_optQValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ)
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤ ε)
    (p : 𝓢 × 𝓐) :
    |M.optQValue γ p - M'.optQValue γ p| ≤ δ / (1 - γ) + γ * ε / (1 - γ) := by
  have := Fintype.ofFinite 𝓐
  have hb (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] :=
    Kernel.abs_integral_resolvent_add_mul_le (κ := M'.saKernel π) hγ hδ hε p
  -- the greedy policies for the optimal values are optimal stationary policies
  have hg := measurable_greedy (M := M) (γ := γ) (measurable_optValue hγ hR)
  have hg' := measurable_greedy (M := M') (γ := γ) (measurable_optValue hγ hR')
  exact abs_le.2 ⟨(neg_le_of_abs_le (hb _)).trans
    (le_optQValue_sub_optQValue hγ hR hR' (value_greedy_optValue hγ hR' hg') p),
    (optQValue_sub_optQValue_le hγ hR hR' (value_greedy_optValue hγ hR hg) p).trans
      (le_of_abs_le (hb _))⟩

/-- For two MDPs `M` and `M'` with finitely many actions, bounded rewards and `γ < 1`, if the mean
rewards differ by at most `δ` and the one-step predictions of the optimal value `v*` of `M` differ
by at most `ε`, `|∫ v* dP (s, a) - ∫ v* dP' (s, a)| ≤ ε`, then the optimal values of the two MDPs
differ by at most `δ / (1 - γ) + γ ε / (1 - γ)`. -/
theorem abs_optValue_sub_optValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ)
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤ ε) (s : 𝓢) :
    |M.optValue γ s - M'.optValue γ s| ≤ δ / (1 - γ) + γ * ε / (1 - γ) := by
  have h a := abs_le.1 (abs_optQValue_sub_optQValue_le hγ hR hR' hδ hε (s, a))
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · rw [sub_le_iff_le_add, ← iSup_optQValue hγ hR s]
    exact ciSup_le fun a ↦ by linarith [(h a).2, optQValue_le_optValue hγ hR' s a]
  · rw [sub_le_iff_le_add, ← iSup_optQValue hγ hR' s]
    exact ciSup_le fun a ↦ by linarith [(h a).1, optQValue_le_optValue hγ hR s a]

/-- **The simulation bound in total variation**, for optimal action values: for two MDPs `M` and
`M'` with finitely many actions, bounded rewards, `|r| ≤ C` for `M`, and `γ < 1`, if the mean
rewards differ by at most `δ` and the transition kernels are within `η` in total variation, then
the optimal action values of the two MDPs differ by at most `δ / (1 - γ) + γ C η / (1 - γ) ^ 2`. -/
theorem abs_optQValue_sub_optQValue_le_of_tvDist_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ) {η : ℝ}
    (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (p : 𝓢 × 𝓐) :
    |M.optQValue γ p - M'.optQValue γ p| ≤ δ / (1 - γ) + γ * C * η / (1 - γ) ^ 2 :=
  (abs_optQValue_sub_optQValue_le hγ hR hR' hδ (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_optValue hγ hR) (abs_optValue_le hγ hR) hη) p).trans_eq
    (by rw [sq, ← div_div]; ring)

/-- **The simulation bound in total variation**, for optimal values: for two MDPs `M` and `M'`
with finitely many actions, bounded rewards, `|r| ≤ C` for `M`, and `γ < 1`, if the mean rewards
differ by at most `δ` and the transition kernels are within `η` in total variation, then the
optimal values of the two MDPs differ by at most `δ / (1 - γ) + γ C η / (1 - γ) ^ 2`. -/
theorem abs_optValue_sub_optValue_le_of_tvDist_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hδ : ∀ q, |meanReward M.R q - meanReward M'.R q| ≤ δ) {η : ℝ}
    (hη : ∀ q, tvDist (M.P q) (M'.P q) ≤ η) (s : 𝓢) :
    |M.optValue γ s - M'.optValue γ s| ≤ δ / (1 - γ) + γ * C * η / (1 - γ) ^ 2 :=
  (abs_optValue_sub_optValue_le hγ hR hR' hδ (abs_integral_sub_integral_le_of_tvDist_le
    (measurable_optValue hγ hR) (abs_optValue_le hγ hR) hη) s).trans_eq
    (by rw [sq, ← div_div]; ring)

end Optimal

/-! ### Variance-aware accuracy of the action values of a policy -/

section PolicyVarianceAware

variable {a b : ℝ}

/-- The resolvent step of the variance-aware bounds: for an MDP `M` with rewards bounded by `C`,
`γ < 1` and a stationary policy `π`, if a function `g` satisfies
`|g q| ≤ a √(Var_{P q}(v^π)) + c` at every pair `q`, with `a ≥ 0`, then the resolvent of the
state-action kernel of `π` maps `g` to at most `a C √(2 / (1 - γ) ^ 3) + c / (1 - γ)`, by the
total-variance lemma. -/
private lemma abs_integral_resolvent_le_of_abs_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (ha : 0 ≤ a) {g : 𝓢 × 𝓐 → ℝ} {c : ℝ}
    (hg : ∀ q, |g q| ≤ a * √(Var[M.value γ π; M.P q]) + c) (p : 𝓢 × 𝓐) :
    |∫ q, g q ∂(Kernel.resolvent γ (M.saKernel π) p)| ≤
      a * C * √(2 / (1 - γ) ^ 3) + c / (1 - γ) := by
  have := Kernel.isFiniteKernel_resolvent (κ := M.saKernel π) hγ
  have hB : 0 ≤ C / (1 - γ) := (abs_nonneg _).trans (abs_value_le (π := π) hγ hR p.1)
  have hv := measurable_value (π := π) hγ hR
  have hvB := abs_value_le (π := π) hγ hR
  set ρ := Kernel.resolvent γ (M.saKernel π) p
  -- the standard deviation `σ` of `v^π` under `P` is bounded by `C / (1 - γ)`
  set σ : 𝓢 × 𝓐 → ℝ := fun q ↦ √(Var[M.value γ π; M.P q])
  have hσ : Measurable σ := (hv.variance_kernel (η := M.P)).sqrt
  have hσB (q : 𝓢 × 𝓐) : |σ q| ≤ C / (1 - γ) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_left hB]
    exact variance_le_sq_of_abs_le hv.aemeasurable (.of_forall hvB)
  have hσi := (integrable_of_abs_le hσ hσB ρ).const_mul a
  have h_int : ∫ q, σ q ∂ρ ≤ C * √(2 / (1 - γ) ^ 3) :=
    integral_sqrt_variance_value_resolvent_le hγ hR p
  calc |∫ q, g q ∂ρ| ≤ ∫ q, |g q| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ q, (a * σ q + c) ∂ρ := integral_mono_of_nonneg (.of_forall fun _ ↦ abs_nonneg _)
        (hσi.add (integrable_const _)) (.of_forall hg)
    _ = a * ∫ q, σ q ∂ρ + c / (1 - γ) := by
        rw [integral_add hσi (integrable_const _), integral_const_mul, integral_const, smul_eq_mul,
          Kernel.measureReal_resolvent_univ hγ, inv_mul_eq_div]
    _ ≤ a * (C * √(2 / (1 - γ) ^ 3)) + c / (1 - γ) := by gcongr
    _ = a * C * √(2 / (1 - γ) ^ 3) + c / (1 - γ) := by ring

/-- **Variance-aware accuracy of the action values of a policy** [AKY20, Lemma 10]: for two MDPs
`M` and `M'` with the same mean rewards, bounded rewards, rewards of `M` bounded by `C`, `γ < 1`
and a stationary policy `π`, let `u` be a measurable function within `ε` of the value `v'^π` of `π`
in `M'` whose one-step predictions satisfy the Bernstein-type bound
`|∫ u dP q - ∫ u dP' q| ≤ a √(Var_{P q}(u)) + b`, with the variance under the transitions `P` of
`M`, at every pair `q`. If `α = γ a / (1 - γ) < 1`, the action values of `π` in the two MDPs
differ by at most `γ (a C √(2 / (1 - γ) ^ 3) + ((2 + a) ε + b) / (1 - γ)) / (1 - α)`.

[AKY20] applies this with `u = v'^π` and `ε = 0`, for a policy `π` that does not depend on `M'`,
and with `u` the optimal value of `M'`, for a policy `π` whose value in `M'` is `ε`-optimal. -/
theorem abs_qValue_sub_qValue_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a) (hα : γ * a / (1 - γ) < 1)
    {u : 𝓢 → ℝ} (hu : Measurable u) (hπu : ∀ s, |M'.value γ π s - u s| ≤ ε)
    (hε : ∀ q, |∫ s, u s ∂(M.P q) - ∫ s, u s ∂(M'.P q)| ≤ a * √(Var[u; M.P q]) + b)
    (p : 𝓢 × 𝓐) :
    |M.qValue γ π p - M'.qValue γ π p| ≤
      γ * (a * C * √(2 / (1 - γ) ^ 3) + ((2 + a) * ε + b) / (1 - γ)) /
        (1 - γ * a / (1 - γ)) := by
  have : Nonempty (𝓢 × 𝓐) := ⟨p⟩
  have hv := measurable_value (π := π) hγ hR
  have hvB := abs_value_le (π := π) hγ hR
  have hv' := measurable_value (π := π) hγ hR'
  have hvB' := abs_value_le (π := π) hγ hR'
  have huB (s : 𝓢) : |u s| ≤ C' / (1 - γ) + ε := by
    have h₁ := abs_le.1 (hπu s)
    have h₂ := abs_le.1 (hvB' s)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hmem {f : 𝓢 → ℝ} {B' : ℝ} (hf : Measurable f) (hfB : ∀ s, |f s| ≤ B') (q : 𝓢 × 𝓐) :
      MemLp f 2 (M.P q) :=
    MemLp.of_bound hf.aestronglyMeasurable _
      (.of_forall fun s ↦ (Real.norm_eq_abs _).trans_le (hfB s))
  -- the largest error `Δ` of the action values, which bounds the error of the values
  set x : 𝓢 × 𝓐 → ℝ := fun q ↦ |M.qValue γ π q - M'.qValue γ π q|
  have hxB : BddAbove (Set.range x) := ⟨C / (1 - γ) + C' / (1 - γ), Set.forall_mem_range.2
    fun q ↦ (abs_sub _ _).trans (add_le_add (abs_qValue_le hγ hR q) (abs_qValue_le hγ hR' q))⟩
  set Δ := ⨆ q, x q
  have hxΔ (q : 𝓢 × 𝓐) : x q ≤ Δ := le_ciSup hxB q
  have hvΔ (s : 𝓢) : |M'.value γ π s - M.value γ π s| ≤ Δ :=
    abs_value_sub_value_le_of_abs_qValue_sub_qValue_le hγ hR' hR fun a ↦
      (abs_sub_comm _ _).trans_le (hxΔ (s, a))
  -- pointwise, the one-step error `(P' - P) v'^π` is at most `a σ + (a Δ + (2 + a) ε + b)`, with
  -- `σ` the standard deviation of `v^π` under `P`
  have h_pt (q : 𝓢 × 𝓐) :
      |∫ s, M'.value γ π s ∂(M'.P q) - ∫ s, M'.value γ π s ∂(M.P q)| ≤
        a * √(Var[M.value γ π; M.P q]) + (a * Δ + ((2 + a) * ε + b)) := by
    have h := abs_integral_sub_integral_le_of_abs_sub_le (hmem hv' hvB' q) (hmem hu huB q)
      (integrable_of_abs_le hv' hvB' _) (integrable_of_abs_le hu huB _) ha hπu (hε q)
    have h_sd := sqrt_variance_le_sqrt_variance_add_of_abs_sub_le (hmem hv' hvB' q)
      (hmem hv hvB q) (.of_forall hvΔ)
    calc _ ≤ a * √Var[M'.value γ π; M.P q] + (2 + a) * ε + b := (abs_sub_comm _ _).trans_le h
      _ ≤ a * (√(Var[M.value γ π; M.P q]) + Δ) + (2 + a) * ε + b := by gcongr
      _ = a * √(Var[M.value γ π; M.P q]) + (a * Δ + ((2 + a) * ε + b)) := by ring
  -- every action value error is at most `K + α Δ`, by the simulation lemma and the
  -- total-variance lemma
  have h_step (q : 𝓢 × 𝓐) : x q ≤ γ * (a * C * √(2 / (1 - γ) ^ 3) + ((2 + a) * ε + b) /
      (1 - γ)) + γ * a / (1 - γ) * Δ := by
    simp only [x]
    rw [abs_sub_comm, qValue_sub_qValue hγ hR' hR q]
    simp only [hr, sub_self, zero_add]
    rw [integral_const_mul, abs_mul, NNReal.abs_eq]
    calc _ ≤ (γ : ℝ) * (a * C * √(2 / (1 - γ) ^ 3) + (a * Δ + ((2 + a) * ε + b)) / (1 - γ)) := by
          gcongr
          exact abs_integral_resolvent_le_of_abs_le_sqrt_variance hγ hR ha h_pt q
      _ = γ * (a * C * √(2 / (1 - γ) ^ 3) + ((2 + a) * ε + b) / (1 - γ)) +
          γ * a / (1 - γ) * Δ := by ring
  -- hence `Δ ≤ K + α Δ`, that is `Δ ≤ K / (1 - α)`
  have hΔ := ciSup_le h_step
  refine (hxΔ p).trans ?_
  rw [le_div_iff₀ (sub_pos.2 hα)]
  linarith

/-- **Variance-aware accuracy of the values of a policy** [AKY20, Lemma 10]: under the hypotheses
of `Learning.MDP.abs_qValue_sub_qValue_le_of_le_sqrt_variance`, the values of `π` in the two MDPs
differ by at most `γ (a C √(2 / (1 - γ) ^ 3) + ((2 + a) ε + b) / (1 - γ)) / (1 - α)`. -/
theorem abs_value_sub_value_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a) (hα : γ * a / (1 - γ) < 1)
    {u : 𝓢 → ℝ} (hu : Measurable u) (hπu : ∀ s, |M'.value γ π s - u s| ≤ ε)
    (hε : ∀ q, |∫ s, u s ∂(M.P q) - ∫ s, u s ∂(M'.P q)| ≤ a * √(Var[u; M.P q]) + b) (s : 𝓢) :
    |M.value γ π s - M'.value γ π s| ≤
      γ * (a * C * √(2 / (1 - γ) ^ 3) + ((2 + a) * ε + b) / (1 - γ)) /
        (1 - γ * a / (1 - γ)) :=
  abs_value_sub_value_le_of_abs_qValue_sub_qValue_le hγ hR hR' fun a ↦
    abs_qValue_sub_qValue_le_of_le_sqrt_variance hγ hR hR' hr ha hα hu hπu hε (s, a)

end PolicyVarianceAware

section VarianceAware

variable [Nonempty 𝓢] [Nonempty 𝓐] [Finite 𝓐] {a b : ℝ}

/-- For two MDPs with the same mean rewards and a one-step error of the optimal value `v*` of `M`
bounded by `a √(Var_{P' q}(v*)) + b`, the resolvent of the state-action kernel in `M'` of a
stationary policy `π` whose value in `M'` is within `D` of `v*` maps the right-hand side of the
componentwise bounds to at most `γ (a C √(2 / (1 - γ) ^ 3) + (a D + b) / (1 - γ))`. -/
private lemma abs_integral_resolvent_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C)
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a)
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤
      a * √(Var[M.optValue γ; M'.P q]) + b)
    (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] {D : ℝ}
    (hD : ∀ s, |M.optValue γ s - M'.value γ π s| ≤ D) (p : 𝓢 × 𝓐) :
    |∫ q, (meanReward M.R q - meanReward M'.R q +
        γ * (∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)))
        ∂(Kernel.resolvent γ (M'.saKernel π) p)| ≤
      γ * (a * C * √(2 / (1 - γ) ^ 3) + (a * D + b) / (1 - γ)) := by
  have hv := measurable_optValue hγ hR
  have hvB := abs_optValue_le hγ hR
  have hv' := measurable_value (π := π) hγ hR'
  have hvB' := abs_value_le (π := π) hγ hR'
  -- pointwise, the one-step error `(P - P') v*` is at most `a σ + (a D + b)`, with `σ` the
  -- standard deviation of `v^π_M'` under `P'`: the standard deviations of `v*` and `v^π_M'` are
  -- within `D`
  have h_pt (q : 𝓢 × 𝓐) :
      |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤
        a * √(Var[M'.value γ π; M'.P q]) + (a * D + b) := by
    have hmem {f : 𝓢 → ℝ} (hf : Measurable f) (hfB : ∀ s, |f s| ≤ C / (1 - γ)) :
        MemLp f 2 (M'.P q) :=
      MemLp.of_bound hf.aestronglyMeasurable _
        (.of_forall fun s ↦ (Real.norm_eq_abs _).trans_le (hfB s))
    have h_sd := sqrt_variance_le_sqrt_variance_add_of_abs_sub_le (hmem hv hvB) (hmem hv' hvB')
      (.of_forall hD)
    calc _ ≤ a * √(Var[M.optValue γ; M'.P q]) + b := hε q
      _ ≤ a * (√(Var[M'.value γ π; M'.P q]) + D) + b := by gcongr
      _ = a * √(Var[M'.value γ π; M'.P q]) + (a * D + b) := by ring
  simp only [hr, sub_self, zero_add]
  rw [integral_const_mul, abs_mul, NNReal.abs_eq]
  gcongr
  exact abs_integral_resolvent_le_of_abs_le_sqrt_variance hγ hR' ha h_pt p

/-- **Variance-aware accuracy of the optimal action values** [AJKS, §2.4]: for two MDPs `M` and
`M'` with finitely many actions, the same mean rewards, rewards bounded by `C` and `γ < 1`, if the
one-step predictions of the optimal value `v*` of `M` satisfy, for some `a ≥ 0` and `b`, the
Bernstein-type bound `|∫ v* dP q - ∫ v* dP' q| ≤ a √(Var_{P' q}(v*)) + b` at every pair `q`, then
the optimal action values satisfy
`|Q*_M - Q*_M'| ≤ γ (a C √(2 / (1 - γ) ^ 3) + (a D + b) / (1 - γ))`, with
`D = γ (a C / (1 - γ) + b) / (1 - γ)`. For a small `a`, the leading term `γ a C √(2 / (1 - γ) ^ 3)`
is smaller by the factor `√(1 - γ)` than the bound `γ a C / (1 - γ) ^ 2` obtained from the
uniform bound `√(Var_{P' q}(v*)) ≤ C / (1 - γ)`. -/
theorem abs_optQValue_sub_optQValue_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C)
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a)
    (hε : ∀ q, |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤
      a * √(Var[M.optValue γ; M'.P q]) + b) (p : 𝓢 × 𝓐) :
    |M.optQValue γ p - M'.optQValue γ p| ≤ γ * (a * C * √(2 / (1 - γ) ^ 3) +
      (a * (γ * (a * (C / (1 - γ)) + b) / (1 - γ)) + b) / (1 - γ)) := by
  have := Fintype.ofFinite 𝓐
  have hv := measurable_optValue hγ hR
  have hvB := abs_optValue_le hγ hR
  have hB : 0 ≤ C / (1 - γ) := (abs_nonneg _).trans (hvB (Classical.arbitrary 𝓢))
  have hδ (q : 𝓢 × 𝓐) : |meanReward M.R q - meanReward M'.R q| ≤ 0 := by simp [hr]
  -- the uniform bound on the one-step error, from `√(Var_{P' q}(v*)) ≤ C / (1 - γ)`
  have hε' (q : 𝓢 × 𝓐) : |∫ s, M.optValue γ s ∂(M.P q) - ∫ s, M.optValue γ s ∂(M'.P q)| ≤
      a * (C / (1 - γ)) + b := by
    refine (hε q).trans ?_
    gcongr
    rw [Real.sqrt_le_left hB]
    exact variance_le_sq_of_abs_le hv.aemeasurable (.of_forall hvB)
  -- the greedy policies for the optimal values are optimal stationary policies
  have hg := measurable_greedy (M := M) (γ := γ) hv
  have hg' := measurable_greedy (M := M') (γ := γ) (measurable_optValue hγ hR')
  have hπ := value_greedy_optValue hγ hR hg
  have hπ' := value_greedy_optValue hγ hR' hg'
  -- their values in `M'` are within `D` of `v*`, by the simulation bounds
  have hD (s : 𝓢) : |M.optValue γ s - M'.value γ (Kernel.deterministic _ hg) s| ≤
      γ * (a * (C / (1 - γ)) + b) / (1 - γ) := by
    have h := abs_value_sub_value_le (π := Kernel.deterministic _ hg) hγ hR hR' hδ
      (fun q ↦ by rw [hπ]; exact hε' q) s
    rwa [hπ, zero_div, zero_add] at h
  have hD' (s : 𝓢) : |M.optValue γ s - M'.value γ (Kernel.deterministic _ hg') s| ≤
      γ * (a * (C / (1 - γ)) + b) / (1 - γ) := by
    have h := abs_optValue_sub_optValue_le hγ hR hR' hδ hε' s
    rwa [← hπ', zero_div, zero_add] at h
  have h₁ := abs_integral_resolvent_le_of_le_sqrt_variance hγ hR hR' hr ha hε _ hD p
  have h₂ := abs_integral_resolvent_le_of_le_sqrt_variance hγ hR hR' hr ha hε _ hD' p
  exact abs_le.2 ⟨(neg_le_of_abs_le h₂).trans (le_optQValue_sub_optQValue hγ hR hR' hπ' p),
    (optQValue_sub_optQValue_le hγ hR hR' hπ p).trans (le_of_abs_le h₁)⟩

/-- The common bound of `Learning.MDP.optQValue_sub_qValue_le_of_le_sqrt_variance` and
`Learning.MDP.optValue_sub_value_le_of_le_sqrt_variance`: the action values and the values of
`π` and of an optimal policy `π'` of `M` are accurate in `M'`. -/
private lemma abs_qValue_sub_qValue_add_abs_qValue_sub_qValue_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a) (hα : γ * a / (1 - γ) < 1)
    {π' : Kernel 𝓢 𝓐} [IsMarkovKernel π']
    (hε' : ∀ q, |∫ s, M'.value γ π' s ∂(M.P q) - ∫ s, M'.value γ π' s ∂(M'.P q)| ≤
      a * √(Var[M'.value γ π'; M.P q]) + b)
    (hε : ∀ q, |∫ s, M'.optValue γ s ∂(M.P q) - ∫ s, M'.optValue γ s ∂(M'.P q)| ≤
      a * √(Var[M'.optValue γ; M.P q]) + b)
    (hπ : ∀ s, |M'.value γ π s - M'.optValue γ s| ≤ ε) :
    (∀ p, |M.qValue γ π' p - M'.qValue γ π' p| + |M'.qValue γ π p - M.qValue γ π p| ≤
      (2 * γ * (a * C * √(2 / (1 - γ) ^ 3) + b / (1 - γ)) + γ * (2 + a) * ε / (1 - γ)) /
        (1 - γ * a / (1 - γ))) ∧
    ∀ s, |M.value γ π' s - M'.value γ π' s| + |M'.value γ π s - M.value γ π s| ≤
      (2 * γ * (a * C * √(2 / (1 - γ) ^ 3) + b / (1 - γ)) + γ * (2 + a) * ε / (1 - γ)) /
        (1 - γ * a / (1 - γ)) := by
  have hv' := measurable_value (π := π') hγ hR'
  have h₀ (s : 𝓢) : |M'.value γ π' s - M'.value γ π' s| ≤ 0 := by simp
  have hu := measurable_optValue hγ hR'
  have he : γ * (a * C * √(2 / (1 - γ) ^ 3) + ((2 + a) * 0 + b) / (1 - γ)) /
        (1 - γ * a / (1 - γ)) +
      γ * (a * C * √(2 / (1 - γ) ^ 3) + ((2 + a) * ε + b) / (1 - γ)) / (1 - γ * a / (1 - γ)) =
      (2 * γ * (a * C * √(2 / (1 - γ) ^ 3) + b / (1 - γ)) + γ * (2 + a) * ε / (1 - γ)) /
        (1 - γ * a / (1 - γ)) := by
    ring
  refine ⟨fun p ↦ ?_, fun s ↦ ?_⟩
  · rw [abs_sub_comm (M'.qValue γ π p), ← he]
    exact add_le_add
      (abs_qValue_sub_qValue_le_of_le_sqrt_variance hγ hR hR' hr ha hα hv' h₀ hε' p)
      (abs_qValue_sub_qValue_le_of_le_sqrt_variance hγ hR hR' hr ha hα hu hπ hε p)
  · rw [abs_sub_comm (M'.value γ π s), ← he]
    exact add_le_add
      (abs_value_sub_value_le_of_le_sqrt_variance hγ hR hR' hr ha hα hv' h₀ hε' s)
      (abs_value_sub_value_le_of_le_sqrt_variance hγ hR hR' hr ha hα hu hπ hε s)

/-- **Accuracy of the action values of a near-optimal policy of a model** [AKY20, Lemmas 2 and
10]: for two MDPs `M` and `M'` with finitely many actions, the same mean rewards, bounded rewards,
rewards of `M` bounded by `C` and `γ < 1`, let `π'` be an optimal stationary policy of `M`, and
assume that the values `v'^π'` of `π'` and `v'*` of `M'` satisfy the Bernstein-type bounds
`|∫ v dP q - ∫ v dP' q| ≤ a √(Var_{P q}(v)) + b` at every pair `q`, with the variance under the
transitions `P` of `M`. If `α = γ a / (1 - γ) < 1`, every stationary policy `π` whose value in `M'`
is within `ε` of `v'*` has action values in `M` at least
`Q*_M - (2 γ (a C √(2 / (1 - γ) ^ 3) + b / (1 - γ)) + γ (2 + a) ε / (1 - γ)) / (1 - α) - γ ε`. -/
theorem optQValue_sub_qValue_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a) (hα : γ * a / (1 - γ) < 1)
    {π' : Kernel 𝓢 𝓐} [IsMarkovKernel π'] (hπ' : M.value γ π' = M.optValue γ)
    (hε' : ∀ q, |∫ s, M'.value γ π' s ∂(M.P q) - ∫ s, M'.value γ π' s ∂(M'.P q)| ≤
      a * √(Var[M'.value γ π'; M.P q]) + b)
    (hε : ∀ q, |∫ s, M'.optValue γ s ∂(M.P q) - ∫ s, M'.optValue γ s ∂(M'.P q)| ≤
      a * √(Var[M'.optValue γ; M.P q]) + b)
    (hπ : ∀ s, |M'.value γ π s - M'.optValue γ s| ≤ ε) (p : 𝓢 × 𝓐) :
    M.optQValue γ p - M.qValue γ π p ≤
      (2 * γ * (a * C * √(2 / (1 - γ) ^ 3) + b / (1 - γ)) + γ * (2 + a) * ε / (1 - γ)) /
        (1 - γ * a / (1 - γ)) + γ * ε := by
  have h := (abs_qValue_sub_qValue_add_abs_qValue_sub_qValue_le hγ hR hR' hr ha hα hε' hε hπ).1 p
  -- `π'` is suboptimal in `M'`
  have h₁ := qValue_le_optQValue (π := π') hγ hR' p
  -- the action values of `π` in `M'` are `γ ε`-optimal
  have h₂ := optQValue_sub_qValue_le_of_optValue_sub_value_le hγ hR'
    (fun s ↦ (le_abs_self _).trans ((abs_sub_comm _ _).trans_le (hπ s))) p
  rw [← qValue_eq_optQValue hπ']
  linarith [le_abs_self (M.qValue γ π' p - M'.qValue γ π' p),
    le_abs_self (M'.qValue γ π p - M.qValue γ π p)]

/-- **Accuracy of the values of a near-optimal policy of a model** [AKY20, Lemmas 2 and 10]:
under the hypotheses of `Learning.MDP.optQValue_sub_qValue_le_of_le_sqrt_variance`, every
stationary policy `π` whose value in `M'` is within `ε` of `v'*` has values in `M` at least
`v*_M - (2 γ (a C √(2 / (1 - γ) ^ 3) + b / (1 - γ)) + γ (2 + a) ε / (1 - γ)) / (1 - α) - ε`. -/
theorem optValue_sub_value_le_of_le_sqrt_variance (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hr : meanReward M'.R = meanReward M.R) (ha : 0 ≤ a) (hα : γ * a / (1 - γ) < 1)
    {π' : Kernel 𝓢 𝓐} [IsMarkovKernel π'] (hπ' : M.value γ π' = M.optValue γ)
    (hε' : ∀ q, |∫ s, M'.value γ π' s ∂(M.P q) - ∫ s, M'.value γ π' s ∂(M'.P q)| ≤
      a * √(Var[M'.value γ π'; M.P q]) + b)
    (hε : ∀ q, |∫ s, M'.optValue γ s ∂(M.P q) - ∫ s, M'.optValue γ s ∂(M'.P q)| ≤
      a * √(Var[M'.optValue γ; M.P q]) + b)
    (hπ : ∀ s, |M'.value γ π s - M'.optValue γ s| ≤ ε) (s : 𝓢) :
    M.optValue γ s - M.value γ π s ≤
      (2 * γ * (a * C * √(2 / (1 - γ) ^ 3) + b / (1 - γ)) + γ * (2 + a) * ε / (1 - γ)) /
        (1 - γ * a / (1 - γ)) + ε := by
  have h := (abs_qValue_sub_qValue_add_abs_qValue_sub_qValue_le hγ hR hR' hr ha hα hε' hε hπ).2 s
  have h₁ := value_le_optValue (π := π') hγ hR' s
  rw [← hπ']
  linarith [le_abs_self (M.value γ π' s - M'.value γ π' s),
    le_abs_self (M'.value γ π s - M.value γ π s), neg_le_of_abs_le (hπ s)]

end VarianceAware

end Learning.MDP
