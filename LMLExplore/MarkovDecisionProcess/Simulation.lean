/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Value

/-!
# The simulation lemma

Let `M` and `M'` be two MDPs on the same state and action spaces, with the same mean reward `r`
and transition kernels `P` and `P'`; typically `M'` is a model of `M` estimated from samples of its
transitions. For a stationary policy `π` and `0 ≤ γ < 1`, the action values of `π` in the two
models are the resolvents of their state-action kernels applied to `r`,
`Q^π_M = R_γ(P^π_SA) r` and `Q^π_M' = R_γ(P'^π_SA) r`. The simulation identity for resolvents
(`ProbabilityTheory.Kernel.integral_resolvent_sub_integral_resolvent`) compares them through the
one-step difference of the transition kernels acting on the value of `π` in `M`:

`Q^π_M - Q^π_M' = γ R_γ(P'^π_SA) ((P - P') v^π_M)`.

Since `R_γ(P'^π_SA)` has mass `(1 - γ)⁻¹`, an error of at most `ε` in the one-step predictions
`|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε` of the model results in an error of at most
`γ ε / (1 - γ)` in the action values and the values of `π`. This is the basic tool for planning
with an estimated model: errors in the transitions are measured only through the value of the
policy, not uniformly over all functions.

## Main statements

* `Learning.MDP.qValue_sub_qValue`: **the simulation lemma** [AJKS, Lemma 2.2],
  `Q^π_M - Q^π_M' = γ R_γ(P'^π_SA) ((P - P') v^π_M)`.
* `Learning.MDP.abs_qValue_sub_qValue_le`, `Learning.MDP.abs_value_sub_value_le`: if
  `|(P - P') v^π_M| ≤ ε`, the action values and the values of `π` in the two models differ by at
  most `γ ε / (1 - γ)`.

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemma 2.2
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {M M' : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] {C C' ε : ℝ}

/-- **The simulation lemma** [AJKS, Lemma 2.2]: for two MDPs `M` and `M'` with the same mean
reward and bounded rewards, `γ < 1` and a stationary policy `π`, the action values of `π` differ by
the resolvent of the state-action kernel of `π` in `M'` applied to the one-step difference of the
transition kernels acting on the value of `π` in `M`:
`Q^π_M - Q^π_M' = γ R_γ(P'^π_SA) ((P - P') v^π_M)`. -/
theorem qValue_sub_qValue (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C') (p : 𝓢 × 𝓐) :
    M.qValue γ π p - M'.qValue γ π p =
      γ * ∫ q, (∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q))
        ∂(Kernel.resolvent γ (M'.saKernel π) p) := by
  have h := Kernel.integral_resolvent_sub_integral_resolvent (κ := M'.saKernel π) (M.saKernel π)
    hγ (measurable_meanReward M.R) (abs_meanReward_le hR) p
  have hQ' := qValue_eq_integral_resolvent (M := M') (π := π) hγ hR' p
  rw [hr] at hQ'
  simp_rw [← hQ', ← qValue_eq_integral_resolvent hγ hR, integral_qValue_saKernel _ hγ hR] at h
  rw [← neg_sub, h, ← mul_neg, ← integral_neg]
  simp_rw [neg_sub]

/-- **The simulation bound**: for two MDPs `M` and `M'` with the same mean reward and bounded
rewards, `γ < 1` and a stationary policy `π`, if the one-step predictions of the value of `π` in
`M` differ by at most `ε`, `|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε`, then the action values
of `π` differ by at most `γ ε / (1 - γ)`. -/
theorem abs_qValue_sub_qValue_le (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hε : ∀ q, |∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q)| ≤ ε)
    (p : 𝓢 × 𝓐) :
    |M.qValue γ π p - M'.qValue γ π p| ≤ γ * ε / (1 - γ) := by
  rw [qValue_sub_qValue hr hγ hR hR', abs_mul, NNReal.abs_eq, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (Kernel.abs_integral_resolvent_le hγ hε p) γ.coe_nonneg

/-- For two MDPs `M` and `M'` with the same mean reward and bounded rewards, `γ < 1` and a
stationary policy `π`, if the one-step predictions of the value of `π` in `M` differ by at most
`ε`, `|∫ v^π_M dP (s, a) - ∫ v^π_M dP' (s, a)| ≤ ε`, then the values of `π` differ by at most
`γ ε / (1 - γ)`. -/
theorem abs_value_sub_value_le (hr : meanReward M'.R = meanReward M.R) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hR' : ∀ p, ∀ᵐ x ∂(M'.R p), |x| ≤ C')
    (hε : ∀ q, |∫ s, M.value γ π s ∂(M.P q) - ∫ s, M.value γ π s ∂(M'.P q)| ≤ ε) (s : 𝓢) :
    |M.value γ π s - M'.value γ π s| ≤ γ * ε / (1 - γ) := by
  have hint {M'' : MDP 𝓢 𝓐 ℝ} {C'' : ℝ} (hR'' : ∀ p, ∀ᵐ x ∂(M''.R p), |x| ≤ C'') :
      Integrable (fun a ↦ M''.qValue γ π (s, a)) (π s) :=
    integrable_of_abs_le ((measurable_qValue hγ hR'').comp measurable_prodMk_left)
      (fun a ↦ abs_qValue_le hγ hR'' (s, a)) _
  rw [← integral_qValue hγ hR, ← integral_qValue hγ hR', ← integral_sub (hint hR) (hint hR')]
  exact abs_integral_le_of_abs_le fun a ↦ abs_qValue_sub_qValue_le hr hγ hR hR' hε (s, a)

end Learning.MDP
