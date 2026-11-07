/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Value
public import LMLExplore.Probability.MarkovChain.DiscountedReturn.Basic

/-!
# The variance of the discounted return of a stationary policy

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with mean reward `r = meanReward M.R`, `π` a stationary policy and
`γ < 1`. Under `π`, the state-action pairs form a Markov chain with kernel
`P^π_SA = M.saKernel π`, and the expected discounted return `∑ t, γ ^ t r (S_t, A_t)` of that chain
started at `(s, a)` is the action value `Q^π (s, a)`. Its variance is
`Σ^π (s, a) = M.returnVariance γ π (s, a)`. For deterministic rewards
(`M.R = Kernel.deterministic r _`), the discounted return of the mean rewards is the realized
discounted return, and `Σ^π` is its variance.

The total-variance identity for Markov chains, applied to the state-action chain, gives the
*variance Bellman equation* [AJKS, Lemma 2.11]
`Σ^π = γ ^ 2 Var_{P^π_SA}(Q^π) + γ ^ 2 P^π_SA Σ^π`. For a deterministic policy, the one-step
variance `Var_{P^π_SA}(Q^π) (s, a)` is the variance `Var_P(v^π) (s, a)` of the value `v^π` at the
next state drawn from `P (s, a)`; for a randomized policy it is larger, by the mean over the next
state of the variance of `Q^π` over the actions of `π`. Its consequence is the *total-variance
lemma* [AJKS, Lemma 2.12]: with rewards bounded by `C`, the resolvent of `P^π_SA` applied to the
standard deviations `√(Var_P(v^π))` is at most `C √(2 / (1 - γ) ^ 3)`, a factor `√(1 - γ)` better
than the bound `C / (1 - γ) ^ 2` given by `√(Var_P(v^π)) ≤ C / (1 - γ)` alone. Applied to an
empirical MDP, it is the variance bound behind the sample complexity of planning with a generative
model.

## Main definitions

* `Learning.MDP.returnVariance M γ π`: the variance `Σ^π (s, a)` of the discounted return of the
  mean rewards along the state-action chain of `π` started at `(s, a)`.

## Main statements

* `Learning.MDP.integral_discountedReturn_saKernel`: the mean of that return is `Q^π (s, a)`.
* `Learning.MDP.returnVariance_le`: `Σ^π ≤ γ ^ 2 (C / (1 - γ)) ^ 2`.
* `Learning.MDP.returnVariance_eq_add`: `Σ^π = γ ^ 2 (Var_{P^π_SA}(Q^π) + P^π_SA Σ^π)`.
* `Learning.MDP.variance_qValue_saKernel`: `Var_{P^π_SA}(Q^π) (s, a)` is
  `∫ s', Var_{π s'}(Q^π (s', ·)) dP (s, a) + Var_P(v^π) (s, a)`; in particular
  `Var_P(v^π) ≤ Var_{P^π_SA}(Q^π)` (`Learning.MDP.variance_value_le_variance_qValue`), with
  equality for deterministic policies (`Learning.MDP.variance_qValue_saKernel_deterministic`).
* `Learning.MDP.returnVariance_deterministic_eq_add`: for a deterministic policy,
  `Σ^π = γ ^ 2 Var_P(v^π) + γ ^ 2 P^π_SA Σ^π` [AJKS, Lemma 2.11].
* `Learning.MDP.integral_sqrt_variance_value_resolvent_le`: the total-variance lemma
  `R_γ(P^π_SA) √(Var_P(v^π)) ≤ C √(2 / (1 - γ) ^ 3)` [AJKS, Lemma 2.12].

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], §2.3, Lemmas 2.11 and 2.12
* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, 2013][AMK13]
-/

public section

open MeasureTheory ProbabilityTheory LMLExplore Learning
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] {C : ℝ}

/-- The variance `Σ^π (s, a)` of the discounted return `∑' t, γ ^ t r (S_t, A_t)` of the mean
rewards `r = meanReward M.R` along the state-action chain of the stationary policy `π` (with kernel
`M.saKernel π`) started at `p = (s, a)`. For deterministic rewards, this is the variance of the
realized discounted return. -/
noncomputable def returnVariance (p : 𝓢 × 𝓐) : ℝ :=
  Var[discountedReturn γ (meanReward M.R); (M.saKernel π).markovChainKernel p]

lemma returnVariance_def (p : 𝓢 × 𝓐) :
    M.returnVariance γ π p =
      Var[discountedReturn γ (meanReward M.R); (M.saKernel π).markovChainKernel p] :=
  (rfl)

variable {M γ π}

lemma returnVariance_nonneg (p : 𝓢 × 𝓐) : 0 ≤ M.returnVariance γ π p :=
  variance_nonneg _ _

/-- With bounded rewards and `γ < 1`, the expected discounted return of the mean rewards along the
state-action chain of `π` started at `p` is the action value `Q^π p`. -/
theorem integral_discountedReturn_saKernel (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (p : 𝓢 × 𝓐) :
    ∫ ω, discountedReturn γ (meanReward M.R) ω ∂((M.saKernel π).markovChainKernel p) =
      M.qValue γ π p := by
  rw [Kernel.integral_discountedReturn_markovChainKernel hγ (measurable_meanReward _)
    (abs_meanReward_le hR), qValue_eq_integral_resolvent hγ hR]

/-- With bounded rewards and `γ < 1`, the variance of the discounted return is measurable in the
starting state-action pair. -/
theorem measurable_returnVariance (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    Measurable (M.returnVariance γ π) :=
  (measurable_discountedReturn hγ (measurable_meanReward _) (abs_meanReward_le hR)).variance_kernel

/-- With rewards bounded by `C` and `γ < 1`, the variance of the discounted return is at most
`γ ^ 2 (C / (1 - γ)) ^ 2`; for rewards in `[0, 1]`, this is the bound `γ ^ 2 / (1 - γ) ^ 2` of
[AJKS, Lemma 2.11]. -/
theorem returnVariance_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    M.returnVariance γ π p ≤ (γ : ℝ) ^ 2 * (C / (1 - γ)) ^ 2 :=
  Kernel.variance_discountedReturn_markovChainKernel_le hγ (measurable_meanReward _)
    (abs_meanReward_le hR) p

/-- **The variance Bellman equation of a stationary policy**: with bounded rewards and `γ < 1`,
`Σ^π = γ ^ 2 Var_{P^π_SA}(Q^π) + γ ^ 2 P^π_SA Σ^π`, where `P^π_SA = M.saKernel π` and
`Var_{P^π_SA}(Q^π) p` is the variance of `Q^π` at the next state-action pair drawn from
`P^π_SA p`. -/
theorem returnVariance_eq_add (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    M.returnVariance γ π p = (γ : ℝ) ^ 2 * (Var[M.qValue γ π; M.saKernel π p] +
      ∫ q, M.returnVariance γ π q ∂(M.saKernel π p)) := by
  have h := Kernel.variance_discountedReturn_markovChainKernel_eq_add (κ := M.saKernel π) hγ
    (measurable_meanReward M.R) (abs_meanReward_le hR) p
  simp_rw [integral_discountedReturn_saKernel hγ hR] at h
  exact h

/-- **The one-step variance of the action value**: with bounded rewards and `γ < 1`, the variance
of `Q^π` at the state-action pair drawn from `P^π_SA p` is the mean over the next state `s` of the
variance of `Q^π (s, ·)` under `π s`, plus the variance `Var_P(v^π) p` of the value at the next
state drawn from `M.P p`. -/
theorem variance_qValue_saKernel (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    Var[M.qValue γ π; M.saKernel π p] =
      ∫ s, Var[fun a ↦ M.qValue γ π (s, a); π s] ∂(M.P p) + Var[M.value γ π; M.P p] := by
  have hQ := measurable_qValue (π := π) hγ hR
  have hmem : MemLp (M.qValue γ π) 2 (M.saKernel π p) := MemLp.of_bound hQ.aestronglyMeasurable
    (C / (1 - γ)) (.of_forall fun q ↦ (Real.norm_eq_abs _).trans_le (abs_qValue_le hγ hR q))
  -- From the state `s`, the pair `(s, a)` has law the image of `π s` under `a ↦ (s, a)`.
  have h_prod (s : 𝓢) : (Kernel.id ×ₖ π) s = (π s).map (Prod.mk s) := by
    rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]
  rw [saKernel_def, Kernel.comp_apply] at hmem ⊢
  rw [Kernel.variance_comp _ hmem]
  simp_rw [h_prod, variance_map hQ.aemeasurable measurable_prodMk_left.aemeasurable,
    integral_map measurable_prodMk_left.aemeasurable hQ.aestronglyMeasurable, Function.comp_def,
    integral_qValue hγ hR]

/-- With bounded rewards and `γ < 1`, the variance `Var_P(v^π) p` of the value at the next state is
at most the one-step variance `Var_{P^π_SA}(Q^π) p` of the action value. -/
theorem variance_value_le_variance_qValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (p : 𝓢 × 𝓐) :
    Var[M.value γ π; M.P p] ≤ Var[M.qValue γ π; M.saKernel π p] := by
  rw [variance_qValue_saKernel hγ hR]
  exact le_add_of_nonneg_left (integral_nonneg fun _ ↦ variance_nonneg _ _)

section Deterministic

variable {d : 𝓢 → 𝓐} (hd : Measurable d)

/-- For a measurable deterministic stationary policy `d`, with bounded rewards and `γ < 1`, the
one-step variance `Var_{P^d_SA}(Q^d) p` of the action value is the variance `Var_P(v^d) p` of the
value at the next state. -/
theorem variance_qValue_saKernel_deterministic (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    Var[M.qValue γ (Kernel.deterministic d hd); M.saKernel (Kernel.deterministic d hd) p] =
      Var[M.value γ (Kernel.deterministic d hd); M.P p] := by
  have hQ (s : 𝓢) : Measurable fun a ↦ M.qValue γ (Kernel.deterministic d hd) (s, a) :=
    (measurable_qValue hγ hR).comp measurable_prodMk_left
  rw [variance_qValue_saKernel hγ hR, add_eq_right]
  refine integral_eq_zero_of_ae (.of_forall fun s ↦ ?_)
  simp only [Pi.zero_apply, Kernel.deterministic_apply]
  rw [variance_eq_integral (hQ s).aemeasurable, integral_dirac' _ _ (hQ s).stronglyMeasurable,
    integral_dirac' _ _ (((hQ s).sub_const _).pow_const 2).stronglyMeasurable, sub_self,
    zero_pow two_ne_zero]

/-- **The variance Bellman equation of a deterministic policy** [AJKS, Lemma 2.11]: for a
measurable deterministic stationary policy `d`, with bounded rewards and `γ < 1`,
`Σ^d = γ ^ 2 Var_P(v^d) + γ ^ 2 P^d_SA Σ^d`. -/
theorem returnVariance_deterministic_eq_add (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (p : 𝓢 × 𝓐) :
    M.returnVariance γ (Kernel.deterministic d hd) p =
      (γ : ℝ) ^ 2 * Var[M.value γ (Kernel.deterministic d hd); M.P p] +
        (γ : ℝ) ^ 2 * ∫ q, M.returnVariance γ (Kernel.deterministic d hd) q
          ∂(M.saKernel (Kernel.deterministic d hd) p) := by
  rw [returnVariance_eq_add hγ hR, variance_qValue_saKernel_deterministic hd hγ hR, mul_add]

end Deterministic

/-- **The total-variance lemma** [AJKS, Lemma 2.12]: for a stationary policy `π`, rewards bounded
by `C` and `γ < 1`, the resolvent `R_γ(P^π_SA)` of the state-action kernel applied to the standard
deviations `√(Var_P(v^π))` of the value at the next state is at most `C √(2 / (1 - γ) ^ 3)`. -/
theorem integral_sqrt_variance_value_resolvent_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    ∫ q, √(Var[M.value γ π; M.P q]) ∂(Kernel.resolvent γ (M.saKernel π) p) ≤
      C * √(2 / (1 - γ) ^ 3) := by
  have := Kernel.isFiniteKernel_resolvent (κ := M.saKernel π) hγ
  have hγ' : 0 < 1 - (γ : ℝ) := sub_pos.2 hγ
  have hC : 0 ≤ C := (abs_nonneg _).trans (abs_meanReward_le hR p)
  have h := Kernel.integral_sqrt_variance_integral_discountedReturn_resolvent_le
    (κ := M.saKernel π) hγ (measurable_meanReward M.R) (abs_meanReward_le hR) p
  simp_rw [integral_discountedReturn_saKernel hγ hR] at h
  -- Both standard deviations are bounded measurable functions of the state-action pair.
  have h_int {g : 𝓢 × 𝓐 → ℝ} (hg : Measurable g) (hgB : ∀ q, g q ≤ (C / (1 - γ)) ^ 2) :
      Integrable (fun q ↦ √(g q)) (Kernel.resolvent γ (M.saKernel π) p) := by
    refine integrable_of_abs_le (B := C / (1 - γ)) hg.sqrt (fun q ↦ ?_) _
    rw [abs_of_nonneg (Real.sqrt_nonneg _), ← Real.sqrt_sq (by positivity : 0 ≤ C / (1 - γ))]
    exact Real.sqrt_le_sqrt (hgB q)
  calc ∫ q, √(Var[M.value γ π; M.P q]) ∂(Kernel.resolvent γ (M.saKernel π) p)
      ≤ ∫ q, √(Var[M.qValue γ π; M.saKernel π q]) ∂(Kernel.resolvent γ (M.saKernel π) p) := by
        refine integral_mono (h_int ((measurable_value hγ hR).variance_kernel (η := M.P))
          fun q ↦ variance_le_sq_of_abs_le (measurable_value hγ hR).aemeasurable
            (.of_forall (abs_value_le hγ hR)))
          (h_int ((measurable_qValue hγ hR).variance_kernel (η := M.saKernel π))
            fun q ↦ variance_le_sq_of_abs_le (measurable_qValue hγ hR).aemeasurable
              (.of_forall (abs_qValue_le hγ hR)))
          fun q ↦ Real.sqrt_le_sqrt (variance_value_le_variance_qValue hγ hR q)
    _ ≤ C * √((1 + γ) / (1 - γ) ^ 3) := h
    _ ≤ C * √(2 / (1 - γ) ^ 3) := by
        gcongr
        linarith

end Learning.MDP
