/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.MarkovDecisionProcess.Optimality
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

For a nonnegative reward `r_π`, the bound can be stated in terms of the value rather than of the
rewards [LWCGC24, Lemma 11]: if `v^π ≤ B`, the resolvent of the state kernel `P_π` applied to the
standard deviations `√(Var_{P_π}(v^π))` is at most `B / (γ √(1 - γ))`. The values
`V^(l) = R_γ(P_π) √(Var_{P_π}(V^(l-1)))` of the successive standard deviations, with
`V^(0) = v^π`, are the levels `M.valueLevel γ π l` of [LWCGC24, Lemma 2]; they are not policy
values. The generic form for a Markov kernel,
`ProbabilityTheory.Kernel.integral_sqrt_variance_integral_resolvent_le`, applied with
`f = √(Var_{P_π}(V^(l-2)))` (and `f = r_π` for `l = 1`), so that its resolvent is `V = V^(l-1)`,
bounds each `V^(l)` by `(γ √(1 - γ))⁻¹` times a bound on `V^(l-1)` [LWCGC24, (73)].
This recursion is how [LWCGC24] evaluates a fixed policy with a generative model from sample
sizes of order `(1 - γ)⁻¹`: if the state kernel `P'_π` of a second MDP `M'` with the same rewards
deviates from `P_π` on the first `m ≥ log (1 - γ)⁻¹` levels by a Bernstein-type bound, the values
of `π` in `M` and `M'` are close [LWCGC24, Lemmas 1 and 2].

## Main definitions

* `Learning.MDP.returnVariance M γ π`: the variance `Σ^π (s, a)` of the discounted return of the
  mean rewards along the state-action chain of `π` started at `(s, a)`.
* `Learning.MDP.valueLevel M γ π l`: the levels `V 0 = v^π` and
  `V (l + 1) = R_γ(P_π) √Var_{P_π}(V l)` of [LWCGC24, Lemma 2] for a stationary policy `π`.

## Main statements

* `Learning.MDP.integral_discountedReturn_saKernel`: the mean of that return is `Q^π (s, a)`.
* `Learning.MDP.returnVariance_le`: `Σ^π ≤ γ ^ 2 (C / (1 - γ)) ^ 2`.
* `Learning.MDP.returnVariance_eq_add`: `Σ^π = γ ^ 2 (Var_{P^π_SA}(Q^π) + P^π_SA Σ^π)`.
* `Learning.MDP.variance_qValue_saKernel`: `Var_{P^π_SA}(Q^π) (s, a)` is
  `∫ s', Var_{π s'}(Q^π (s', ·)) dP (s, a) + Var_P(v^π) (s, a)`; in particular
  `Var_P(v^π) ≤ Var_{P^π_SA}(Q^π)` (`Learning.MDP.variance_value_le_variance_qValue`), with
  equality for deterministic policies (`Learning.MDP.variance_qValue_saKernel_deterministic`).
* `Learning.MDP.variance_saKernel_deterministic`: for a deterministic policy `d`,
  `Var_{P^d_SA}(f) (s, a)` is the variance of `s' ↦ f (s', d s')` under `M.P (s, a)`.
* `Learning.MDP.returnVariance_deterministic_eq_add`: for a deterministic policy,
  `Σ^π = γ ^ 2 Var_P(v^π) + γ ^ 2 P^π_SA Σ^π` [AJKS, Lemma 2.11].
* `Learning.MDP.integral_sqrt_variance_value_resolvent_le`: the total-variance lemma
  `R_γ(P^π_SA) √(Var_P(v^π)) ≤ C √(2 / (1 - γ) ^ 3)` [AJKS, Lemma 2.12].
* `Learning.MDP.mul_integral_variance_value_stateKernel_resolvent_le`,
  `Learning.MDP.integral_sqrt_variance_value_stateKernel_resolvent_le`: for `r_π ≥ 0` and
  `v^π ≤ B`, `γ ^ 2 R_γ(P_π) Var_{P_π}(v^π) ≤ 2 B v^π - (v^π) ^ 2` and
  `R_γ(P_π) √(Var_{P_π}(v^π)) ≤ B / (γ √(1 - γ))` [LWCGC24, Lemma 11].
* `Learning.MDP.valueLevel_mem_Icc`: with rewards in `[0, C]`, the level `l` is in
  `[0, C / ((1 - γ) (γ √(1 - γ)) ^ l)]` [LWCGC24, (73)].
* `Learning.MDP.abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le`: the deterministic part
  of model-based policy evaluation [LWCGC24, Lemmas 1 and 2], for two MDPs with the same rewards,
  with the deviations in the form given by Bernstein's inequality at a level `L` and `ε = 2 L / N`.
  It is shared by `ReinforcementLearning/Generative/PolicyEvaluation.lean` [LWCGC24, Lemma 1] and
  `ReinforcementLearning/Generative/LeaveOneOut.lean` [LWCGC24, Lemma 5].
* `Learning.MDP.sq_mul_variance_optValue_add_mul_integral_le`: with rewards in `[0, C]`, for every
  Markov kernel `K` on the state-action pairs with `P (V* ^ 2) ≤ K (Q* ^ 2) + e`, the function
  `(2 C ^ 2 / (1 - γ) + γ ^ 2 e) / (1 - γ) - Q* ^ 2` is a supersolution for `γ ^ 2 Var_P(V*)`
  [LCCWC24, (97)–(98)], a closed form of [LCCWC24, Lemma 5].

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], §2.3, Lemmas 2.11 and 2.12
* [M. G. Azar, R. Munos and H. J. Kappen, *Minimax PAC bounds on the sample complexity of
  reinforcement learning with a generative model*, 2013][AMK13]
* [G. Li, Y. Wei, Y. Chi, Y. Gu and Y. Chen, *Breaking the sample size barrier in model-based
  reinforcement learning with a generative model*, Operations Research, 2024][LWCGC24], Lemmas 1,
  2 and 11 (arXiv:2005.12900)
* [G. Li, C. Cai, Y. Chen, Y. Wei and Y. Chi, *Is Q-learning minimax optimal? A tight sample
  complexity analysis*, Operations Research, 2024][LCCWC24], Lemma 5 (arXiv:2102.06548)
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

/-- For a measurable deterministic stationary policy `d`, the variance under the state-action
kernel of `d` from `p` is the variance at the next state: `Var_{P^d_SA}(f) p` is the variance of
`s ↦ f (s, d s)` under `M.P p`. -/
lemma variance_saKernel_deterministic {p : 𝓢 × 𝓐} {f : 𝓢 × 𝓐 → ℝ}
    (hf : AEMeasurable f (M.saKernel (Kernel.deterministic d hd) p)) :
    Var[f; M.saKernel (Kernel.deterministic d hd) p] = Var[fun s ↦ f (s, d s); M.P p] := by
  rw [saKernel_apply, Measure.compProd_deterministic] at hf ⊢
  exact variance_map hf (measurable_id.prodMk hd).aemeasurable

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
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_iff.2 ⟨by positivity, hgB q⟩
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

/-- For a stationary policy `π` with nonnegative reward `r_π`, bounded rewards and `γ < 1`, if the
value `v^π` is bounded by `B`, then the resolvent `R_γ(P_π)` of the state kernel applied to the
one-step variances `Var_{P_π}(v^π)` of the value satisfies
`γ ^ 2 R_γ(P_π) Var_{P_π}(v^π) ≤ 2 B v^π - (v^π) ^ 2`, hence `≤ B ^ 2`. -/
theorem mul_integral_variance_value_stateKernel_resolvent_le (hγ : γ < 1) {B : ℝ}
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hr : ∀ s, 0 ≤ M.policyReward π s)
    (hvB : ∀ s, M.value γ π s ≤ B) (s : 𝓢) :
    (γ : ℝ) ^ 2 * ∫ s', Var[M.value γ π; M.stateKernel π s']
        ∂(Kernel.resolvent γ (M.stateKernel π) s) ≤
      2 * B * M.value γ π s - M.value γ π s ^ 2 := by
  rw [funext (value_eq_integral_resolvent hγ hR)] at hvB ⊢
  exact Kernel.mul_integral_variance_integral_resolvent_le hγ measurable_policyReward
    (abs_policyReward_le hR) hr hvB s

/-- **The total-variance lemma in terms of the value** [LWCGC24, Lemma 11]: for a stationary
policy `π` with nonnegative reward `r_π`, bounded rewards and `0 < γ < 1`, if the value `v^π` is
bounded by `B`, then the resolvent `R_γ(P_π)` of the state kernel applied to the one-step standard
deviations `√(Var_{P_π}(v^π))` of the value is at most `B / (γ √(1 - γ))`. This improves the
constant `4` of [LWCGC24, Lemma 11] to `1`. -/
theorem integral_sqrt_variance_value_stateKernel_resolvent_le (hγ₀ : 0 < γ) (hγ : γ < 1)
    {B : ℝ} (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hr : ∀ s, 0 ≤ M.policyReward π s)
    (hvB : ∀ s, M.value γ π s ≤ B) (s : 𝓢) :
    ∫ s', √(Var[M.value γ π; M.stateKernel π s']) ∂(Kernel.resolvent γ (M.stateKernel π) s) ≤
      B / (γ * √(1 - γ)) := by
  rw [funext (value_eq_integral_resolvent hγ hR)] at hvB ⊢
  exact Kernel.integral_sqrt_variance_integral_resolvent_le hγ₀ hγ measurable_policyReward
    (abs_policyReward_le hR) hr hvB s

end Learning.MDP

/-! ### The levels of [LWCGC24, Lemma 2] -/

namespace Learning.MDP

open Real (log)

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}

/-- The levels of [LWCGC24, Lemma 2] for a stationary policy `π`, with state kernel `P_π`:
`V 0 = R_γ(P_π) r_π`, which is the value `v^π` for bounded rewards and `γ < 1`, and
`V (l + 1) = R_γ(P_π) √Var_{P_π}(V l)`. -/
noncomputable def valueLevel (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (π : Kernel 𝓢 𝓐) : ℕ → 𝓢 → ℝ
  | 0, x => ∫ y, M.policyReward π y ∂(Kernel.resolvent γ (M.stateKernel π) x)
  | l + 1, x =>
    ∫ y, √Var[valueLevel M γ π l; M.stateKernel π y] ∂(Kernel.resolvent γ (M.stateKernel π) x)

@[simp]
lemma valueLevel_zero (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (π : Kernel 𝓢 𝓐) (x : 𝓢) :
    M.valueLevel γ π 0 x = ∫ y, M.policyReward π y ∂(Kernel.resolvent γ (M.stateKernel π) x) :=
  (rfl)

@[simp]
lemma valueLevel_succ (M : MDP 𝓢 𝓐 ℝ) (γ : ℝ≥0) (π : Kernel 𝓢 𝓐) (l : ℕ) (x : 𝓢) :
    M.valueLevel γ π (l + 1) x =
      ∫ y, √Var[M.valueLevel γ π l; M.stateKernel π y] ∂(Kernel.resolvent γ (M.stateKernel π) x) :=
  (rfl)

/-- With rewards in `[0, C]` and `0 < γ < 1`, the level `l` of [LWCGC24, Lemma 2] for a stationary
policy is in `[0, C / ((1 - γ) (γ √(1 - γ)) ^ l)]` [LWCGC24, (73)]. -/
lemma valueLevel_mem_Icc {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : γ < 1) {C : ℝ}
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] (l : ℕ)
    (x : 𝓢) : M.valueLevel γ π l x ∈ Set.Icc 0 (C / ((1 - γ) * (γ * √(1 - γ)) ^ l)) :=
  Kernel.mem_Icc_of_eq_integral_resolvent_sqrt_variance hγ₀ hγ measurable_policyReward
    (fun y ↦ (policyReward_mem_Icc hR y).1) (fun y ↦ (policyReward_mem_Icc hR y).2)
    (valueLevel_zero M γ π) (valueLevel_succ M γ π) l x

/-- **The deterministic part of model-based policy evaluation** [LWCGC24, Lemmas 1 and 2]. Let
`M` and `M'` be MDPs with the same rewards, in `[0, C]`, `0 < γ < 1`, and `π` a stationary policy,
with state kernels `P_π` in `M` and `P'_π` in `M'`. Let `V = M.valueLevel γ π` be the levels
`V 0 = v^π` and `V (l + 1) = R_γ(P_π) √Var_{P_π}(V l)` of [LWCGC24, Lemma 2], bounded by
`b l = C / ((1 - γ) (γ √(1 - γ)) ^ l)`, and `log (1 - γ)⁻¹ ≤ m`. Let `L ≥ 0`, `N > 0` and
`18 L ≤ (1 - γ) N`. If `P'_π` deviates from `P_π` on the levels `l ≤ m` by the bound
`√(2 Var_{P_π}(V l) L / N) + b l L / (3 N)` of Bernstein's inequality at the level `L`, then the
value of `π` in `M'` satisfies `|v'^π - v^π| ≤ 3 C √(2 L / (N (1 - γ) ^ 3))`.

This is `ProbabilityTheory.Kernel.abs_integral_resolvent_sub_integral_resolvent_le_of_abs_sub_le`
with `ε = 2 L / N`, for the resolvent forms `v^π = R_γ(P_π) r_π` and `v'^π = R_γ(P'_π) r_π` of the
two values. -/
theorem abs_value_sub_value_le_of_abs_integral_stateKernel_sub_le {M M' : MDP 𝓢 𝓐 ℝ}
    (hM' : M'.R = M.R) {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : γ < 1) {C : ℝ}
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] {m : ℕ}
    (hm : log (1 - (γ : ℝ))⁻¹ ≤ m) {N L : ℝ} (hN : 0 < N) (hL : 0 ≤ L) (hNL : 18 * L ≤ (1 - γ) * N)
    (h : ∀ l ≤ m, ∀ x,
      |∫ y, M.valueLevel γ π l y ∂(M'.stateKernel π x) -
          ∫ y, M.valueLevel γ π l y ∂(M.stateKernel π x)| ≤
        √(2 * Var[M.valueLevel γ π l; M.stateKernel π x] * L / N) +
          C / ((1 - γ) * (γ * √(1 - γ)) ^ l) * L / (3 * N)) (s : 𝓢) :
    |M'.value γ π s - M.value γ π s| ≤ 3 * C * √(2 * L / (N * (1 - γ) ^ 3)) := by
  have hRabs (p : 𝓢 × 𝓐) : ∀ᵐ x ∂(M.R p), |x| ≤ C :=
    (hR p).mono fun x hx ↦ (abs_of_nonneg hx.1).trans_le hx.2
  have hf (y : 𝓢) := policyReward_mem_Icc (π := π) hR y
  -- both values are resolvents of the same reward `r_π`
  have hfe : M'.policyReward π = M.policyReward π :=
    funext fun y ↦ by rw [policyReward_def, hM', policyReward_def]
  rw [value_eq_integral_resolvent hγ (hM' ▸ hRabs), value_eq_integral_resolvent hγ hRabs, hfe]
  -- Lemma 2 with `ε = 2 L / N`, for which `9 ε ≤ 1 - γ`
  have hε9 : 9 * (2 * L / N) ≤ 1 - γ := by
    rw [← mul_div_assoc, div_le_iff₀ hN]
    linarith
  refine (Kernel.abs_integral_resolvent_sub_integral_resolvent_le_of_abs_sub_le
    (M'.stateKernel π) hγ₀ hγ measurable_policyReward (fun y ↦ (hf y).1) (fun y ↦ (hf y).2)
    (valueLevel_zero M γ π) (valueLevel_succ M γ π) hm (by positivity) hε9
    (fun l hl x ↦ (h l hl x).trans (add_le_add (le_of_eq ?_) ?_)) s).trans_eq ?_
  · congr 1
    ring
  · -- the bound `b l` of the level `l` is nonnegative
    have hb := valueLevel_mem_Icc hγ₀ hγ hR π l x
    have hbL : 0 ≤ C / ((1 - γ) * (γ * √(1 - γ)) ^ l) * L / N := by
      have := hb.1.trans hb.2
      positivity
    calc C / ((1 - γ) * (γ * √(1 - γ)) ^ l) * L / (3 * N)
        = C / ((1 - γ) * (γ * √(1 - γ)) ^ l) * L / N / 3 := by
          rw [div_div, mul_comm (3 : ℝ)]
      _ ≤ C / ((1 - γ) * (γ * √(1 - γ)) ^ l) * L / N * 2 := by linarith
      _ = 2 * L / N * (C / ((1 - γ) * (γ * √(1 - γ)) ^ l)) := by ring
  · rw [div_div]

end Learning.MDP

/-! ### The one-step variances of the optimal value along near-greedy kernels -/

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Finite 𝓢]
  [Nonempty 𝓢] [MeasurableSingletonClass 𝓢] [Finite 𝓐] [Nonempty 𝓐] [MeasurableSingletonClass 𝓐]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C : ℝ}

/-- **A supersolution for the one-step variances of the optimal value** [LCCWC24, (97)–(98)].
With rewards in `[0, C]` and `γ < 1`, let `K` be a Markov kernel on the state-action pairs with
`P (V* ^ 2) ≤ K (Q* ^ 2) + e` at `p`, as for the state-action kernel of a policy `π` with
`V* ^ 2 ≤ Q* (·, π ·) ^ 2 + e`. Then `G - Q* ^ 2`, with
`G = (2 C ^ 2 / (1 - γ) + γ ^ 2 e) / (1 - γ)`, satisfies at `p` the supersolution inequality
`γ ^ 2 Var_P(V*) + γ K (G - Q* ^ 2) ≤ G - Q* ^ 2`. Since it holds for every such kernel at once,
for `e ≥ 0` the discounted sums of `γ ^ 2 Var_P(V*)` along any sequence of near-greedy kernels
are at most `G`: this is the content of [LCCWC24, Lemma 5], there obtained by telescoping along
each sequence. -/
theorem sq_mul_variance_optValue_add_mul_integral_le (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), x ∈ Set.Icc 0 C) {K : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)} [IsMarkovKernel K]
    {e : ℝ} {p : 𝓢 × 𝓐}
    (hK : ∫ s, M.optValue γ s ^ 2 ∂(M.P p) ≤ ∫ q, M.optQValue γ q ^ 2 ∂(K p) + e) :
    (γ : ℝ) ^ 2 * Var[M.optValue γ; M.P p] +
        γ * ∫ q, ((2 * (C / (1 - γ)) * C + γ ^ 2 * e) / (1 - γ) - M.optQValue γ q ^ 2) ∂(K p) ≤
      (2 * (C / (1 - γ)) * C + γ ^ 2 * e) / (1 - γ) - M.optQValue γ p ^ 2 := by
  have h1γ : (0 : ℝ) < 1 - γ := sub_pos.2 (NNReal.coe_lt_one.2 hγ)
  have hγ1 : (γ : ℝ) ≤ 1 := by exact_mod_cast hγ.le
  have hRabs (q : 𝓢 × 𝓐) := ae_abs_le_of_ae_mem_Icc (hR q)
  have hr (q : 𝓢 × 𝓐) := meanReward_mem_Icc_of_ae_mem_Icc (hR q)
  have hQ₀ := optQValue_nonneg hγ hRabs (fun q ↦ (hr q).1) p
  have hQB := (le_abs_self _).trans (abs_optQValue_le hγ hRabs p)
  have hIK : 0 ≤ ∫ q, M.optQValue γ q ^ 2 ∂(K p) := integral_nonneg fun q ↦ sq_nonneg _
  set G := (2 * (C / (1 - γ)) * C + γ ^ 2 * e) / (1 - γ) with hG_def
  have hG : (1 - γ) * G = 2 * (C / (1 - γ)) * C + γ ^ 2 * e := by
    rw [hG_def]
    field_simp
  -- `Var_P(V*) = P (V* ^ 2) - (P V*) ^ 2` and the Bellman equation `Q* = r + γ P V*`
  rw [variance_eq_sub .of_discrete, integral_sub (integrable_const _) .of_finite, integral_const,
    probReal_univ, one_smul, optQValue_def (p := p)]
  simp only [Pi.pow_apply]
  have hQ := optQValue_def (M := M) (γ := γ) p
  rw [hQ] at hQ₀ hQB
  -- `P (V* ^ 2) ≤ K (Q* ^ 2) + e`, `γ ^ 2 K (Q* ^ 2) ≤ γ K (Q* ^ 2)` and `r Q* ≤ C ^ 2 / (1 - γ)`
  nlinarith [mul_le_mul_of_nonneg_left hK (sq_nonneg (γ : ℝ)),
    mul_nonneg (mul_nonneg γ.coe_nonneg (sub_nonneg.2 hγ1)) hIK,
    mul_le_mul (hr p).2 hQB hQ₀ ((hr p).1.trans (hr p).2), sq_nonneg (meanReward M.R p)]

end Learning.MDP
