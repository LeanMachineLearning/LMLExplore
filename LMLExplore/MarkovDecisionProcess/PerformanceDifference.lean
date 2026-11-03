/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Comparison
public import LMLExplore.MarkovDecisionProcess.Occupancy

/-!
# The performance difference lemma and the discounted value-difference identity

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with bounded rewards, mean reward `r` and transition kernel `P`, and
let `0 ≤ γ < 1`. The value of an algorithm and a bounded measurable `v : 𝓢 → ℝ` differ by the
discounted sum, along the runs of the algorithm, of the Bellman residuals
`r (s, a) + γ * ∫ v dP (s, a) - v s` (`Learning.MDP.runValue_eq_integral_add_tsum`). Expressed
with the occupancy measure `d = M.occupancy γ alg μ` of the algorithm, this is

`runValue γ alg μ - ∫ v dμ = (1 - γ)⁻¹ * ∫ (r + γ P v - v) dd`.

Two choices of `v` give the basic identities of the value-difference calculus:
* for `v = v^π'` the value of a stationary policy `π'`, the residual is the advantage
  `A^π' (s, a) = Q^π' (s, a) - v^π' s`: this is the **performance difference lemma**
  [AJKS, Lemma 1.16], `runValue γ alg μ - ∫ v^π' dμ = (1 - γ)⁻¹ * ∫ A^π' dd`, valid for every
  history-dependent algorithm;
* for `v = V̂`, where `V̂ s = ∫ Q̂ (s, a) ∂π' s` for a bounded measurable `Q̂ : 𝓢 × 𝓐 → ℝ` and a
  stationary policy `π'`, and for the runs of a stationary policy `π`, the residual splits into a
  policy-mismatch term and a Bellman-error term of `Q̂`: this is the discounted form of the
  **extended value-difference identity** [JYW21, Lemma A.1],
  `∫ V̂ dμ - ∫ v^π dμ = (1 - γ)⁻¹ * (∫ (∫ Q̂ (s, ·) dπ' s - ∫ Q̂ (s, ·) dπ s) dd.fst (s)
    + ∫ (Q̂ - r - γ P V̂) dd)`.

These identities compare values without any reduction to Markov policies, and are the starting
point of the analyses of policy optimization, of planning with an estimated model and of offline
reinforcement learning.

## Main statements

* `Learning.MDP.runValue_sub_integral_eq_integral_occupancy`: the value of every algorithm minus
  `∫ v dμ` is `(1 - γ)⁻¹` times the integral of the Bellman residual of `v` against the occupancy
  measure of the algorithm.
* `Learning.MDP.runValue_sub_integral_value`: the performance difference lemma [AJKS, Lemma 1.16].
* `Learning.MDP.integral_integral_sub_integral_value`: the discounted extended value-difference
  identity [JYW21, Lemma A.1].

## References

* [A. Agarwal, N. Jiang, S. M. Kakade and W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022][AJKS], Lemma 1.16
* [S. Kakade and J. Langford, *Approximately optimal approximate reinforcement learning*,
  ICML 2002][KL02], Lemma 6.1
* [Y. Jin, Z. Yang and Z. Wang, *Is pessimism provably efficient for offline RL?*, ICML 2021,
  arXiv:2012.15085][JYW21], Lemma A.1
-/

public section

open MeasureTheory ProbabilityTheory Learning LMLExplore
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C B : ℝ} {v : 𝓢 → ℝ} {μ : Measure 𝓢} [IsProbabilityMeasure μ]

/-- **Value difference along the occupancy measure**: with bounded rewards and `γ < 1`, for every
algorithm `alg` and every bounded measurable `v`, the discounted value of `alg` from the
probability measure `μ` exceeds `∫ v dμ` by `(1 - γ)⁻¹` times the integral of the Bellman residual
`r (s, a) + γ * ∫ v dP (s, a) - v s` against the occupancy measure of `alg`. -/
theorem runValue_sub_integral_eq_integral_occupancy (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (alg : Algorithm 𝓢 𝓐 ℝ) :
    M.runValue γ alg μ - ∫ s, v s ∂μ =
      (1 - γ : ℝ)⁻¹ * ∫ p, (M.lookahead γ v p - v p.1) ∂(M.occupancy γ alg μ) := by
  have h := IT.isAlgEnvSeq_trajMeasure alg (M.env μ)
  have h0 : (1 - γ : ℝ) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hγ.ne')
  have hd : Measurable fun p : 𝓢 × 𝓐 ↦ M.lookahead γ v p - v p.1 :=
    (measurable_lookahead hv).sub (hv.comp measurable_fst)
  have hdB (p : 𝓢 × 𝓐) : |M.lookahead γ v p - v p.1| ≤ (C + γ * B) + B :=
    (abs_sub _ _).trans (add_le_add (abs_lookahead_le hR hvB p) (hvB _))
  rw [runValue_eq_integral_add_tsum h hγ hR hv hvB, add_sub_cancel_left,
    integral_occupancy h hγ (integrable_of_abs_le hd hdB _), inv_mul_cancel_left₀ h0]
  refine tsum_congr fun n ↦ ?_
  rw [integral_map (h.measurable_obs_action n).aemeasurable hd.aestronglyMeasurable]

/-- **Performance difference lemma** [AJKS, Lemma 1.16]: with bounded rewards and `γ < 1`, for
every algorithm `alg` and every stationary policy `π`, the discounted value of `alg` from the
probability measure `μ` exceeds `∫ v^π dμ` by `(1 - γ)⁻¹` times the integral of the advantage
`A^π` of `π` against the occupancy measure of `alg`. -/
theorem runValue_sub_integral_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (alg : Algorithm 𝓢 𝓐 ℝ) (π : Kernel 𝓢 𝓐) [IsMarkovKernel π] :
    M.runValue γ alg μ - ∫ s, M.value γ π s ∂μ =
      (1 - γ : ℝ)⁻¹ * ∫ p, M.advantage γ π p ∂(M.occupancy γ alg μ) := by
  simp_rw [advantage_def, qValue_eq_lookahead]
  exact runValue_sub_integral_eq_integral_occupancy hγ hR (measurable_value hγ hR)
    (abs_value_le hγ hR) alg

/-- **Extended value-difference identity**, discounted form [JYW21, Lemma A.1]: let `Q̂` be bounded
and measurable, `π'` a stationary policy and `V̂ s = ∫ Q̂ (s, a) ∂π' s`. With bounded rewards and
`γ < 1`, for every stationary policy `π` with occupancy measure `d` from the probability measure
`μ`, the difference `∫ V̂ dμ - ∫ v^π dμ` is `(1 - γ)⁻¹` times the sum of
* the policy-mismatch term `∫ (∫ Q̂ (s, ·) dπ' s - ∫ Q̂ (s, ·) dπ s) dd.fst (s)`, integrated
  against the state occupancy measure of `π`;
* the Bellman-error term `∫ (Q̂ - r - γ P V̂) dd`. -/
theorem integral_integral_sub_integral_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    {π π' : Kernel 𝓢 𝓐} [IsMarkovKernel π] [IsMarkovKernel π'] {Q : 𝓢 × 𝓐 → ℝ}
    (hQ : Measurable Q) (hQB : ∀ p, |Q p| ≤ B) :
    ∫ s, ∫ a, Q (s, a) ∂(π' s) ∂μ - ∫ s, M.value γ π s ∂μ =
      (1 - γ : ℝ)⁻¹ *
        (∫ s, (∫ a, Q (s, a) ∂(π' s) - ∫ a, Q (s, a) ∂(π s))
            ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) μ).fst +
          ∫ p, (Q p - M.lookahead γ (fun s ↦ ∫ a, Q (s, a) ∂(π' s)) p)
            ∂(M.occupancy γ (Algorithm.markov fun _ ↦ π) μ)) := by
  set d := M.occupancy γ (Algorithm.markov fun _ ↦ π) μ
  set V : 𝓢 → ℝ := fun s ↦ ∫ a, Q (s, a) ∂(π' s)
  have hV : Measurable V :=
    (hQ.stronglyMeasurable.integral_kernel_prod_right' (κ := π')).measurable
  have hVB (s : 𝓢) : |V s| ≤ B := abs_integral_le_of_abs_le fun a ↦ hQB (s, a)
  have hL : Measurable (M.lookahead γ V) := measurable_lookahead hV
  have hLB (p : 𝓢 × 𝓐) : |M.lookahead γ V p| ≤ C + γ * B := abs_lookahead_le hR hVB p
  -- the policy-mismatch term is the integral of `V̂ s - Q̂ (s, a)` against `d = d.fst ⊗ₘ π`
  have h_mismatch : ∫ s, (V s - ∫ a, Q (s, a) ∂(π s)) ∂d.fst = ∫ p, (V p.1 - Q p) ∂d := by
    have hint : Integrable (fun p : 𝓢 × 𝓐 ↦ V p.1 - Q p) (d.fst ⊗ₘ π) :=
      integrable_of_abs_le ((hV.comp measurable_fst).sub hQ)
        (fun p ↦ (abs_sub _ _).trans (add_le_add (hVB _) (hQB p))) _
    conv_rhs => rw [← d.disintegrate π]
    rw [Measure.integral_compProd hint]
    refine integral_congr_ae (.of_forall fun s ↦ ?_)
    dsimp only
    rw [integral_sub (integrable_const _) (integrable_of_abs_le (f := fun a ↦ Q (s, a))
      (hQ.comp measurable_prodMk_left) (fun a ↦ hQB (s, a)) _), integral_const, probReal_univ,
      one_smul]
  rw [← runValue_markov_const hγ hR, ← neg_sub,
    runValue_sub_integral_eq_integral_occupancy hγ hR hV hVB, h_mismatch,
    ← integral_add (integrable_of_abs_le (f := fun p ↦ V p.1 - Q p)
      ((hV.comp measurable_fst).sub hQ) (fun p ↦ (abs_sub _ _).trans (add_le_add (hVB _) (hQB p)))
      _)
      (integrable_of_abs_le (f := fun p ↦ Q p - M.lookahead γ V p) (hQ.sub hL)
        (fun p ↦ (abs_sub _ _).trans (add_le_add (hQB p) (hLB p))) _),
    ← mul_neg, ← integral_neg]
  congr 2 with p
  ring

end Learning.MDP
