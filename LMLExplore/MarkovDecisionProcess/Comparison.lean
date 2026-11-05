/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.RunValue
public import LMLExplore.MarkovDecisionProcess.Value

/-!
# Comparison of discounted values with sub- and supersolutions of the Bellman equations

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with bounded rewards, mean reward `r` and transition kernel `P`,
let `0 ≤ γ < 1`, and let `v : 𝓢 → ℝ` be bounded and measurable. Along every run of every
algorithm in `M.env μ`, with states `S n` and actions `A n`, the expected one-step lookahead
`r (S n, A n) + γ * ∫ v dP (S n, A n)` is the expected reward of round `n` plus `γ` times the
expectation of `v (S (n + 1))`. Summing the discounted differences between the lookahead and `v`
therefore telescopes:

`runValue γ alg μ = ∫ v dμ + ∑' n, γ ^ n * E[lookahead γ v (S n, A n) - v (S n)]`.

This identity compares the value of an algorithm with `v` without any reduction to Markov
policies, and gives:
* if `v` is a *supersolution*, `r (s, a) + γ * ∫ v dP (s, a) ≤ v s` for all `s` and `a`, then
  the value of every algorithm from `μ` is at most `∫ v dμ`, hence `v* ≤ v`;
* if `v` is a *subsolution* of the evaluation equation of a stationary policy `π`,
  `v ≤ r_π + γ P_π v`, then `v ≤ v^π`;
* if `v` is a subsolution of the optimality equation, `v ≤ T v`, then `v ≤ v*`, through the
  policy greedy for `v` (for finitely many actions);
* hence a bounded measurable solution of the optimality equation `T v = v` is `v*`.

For a stationary policy `π` and `v = v^π`, the lookahead is the action value of `π` and the
differences have mean zero under `π`, so the discounted value of the runs of `π` from `μ` is
`∫ v^π dμ`. In particular `v^π ≤ v*`.

Here `T` is the Bellman optimality operator `M.bellman γ` and `v*` the optimal value
`M.optValue γ`, the supremum of the discounted values of all history-dependent policies.

## Main statements

* `Learning.MDP.integral_lookahead`: along a run, the expected lookahead of `v` at round `n` is
  the expected reward of round `n` plus `γ` times the expectation of `v` at round `n + 1`.
* `Learning.MDP.runValue_eq_integral_add_tsum`: the telescoping identity above, along every run
  of every algorithm; `Learning.MDP.runValue_markov_const_eq_integral_add_tsum`: its form for a
  stationary policy `π`, in terms of the evaluation operator of `π` and the laws of the states.
* `Learning.MDP.runValue_le_integral_of_lookahead_le`, `Learning.MDP.optValue_le_of_lookahead_le`,
  `Learning.MDP.optValue_le_of_bellman_le`: a supersolution bounds the value of every algorithm
  and the optimal value [P, Theorem 6.2.2 (a)].
* `Learning.MDP.runValue_markov_const`: the value of the runs of a stationary policy `π` from `μ`
  is `∫ v^π dμ`; `Learning.MDP.value_le_optValue`: `v^π ≤ v*`.
* `Learning.MDP.bellmanEval_iterate_succ_sub`, `Learning.MDP.bellmanEval_iterate_eq_add_sum`: the
  increments of the iterates of `T_π` are `T_π^[n + 1] v - T_π^[n] v = (γ P_π) ^ n (T_π v - v)`,
  so `T_π^[n] v = v + ∑ k < n, (γ P_π) ^ k (T_π v - v)`.
* `Learning.MDP.value_eq_add_tsum`: for every bounded measurable `v`,
  `v^π = v + ∑ n, γ ^ n P_π ^ n (T_π v - v)`, where `T_π` is the evaluation operator of `π`.
* `Learning.MDP.le_value_of_le_bellmanEval`, `Learning.MDP.le_optValue_of_le_bellman`: a
  subsolution is a lower bound of `v^π`, respectively of `v*` [P, Theorem 6.2.2 (b)];
  `Learning.MDP.bellmanEval_le_value`: policy improvement, `v ≤ T_π v → T_π v ≤ v^π`.
* `Learning.MDP.eq_optValue_of_bellman_eq`: a bounded measurable solution of the optimality
  equation is the optimal value [P, Theorem 6.2.2 (c)].

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], Theorem 6.2.2
-/

public section

open MeasureTheory ProbabilityTheory Learning LMLExplore
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C B : ℝ} {v : 𝓢 → ℝ}

/-! ### The telescoping identity along a run -/

section Runs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {S : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓢 𝓐 ℝ} {μ : Measure 𝓢}

/-- Along a run in an MDP with bounded rewards, the expected one-step lookahead of a bounded
measurable `v` at the state-action pair of round `n` is the expected mean reward of round `n`
plus `γ` times the expectation of `v` at the state of round `n + 1`. -/
theorem integral_lookahead (h : IsAlgEnvSeq S A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (n : ℕ) :
    ∫ ω, M.lookahead γ v (S n ω, A n ω) ∂P =
      ∫ ω, meanReward M.R (S n ω, A n ω) ∂P + γ * ∫ ω, v (S (n + 1) ω) ∂P := by
  have hm : Measurable fun ω ↦ (S n ω, A n ω) := h.measurable_obs_action n
  have hPv : Measurable fun p ↦ ∫ s', v s' ∂(M.P p) :=
    (hv.stronglyMeasurable.integral_kernel (κ := M.P)).measurable
  simp_rw [lookahead_def]
  rw [integral_add (integrable_of_abs_le (f := fun ω ↦ meanReward M.R (S n ω, A n ω))
      ((measurable_meanReward M.R).comp hm) (fun ω ↦ abs_meanReward_le hR _) P)
      ((integrable_of_abs_le (f := fun ω ↦ ∫ s', v s' ∂(M.P (S n ω, A n ω))) (hPv.comp hm)
        (fun ω ↦ abs_integral_le_of_abs_le hvB) P).const_mul _),
    integral_const_mul]
  congr 2
  -- the state of round `n + 1` has law `M.P ∘ₘ law (S n, A n)`
  rw [← integral_map (h.measurable_obs (n + 1)).aemeasurable hv.aestronglyMeasurable,
    (hasLaw_obs_add_one h n).map_eq, Measure.comp_eq_comp_const_apply,
    Kernel.integral_comp (integrable_of_abs_le hv hvB _), Kernel.const_apply,
    integral_map hm.aemeasurable hPv.aestronglyMeasurable]

/-- **Telescoping identity**: along every run of `alg` in `M.env μ`, with bounded rewards, `γ < 1`
and a bounded measurable `v`, the discounted value of `alg` is `∫ v dμ` plus the discounted sum of
the expected differences between the one-step lookahead of `v` and `v` along the run. -/
theorem runValue_eq_integral_add_tsum [IsProbabilityMeasure μ]
    (h : IsAlgEnvSeq S A Y alg (M.env μ) P) (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) :
    M.runValue γ alg μ = ∫ s, v s ∂μ +
      ∑' n, (γ : ℝ) ^ n * ∫ ω, (M.lookahead γ v (S n ω, A n ω) - v (S n ω)) ∂P := by
  have hm (n : ℕ) : Measurable fun ω ↦ (S n ω, A n ω) := h.measurable_obs_action n
  -- discounted bounded sequences are summable
  have hsum {f : ℕ → ℝ} {K : ℝ} (hf : ∀ n, |f n| ≤ K) : Summable fun n ↦ (γ : ℝ) ^ n * f n :=
    .of_norm_bounded ((summable_geometric_of_lt_one γ.coe_nonneg hγ).mul_right K) fun n ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, NNReal.abs_eq]
      gcongr
      exact hf n
  set a : ℕ → ℝ := fun n ↦ ∫ ω, v (S n ω) ∂P
  set r : ℕ → ℝ := fun n ↦ ∫ ω, meanReward M.R (S n ω, A n ω) ∂P
  have ha : Summable fun n ↦ (γ : ℝ) ^ n * a n :=
    hsum fun n ↦ abs_integral_le_of_abs_le fun _ ↦ hvB _
  have hr : Summable fun n ↦ (γ : ℝ) ^ n * r n :=
    hsum fun n ↦ abs_integral_le_of_abs_le fun _ ↦ abs_meanReward_le hR _
  -- the terms of the series are `γ ^ n * r n + (γ ^ (n + 1) * a (n + 1) - γ ^ n * a n)`
  have hterm (n : ℕ) : (γ : ℝ) ^ n * ∫ ω, (M.lookahead γ v (S n ω, A n ω) - v (S n ω)) ∂P =
      (γ : ℝ) ^ n * r n + ((γ : ℝ) ^ (n + 1) * a (n + 1) - (γ : ℝ) ^ n * a n) := by
    rw [integral_sub (integrable_of_abs_le (f := fun ω ↦ M.lookahead γ v (S n ω, A n ω))
        ((measurable_lookahead hv).comp (hm n)) (fun _ ↦ abs_lookahead_le hR hvB _) P)
        (integrable_of_abs_le (f := fun ω ↦ v (S n ω)) (hv.comp (h.measurable_obs n))
          (fun _ ↦ hvB _) P),
      integral_lookahead h hR hv hvB n]
    ring
  have hr_eq : M.runValue γ alg μ = ∑' n, (γ : ℝ) ^ n * r n := by
    rw [runValue_eq_tsum h hγ hR]
    refine tsum_congr fun n ↦ ?_
    rw [integral_map (hm n).aemeasurable (measurable_meanReward M.R).aestronglyMeasurable]
  have ha0 : a 0 = ∫ s, v s ∂μ :=
    (hasLaw_obs_zero h).integral_comp hv.aestronglyMeasurable
  have ha_succ : Summable fun n ↦ (γ : ℝ) ^ (n + 1) * a (n + 1) :=
    (summable_nat_add_iff 1).2 ha
  simp_rw [hterm]
  rw [hr.tsum_add (ha_succ.sub ha), ha_succ.tsum_sub ha, ha.tsum_eq_zero_add, hr_eq, ← ha0]
  simp

/-- **Telescoping identity for a stationary policy**: with bounded rewards, `γ < 1` and a bounded
measurable `v`, the discounted value of the runs of the stationary policy `π` from `μ` is `∫ v dμ`
plus the discounted sum of the integrals of `T_π v - v` against the laws `P_π ^ n ∘ₘ μ` of the
states, where `T_π` is the evaluation operator of `π`. -/
theorem runValue_markov_const_eq_integral_add_tsum [IsProbabilityMeasure μ] {π : Kernel 𝓢 𝓐}
    [IsMarkovKernel π] (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) :
    M.runValue γ (Algorithm.markov fun _ ↦ π) μ = ∫ s, v s ∂μ +
      ∑' n, (γ : ℝ) ^ n *
        ∫ s, (M.bellmanEval γ π v s - v s) ∂((M.stateKernel π ^ n : Kernel 𝓢 𝓢) ∘ₘ μ) := by
  have h := IT.isAlgEnvSeq_trajMeasure (Algorithm.markov fun _ ↦ π) (M.env μ)
  rw [runValue_eq_integral_add_tsum h hγ hR hv hvB]
  congr 1
  refine tsum_congr fun n ↦ ?_
  -- the state-action pair of round `n` has law `μₙ ⊗ₘ π`, with `μₙ = P_π ^ n ∘ₘ μ`
  have hlaw := (hasLaw_obs_action_markov h n).integral_comp
    (f := fun p ↦ M.lookahead γ v p - v p.1)
    (integrable_lookahead_sub hR hv hvB _).aestronglyMeasurable
  simp only [Function.comp_def] at hlaw
  rw [hlaw, Measure.integral_compProd (integrable_lookahead_sub hR hv hvB _),
    stateMarginal_const]
  congr 1
  refine integral_congr_ae (.of_forall fun s ↦ ?_)
  dsimp only
  rw [integral_sub (integrable_lookahead_prodMk_left hR hv hvB s _) (integrable_const _),
    integral_const, probReal_univ, one_smul, bellmanEval_def]

end Runs

/-! ### Supersolutions -/

section Supersolution

/-- **Comparison with a supersolution** [P, Theorem 6.2.2 (a)]: with bounded rewards and `γ < 1`,
if a bounded measurable `v` satisfies `r (s, a) + γ * ∫ v dP (s, a) ≤ v s` for all `s` and `a`,
then the discounted value of every algorithm from the probability measure `μ` is at most
`∫ v dμ`. -/
theorem runValue_le_integral_of_lookahead_le {μ : Measure 𝓢} [IsProbabilityMeasure μ]
    (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hle : ∀ p, M.lookahead γ v p ≤ v p.1) (alg : Algorithm 𝓢 𝓐 ℝ) :
    M.runValue γ alg μ ≤ ∫ s, v s ∂μ := by
  rw [runValue_eq_integral_add_tsum (IT.isAlgEnvSeq_trajMeasure alg (M.env μ)) hγ hR hv hvB,
    add_le_iff_nonpos_right]
  exact tsum_nonpos fun n ↦ mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (integral_nonpos fun _ ↦ sub_nonpos.2 (hle _))

/-- [P, Theorem 6.2.2 (a)]: with bounded rewards and `γ < 1`, a bounded measurable `v` such that
`r (s, a) + γ * ∫ v dP (s, a) ≤ v s` for all `s` and `a` dominates the optimal value. -/
theorem optValue_le_of_lookahead_le [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hle : ∀ p, M.lookahead γ v p ≤ v p.1) :
    M.optValue γ ≤ v := fun s ↦
  (optValue_le_iff hγ hR).2 fun alg ↦
    (runValue_le_integral_of_lookahead_le hγ hR hv hvB hle alg).trans_eq
      (integral_dirac' _ s hv.stronglyMeasurable)

/-- [P, Theorem 6.2.2 (a)]: with bounded rewards and `γ < 1`, a bounded measurable `v` with
`T v ≤ v` dominates the optimal value, where `T` is the Bellman optimality operator. -/
theorem optValue_le_of_bellman_le [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hle : M.bellman γ v ≤ v) :
    M.optValue γ ≤ v :=
  optValue_le_of_lookahead_le hγ hR hv hvB fun p ↦
    (bellman_le_iff (bddAbove_range_lookahead hR hvB p.1)).1 (hle p.1) p.2

end Supersolution

/-! ### Stationary policies and subsolutions -/

section Subsolution

variable {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]

/-- With bounded rewards and `γ < 1`, the discounted value of the runs of the stationary policy
`π` from the probability measure `μ` is the integral `∫ v^π dμ` of the value of `π`. -/
theorem runValue_markov_const {μ : Measure 𝓢} [IsProbabilityMeasure μ] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.runValue γ (Algorithm.markov fun _ ↦ π) μ = ∫ s, M.value γ π s ∂μ := by
  rw [runValue_markov_const_eq_integral_add_tsum hγ hR (measurable_value (π := π) hγ hR)
    (abs_value_le hγ hR), bellmanEval_value hγ hR]
  simp

/-- With bounded rewards and `γ < 1`, the value of every stationary policy is at most the
optimal value. -/
theorem value_le_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.value γ π ≤ M.optValue γ := fun s ↦ by
  rw [← integral_dirac' _ s (measurable_value hγ hR).stronglyMeasurable,
    ← runValue_markov_const (π := π) hγ hR]
  exact runValue_le_optValue hγ hR _ s

omit [Nonempty 𝓢] in
/-- With bounded rewards, the increments of the iterates of the evaluation operator `T_π` of a
stationary policy at a bounded measurable `v` are
`T_π^[n + 1] v - T_π^[n] v = γ ^ n P_π ^ n (T_π v - v)`, where `P_π` is the state kernel of `π`. -/
theorem bellmanEval_iterate_succ_sub (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) (s : 𝓢) :
    (M.bellmanEval γ π)^[n + 1] v s - (M.bellmanEval γ π)^[n] v s =
      (γ : ℝ) ^ n * ∫ s', (M.bellmanEval γ π v s' - v s') ∂((M.stateKernel π ^ n) s) := by
  -- the iterates of `T_π` at `v` are bounded measurable
  have hm := measurable_bellmanEval_iterate (M := M) (γ := γ) (π := π) hv
  choose K hB using exists_abs_bellmanEval_iterate_le (M := M) (γ := γ) (π := π) hR hvB
  have hg : Measurable fun s' ↦ M.bellmanEval γ π v s' - v s' :=
    (measurable_bellmanEval hv).sub hv
  have hgi (μ : Measure 𝓢) [IsFiniteMeasure μ] :
      Integrable (fun s' ↦ M.bellmanEval γ π v s' - v s') μ :=
    (integrable_of_abs_le (measurable_bellmanEval hv) (abs_bellmanEval_le hR hvB) _).sub
      (integrable_of_abs_le hv hvB _)
  induction n generalizing s with
  | zero =>
    simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq, pow_zero, one_mul,
      Kernel.one_eq_id, Kernel.id_apply]
    rw [integral_dirac' _ s hg.stronglyMeasurable]
  | succ n ih =>
    calc (M.bellmanEval γ π)^[n + 1 + 1] v s - (M.bellmanEval γ π)^[n + 1] v s
        = M.bellmanEval γ π ((M.bellmanEval γ π)^[n + 1] v) s -
            M.bellmanEval γ π ((M.bellmanEval γ π)^[n] v) s := by
          rw [Function.iterate_succ_apply' _ (n + 1), Function.iterate_succ_apply' _ n]
      _ = γ * ∫ s', ((M.bellmanEval γ π)^[n + 1] v s' - (M.bellmanEval γ π)^[n] v s')
            ∂(M.stateKernel π s) := by
          rw [bellmanEval_eq_policyReward_add hR (hm (n + 1)) (hB (n + 1)),
            bellmanEval_eq_policyReward_add hR (hm n) (hB n),
            integral_sub (integrable_of_abs_le (hm (n + 1)) (hB (n + 1)) _)
              (integrable_of_abs_le (hm n) (hB n) _)]
          ring
      _ = γ * ∫ s', (γ : ℝ) ^ n * ∫ s'', (M.bellmanEval γ π v s'' - v s'')
            ∂((M.stateKernel π ^ n) s') ∂(M.stateKernel π s) := by
          simp_rw [ih]
      _ = (γ : ℝ) ^ (n + 1) * ∫ s', (M.bellmanEval γ π v s' - v s')
            ∂((M.stateKernel π ^ (n + 1)) s) := by
          rw [integral_const_mul, pow_succ (M.stateKernel π) n, Kernel.mul_eq_comp,
            Kernel.integral_comp (hgi _)]
          ring

omit [Nonempty 𝓢] in
/-- **Expansion of the iterates of the evaluation operator**: with bounded rewards, the iterates of
the evaluation operator `T_π` of a stationary policy at a bounded measurable `v` are
`T_π^[n] v = v + ∑ k < n, γ ^ k P_π ^ k (T_π v - v)`, where `P_π` is the state kernel of `π`. As
`n → ∞`, this becomes the Newton form `Learning.MDP.value_eq_add_tsum` of the value. -/
theorem bellmanEval_iterate_eq_add_sum (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v)
    (hvB : ∀ s, |v s| ≤ B) (n : ℕ) (s : 𝓢) :
    (M.bellmanEval γ π)^[n] v s = v s + ∑ k ∈ Finset.range n, (γ : ℝ) ^ k *
      ∫ s', (M.bellmanEval γ π v s' - v s') ∂((M.stateKernel π ^ k) s) := by
  have h := Finset.sum_range_sub (fun k ↦ (M.bellmanEval γ π)^[k] v s) n
  simp only [bellmanEval_iterate_succ_sub hR hv hvB, Function.iterate_zero, id_eq] at h
  rw [h]
  ring

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

/-- **Comparison with a subsolution** [P, Theorem 6.2.2 (b)]: with bounded rewards and `γ < 1`,
a bounded measurable `v` with `v ≤ r_π + γ P_π v` is at most the value of the stationary
policy `π`. -/
theorem le_value_of_le_bellmanEval (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hle : v ≤ M.bellmanEval γ π v) :
    v ≤ M.value γ π := fun s ↦ by
  rw [value_eq_add_tsum hγ hR hv hvB s, le_add_iff_nonneg_right]
  exact tsum_nonneg fun n ↦ mul_nonneg (by positivity)
    (integral_nonneg fun s' ↦ sub_nonneg.2 (hle s'))

/-- **Policy improvement**: with bounded rewards and `γ < 1`, if a bounded measurable `v`
satisfies `v ≤ T_π v`, where `T_π` is the evaluation operator of the stationary policy `π`, then
`T_π v ≤ v^π`. -/
theorem bellmanEval_le_value (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B) (hle : v ≤ M.bellmanEval γ π v) :
    M.bellmanEval γ π v ≤ M.value γ π :=
  (bellmanEval_mono hR hv hvB (measurable_value hγ hR) (abs_value_le hγ hR)
    (le_value_of_le_bellmanEval hγ hR hv hvB hle)).trans_eq (bellmanEval_value hγ hR)

/-- **Comparison with a subsolution** [P, Theorem 6.2.2 (b)]: with finitely many actions, bounded
rewards and `γ < 1`, a bounded measurable `v` with `v ≤ T v` is at most the optimal value, where
`T` is the Bellman optimality operator. The value of the policy greedy for `v` already
dominates `v`. -/
theorem le_optValue_of_le_bellman [Finite 𝓐] [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (hle : v ≤ M.bellman γ v) :
    v ≤ M.optValue γ := fun s ↦ by
  have := Fintype.ofFinite 𝓐
  rw [← bellmanEval_greedy hv] at hle
  exact (le_value_of_le_bellmanEval hγ hR hv hvB hle s).trans (value_le_optValue hγ hR s)

/-- **Uniqueness in the optimality equation** [P, Theorem 6.2.2 (c)]: with finitely many actions,
bounded rewards and `γ < 1`, a bounded measurable solution `v` of `T v = v` is the optimal value,
where `T` is the Bellman optimality operator. -/
theorem eq_optValue_of_bellman_eq [Finite 𝓐] [Nonempty 𝓐] (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hv : Measurable v) (hvB : ∀ s, |v s| ≤ B)
    (h : M.bellman γ v = v) :
    v = M.optValue γ :=
  le_antisymm (le_optValue_of_le_bellman hγ hR hv hvB h.ge)
    (optValue_le_of_bellman_le hγ hR hv hvB h.le)

end Subsolution

end Learning.MDP
