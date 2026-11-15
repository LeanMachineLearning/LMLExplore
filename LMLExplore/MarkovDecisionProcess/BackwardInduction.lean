/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Logic.Function.Iterate
public import LMLExplore.MarkovDecisionProcess.Comparison

/-!
# Optimality of backward induction in finite horizon

Let `M : MDP 𝓢 𝓐 ℝ` be an MDP with bounded rewards, mean reward `r` and transition kernel `P`, let
`γ ≥ 0` be a discount factor (`γ = 1` gives the undiscounted return), `N` a horizon and `u` a
bounded measurable terminal value. Write `T` for the Bellman optimality operator `M.bellman γ`.
*Backward induction* computes `T^[N] u`; this file proves that it is the optimal `N`-step return
`M.runReturn γ N u alg μ` over all algorithms, that is over all history-dependent policies, and that
Markov deterministic policies attain it, exactly for finitely many actions and up to every `ε > 0`
for countably many.

Everything follows from a finite-horizon telescoping identity. Along every run of every algorithm
in `M.env μ`, with states `S n` and actions `A n`, and for bounded measurable `w n : 𝓢 → ℝ`,

`runReturn γ N (w N) alg μ =
  ∫ w 0 dμ + ∑ n < N, γ ^ n * E[lookahead γ (w (n + 1)) (S n, A n) - w n (S n)]`,

since the expected lookahead of `w (n + 1)` at round `n` is the expected reward of round `n` plus
`γ` times the expectation of `w (n + 1) (S (n + 1))`. With `w n = T^[N - n] u`, every term of the
sum is nonpositive, so no algorithm returns more than `∫ T^[N] u dμ`; no reduction to Markov
policies is needed. For a Markov policy `π`, the expectations are integrals of
`T_{π n} (w (n + 1)) - w n` against the laws of the states, where `T_{π n}` is the evaluation
operator `M.bellmanEval γ (π n)`. This gives
* the policy evaluation formula: the `N`-step return of `π` from `μ` is
  `∫ T_{π 0} (T_{π 1} (⋯ (T_{π (N - 1)} u))) dμ`;
* the lower bound `∫ T^[N] u dμ - ∑ n < N, γ ^ n * ε n` on the return of the Markov deterministic
  policy that plays at round `n` an `ε n`-greedy policy for `T^[N - n - 1] u`;
* hence the characterization of `T^[N] u s` as the supremum of the returns from `s`, through the
  measurable `ε`-greedy policies `M.approxGreedy` for countably many actions, and its attainment
  by the greedy policies `M.greedy` for finitely many.

## Main statements

* `Learning.MDP.runReturn_eq_integral_add_sum`: the telescoping identity along every run;
  `Learning.MDP.runReturn_markov_eq_integral_add_sum`: its form for a Markov policy.
* `Learning.MDP.runReturn_le_integral_of_lookahead_le`: if `lookahead γ (w (n + 1)) (s, a) ≤ w n s`
  for `n < N`, the `N`-step return of every algorithm with terminal value `w N` is at most
  `∫ w 0 dμ`; `Learning.MDP.integral_sub_sum_le_runReturn_markov`: if
  `w n - ε n ≤ T_{π n} (w (n + 1))` for `n < N`, the return of the Markov policy `π` is at least
  `∫ w 0 dμ - ∑ n < N, γ ^ n * ε n`.
* `Learning.MDP.runReturn_markov_eq_integral_foldr`, `Learning.MDP.runReturn_markov_const`:
  policy evaluation [P, §4.2], for Markov and stationary policies.
* `Learning.MDP.runReturn_le_integral_bellman_iterate`: no algorithm returns more than
  `∫ T^[N] u dμ`.
* `Learning.MDP.integral_bellman_iterate_sub_sum_le_runReturn`: the return of a Markov
  deterministic policy `ε n`-greedy for `T^[N - n - 1] u` at round `n` is at least
  `∫ T^[N] u dμ - ∑ n < N, γ ^ n * ε n` [P, Theorem 4.3.4].
* `Learning.MDP.iSup_runReturn_eq_bellman_iterate`: for countably many actions, `T^[N] u s` is the
  supremum of the `N`-step returns of all algorithms from `s` [P, Theorem 4.3.2].
* `Learning.MDP.runReturn_markov_greedy`: for finitely many actions, the Markov deterministic
  policy greedy for `T^[N - n - 1] u` at round `n` attains `∫ T^[N] u dμ` from every initial law
  [P, Theorems 4.3.3, 4.4.2].

## References

* [M. L. Puterman, *Markov Decision Processes*, 1994][P], §4.2, Theorems 4.3.2–4.3.4 and 4.4.2
* [D. P. Bertsekas, *Dynamic Programming and Optimal Control*, Vol. II, 2012][Ber12], Chapter 1
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset LMLExplore
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C B : ℝ} {N : ℕ} {u : 𝓢 → ℝ} {w : ℕ → 𝓢 → ℝ} {K : ℕ → ℝ}
  {μ : Measure 𝓢}

/-! ### The telescoping identity -/

/-- **Finite-horizon telescoping identity**: along every run of `alg` in `M.env μ`, with bounded
rewards and bounded measurable `w n`, the `N`-step return of `alg` with terminal value `w N` is
`∫ w 0 dμ` plus the discounted sum, over the rounds `n < N`, of the expected differences between
the one-step lookahead of `w (n + 1)` and `w n` along the run. -/
theorem runReturn_eq_integral_add_sum {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {S : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ}
    {alg : Algorithm 𝓢 𝓐 ℝ} [IsProbabilityMeasure μ] (h : IsAlgEnvSeq S A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hw : ∀ n, Measurable (w n))
    (hwK : ∀ n s, |w n s| ≤ K n) (N : ℕ) :
    M.runReturn γ N (w N) alg μ = ∫ s, w 0 s ∂μ + ∑ n ∈ range N, (γ : ℝ) ^ n *
      ∫ ω, (M.lookahead γ (w (n + 1)) (S n ω, A n ω) - w n (S n ω)) ∂P := by
  have hm (n : ℕ) : Measurable fun ω ↦ (S n ω, A n ω) := h.measurable_obs_action n
  set a : ℕ → ℝ := fun n ↦ ∫ ω, w n (S n ω) ∂P
  set r : ℕ → ℝ := fun n ↦ ∫ ω, meanReward M.R (S n ω, A n ω) ∂P
  -- the terms of the sum are `γ ^ n * r n + (γ ^ (n + 1) * a (n + 1) - γ ^ n * a n)`
  have hterm (n : ℕ) : (γ : ℝ) ^ n *
      ∫ ω, (M.lookahead γ (w (n + 1)) (S n ω, A n ω) - w n (S n ω)) ∂P =
        (γ : ℝ) ^ n * r n + ((γ : ℝ) ^ (n + 1) * a (n + 1) - (γ : ℝ) ^ n * a n) := by
    rw [integral_lookahead_sub h hR (hw _) (hwK _) (hw n) (hwK n) n]
    ring
  have hret : M.runReturn γ N (w N) alg μ =
      ∑ n ∈ range N, (γ : ℝ) ^ n * r n + (γ : ℝ) ^ N * a N := by
    rw [runReturn_eq_sum h hR (hw N) (hwK N),
      integral_map (h.measurable_obs N).aemeasurable (hw N).aestronglyMeasurable]
    congr 1
    refine sum_congr rfl fun n _ ↦ ?_
    rw [integral_map (hm n).aemeasurable (measurable_meanReward M.R).aestronglyMeasurable]
  have ha0 : a 0 = ∫ s, w 0 s ∂μ :=
    (hasLaw_obs_zero h).integral_comp (hw 0).aestronglyMeasurable
  simp_rw [hterm]
  rw [hret, ← ha0, sum_add_distrib, sum_range_sub (fun n ↦ (γ : ℝ) ^ n * a n), pow_zero, one_mul]
  ring

/-- **Comparison with a supersolution family**: with bounded rewards, if bounded measurable `w n`
satisfy `r (s, a) + γ * ∫ w (n + 1) dP (s, a) ≤ w n s` for all `n < N`, `s` and `a`, then the
`N`-step return with terminal value `w N` of every algorithm from the probability measure `μ` is
at most `∫ w 0 dμ`. -/
theorem runReturn_le_integral_of_lookahead_le [IsProbabilityMeasure μ]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hw : ∀ n, Measurable (w n))
    (hwK : ∀ n s, |w n s| ≤ K n) (hle : ∀ n < N, ∀ p, M.lookahead γ (w (n + 1)) p ≤ w n p.1)
    (alg : Algorithm 𝓢 𝓐 ℝ) :
    M.runReturn γ N (w N) alg μ ≤ ∫ s, w 0 s ∂μ := by
  rw [runReturn_eq_integral_add_sum (IT.isAlgEnvSeq_trajMeasure alg (M.env μ)) hR hw hwK N,
    add_le_iff_nonpos_right]
  exact sum_nonpos fun n hn ↦ mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (integral_nonpos fun _ ↦ sub_nonpos.2 (hle n (mem_range.1 hn) _))

/-! ### Markov policies -/

section Markov

variable {π : ℕ → Kernel 𝓢 𝓐} [∀ n, IsMarkovKernel (π n)] [IsProbabilityMeasure μ]

/-- **Finite-horizon telescoping identity for a Markov policy**: with bounded rewards and bounded
measurable `w n`, the `N`-step return with terminal value `w N` of the Markov policy `π` from `μ` is
`∫ w 0 dμ` plus the discounted sum, over `n < N`, of the integrals of `T_{π n} (w (n + 1)) - w n`
against the law `μₙ = stateMarginal (fun _ ↦ M.P) π μ n` of the state of round `n`, where
`T_{π n}` is the evaluation operator of `π n`. -/
theorem runReturn_markov_eq_integral_add_sum (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hw : ∀ n, Measurable (w n)) (hwK : ∀ n s, |w n s| ≤ K n) (N : ℕ) :
    M.runReturn γ N (w N) (Algorithm.markov π) μ = ∫ s, w 0 s ∂μ +
      ∑ n ∈ range N, (γ : ℝ) ^ n * ∫ s, (M.bellmanEval γ (π n) (w (n + 1)) s - w n s)
        ∂(stateMarginal (fun _ ↦ M.P) π μ n) := by
  have h := IT.isAlgEnvSeq_trajMeasure (Algorithm.markov π) (M.env μ)
  rw [runReturn_eq_integral_add_sum h hR hw hwK N]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  rw [integral_lookahead_sub_markov h hR (hw _) (hwK _) (hw n) (hwK n) n]

/-- With bounded rewards, if bounded measurable `w n` satisfy `w n - ε n ≤ T_{π n} (w (n + 1))` for
all `n < N`, where `T_{π n}` is the evaluation operator of `π n`, then the `N`-step return with
terminal value `w N` of the Markov policy `π` from `μ` is at least
`∫ w 0 dμ - ∑ n < N, γ ^ n * ε n`. -/
theorem integral_sub_sum_le_runReturn_markov (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hw : ∀ n, Measurable (w n)) (hwK : ∀ n s, |w n s| ≤ K n) {ε : ℕ → ℝ}
    (hle : ∀ n < N, ∀ s, w n s - ε n ≤ M.bellmanEval γ (π n) (w (n + 1)) s) :
    ∫ s, w 0 s ∂μ - ∑ n ∈ range N, (γ : ℝ) ^ n * ε n ≤
      M.runReturn γ N (w N) (Algorithm.markov π) μ := by
  rw [runReturn_markov_eq_integral_add_sum hR hw hwK N, sub_eq_add_neg, ← sum_neg_distrib]
  gcongr with n hn
  rw [← mul_neg]
  gcongr
  calc -ε n = ∫ _, -ε n ∂(stateMarginal (fun _ ↦ M.P) π μ n) := by simp
    _ ≤ _ := integral_mono (integrable_const _)
      ((integrable_of_abs_le (measurable_bellmanEval (hw _)) (abs_bellmanEval_le hR (hwK _))
        _).sub (integrable_of_abs_le (hw n) (hwK n) _))
      fun s ↦ by simp only [Pi.sub_apply]; linarith [hle n (mem_range.1 hn) s]

/-- **Policy evaluation in finite horizon**: with bounded rewards, if bounded measurable `w n`
satisfy the backward recursion `T_{π n} (w (n + 1)) = w n` for all `n < N`, where `T_{π n}` is the
evaluation operator of `π n`, then the `N`-step return with terminal value `w N` of the Markov
policy `π` from `μ` is `∫ w 0 dμ`. -/
theorem runReturn_markov_eq_integral_of_bellmanEval_eq (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hw : ∀ n, Measurable (w n)) (hwK : ∀ n s, |w n s| ≤ K n)
    (hev : ∀ n < N, M.bellmanEval γ (π n) (w (n + 1)) = w n) :
    M.runReturn γ N (w N) (Algorithm.markov π) μ = ∫ s, w 0 s ∂μ := by
  rw [runReturn_markov_eq_integral_add_sum hR hw hwK N, add_eq_left]
  exact sum_eq_zero fun n hn ↦ by simp [hev n (mem_range.1 hn)]

/-- **Policy evaluation in finite horizon** [P, §4.2]: with bounded rewards and a bounded
measurable terminal value `u`, the `N`-step return of the Markov policy `π` from `μ` is
`∫ T_{π 0} (T_{π 1} (⋯ (T_{π (N - 1)} u))) dμ`, where `T_{π n}` is the evaluation operator of
`π n`. -/
theorem runReturn_markov_eq_integral_foldr (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hu : Measurable u) (huB : ∀ s, |u s| ≤ B) (N : ℕ) :
    M.runReturn γ N u (Algorithm.markov π) μ =
      ∫ s, (List.range N).foldr (fun n v ↦ M.bellmanEval γ (π n) v) u s ∂μ := by
  -- `W n = T_{π n} (⋯ (T_{π (N - 1)} u))` satisfies the backward recursion of the evaluation
  set W : ℕ → 𝓢 → ℝ := fun n ↦
    (List.range' n (N - n)).foldr (fun n v ↦ M.bellmanEval γ (π n) v) u with hW
  choose K hK using fun n ↦
    exists_abs_foldr_bellmanEval_le (M := M) (γ := γ) (π := π) hR huB (List.range' n (N - n))
  have hev (n : ℕ) (hn : n < N) : M.bellmanEval γ (π n) (W (n + 1)) = W n := by
    simp only [hW, show N - n = N - (n + 1) + 1 by omega, List.range'_succ, List.foldr_cons]
  have h := runReturn_markov_eq_integral_of_bellmanEval_eq (μ := μ) hR
    (fun n ↦ measurable_foldr_bellmanEval hu (List.range' n (N - n))) hK hev
  rwa [Nat.sub_self, List.range'_zero, List.foldr_nil, Nat.sub_zero,
    ← List.range_eq_range'] at h

/-- **Policy evaluation in finite horizon for a stationary policy**: with bounded rewards and a
bounded measurable terminal value `u`, the `N`-step return of the stationary policy `π` from `μ`
is `∫ T_π^[N] u dμ`, where `T_π` is the evaluation operator of `π`. -/
theorem runReturn_markov_const {π : Kernel 𝓢 𝓐} [IsMarkovKernel π]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu : Measurable u) (huB : ∀ s, |u s| ≤ B) (N : ℕ) :
    M.runReturn γ N u (Algorithm.markov fun _ ↦ π) μ = ∫ s, (M.bellmanEval γ π)^[N] u s ∂μ := by
  choose K hK using exists_abs_bellmanEval_iterate_le (M := M) (γ := γ) (π := π) hR huB
  have h := runReturn_markov_eq_integral_of_bellmanEval_eq (π := fun _ ↦ π) (μ := μ)
    (w := fun n ↦ (M.bellmanEval γ π)^[N - n] u) hR
    (fun n ↦ measurable_bellmanEval_iterate hu (N - n)) (fun n ↦ hK (N - n)) (N := N)
    fun n hn ↦ (Function.iterate_sub_eq_apply _ _ hn).symm
  simpa only [Nat.sub_self, Function.iterate_zero, id_eq, Nat.sub_zero] using h

end Markov

/-! ### Optimality of backward induction -/

section Optimality

variable [Countable 𝓐] [Nonempty 𝓐]

/-- **Upper bound of backward induction**: for countably many actions, bounded rewards and a
bounded measurable terminal value `u`, the `N`-step return with discount `γ` of every algorithm
from the probability measure `μ` is at most `∫ T^[N] u dμ`, where `T` is the Bellman optimality
operator. -/
theorem runReturn_le_integral_bellman_iterate [IsProbabilityMeasure μ]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu : Measurable u) (huB : ∀ s, |u s| ≤ B)
    (alg : Algorithm 𝓢 𝓐 ℝ) :
    M.runReturn γ N u alg μ ≤ ∫ s, (M.bellman γ)^[N] u s ∂μ := by
  choose K hK using exists_abs_bellman_iterate_le (M := M) (γ := γ) hR huB
  have h := runReturn_le_integral_of_lookahead_le (μ := μ) (N := N)
    (w := fun n ↦ (M.bellman γ)^[N - n] u) hR (fun n ↦ measurable_bellman_iterate hu (N - n))
    (fun n ↦ hK (N - n)) (fun n hn ⟨s, a⟩ ↦ by
      dsimp only
      rw [Function.iterate_sub_eq_apply _ _ hn]
      exact lookahead_le_bellman (bddAbove_range_lookahead hR (hK _) s) a) alg
  simpa only [Nat.sub_self, Function.iterate_zero, id_eq, Nat.sub_zero] using h

/-- **Return of approximately greedy policies** [P, Theorem 4.3.4]: for countably many actions,
bounded rewards and a bounded measurable terminal value `u`, the Markov deterministic policy that
plays at round `n < N` a measurable policy `d n` which is `ε n`-greedy for `T^[N - n - 1] u` has an
`N`-step return from the probability measure `μ` of at least
`∫ T^[N] u dμ - ∑ n < N, γ ^ n * ε n`, where `T` is the Bellman optimality operator. -/
theorem integral_bellman_iterate_sub_sum_le_runReturn [IsProbabilityMeasure μ]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu : Measurable u) (huB : ∀ s, |u s| ≤ B)
    {ε : ℕ → ℝ} {d : ℕ → 𝓢 → 𝓐} (hd : ∀ n, Measurable (d n))
    (hg : ∀ n < N, M.IsApproxGreedy γ (ε n) ((M.bellman γ)^[N - n - 1] u) (d n)) :
    ∫ s, (M.bellman γ)^[N] u s ∂μ - ∑ n ∈ range N, (γ : ℝ) ^ n * ε n ≤
      M.runReturn γ N u (Algorithm.markov fun n ↦ Kernel.deterministic (d n) (hd n)) μ := by
  choose K hK using exists_abs_bellman_iterate_le (M := M) (γ := γ) hR huB
  have h := integral_sub_sum_le_runReturn_markov (μ := μ) (N := N) (ε := ε)
    (π := fun n ↦ Kernel.deterministic (d n) (hd n)) (w := fun n ↦ (M.bellman γ)^[N - n] u) hR
    (fun n ↦ measurable_bellman_iterate hu (N - n)) (fun n ↦ hK (N - n)) fun n hn s ↦ by
      rw [bellmanEval_deterministic (measurable_bellman_iterate hu _) (hd n),
        Function.iterate_sub_eq_apply _ _ hn]
      simpa only [Nat.sub_sub] using (isApproxGreedy_def M γ _ _ _).1 (hg n hn) s
  simpa only [Nat.sub_self, Function.iterate_zero, id_eq, Nat.sub_zero] using h

/-- **Optimality of backward induction** [P, Theorem 4.3.2]: for countably many actions, bounded
rewards and a bounded measurable terminal value `u`, the supremum over all algorithms of the
`N`-step returns with discount `γ` from the state `s` is `T^[N] u s`, where `T` is the Bellman
optimality operator. The supremum is approached by Markov deterministic policies, through the
measurable `ε`-greedy policies `M.approxGreedy`. -/
theorem iSup_runReturn_eq_bellman_iterate (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (hu : Measurable u) (huB : ∀ s, |u s| ≤ B) (N : ℕ) (s : 𝓢) :
    ⨆ alg : Algorithm 𝓢 𝓐 ℝ, M.runReturn γ N u alg (Measure.dirac s) = (M.bellman γ)^[N] u s := by
  have hint : ∫ s', (M.bellman γ)^[N] u s' ∂(Measure.dirac s) = (M.bellman γ)^[N] u s :=
    integral_dirac' _ s (measurable_bellman_iterate hu N).stronglyMeasurable
  have hle (alg : Algorithm 𝓢 𝓐 ℝ) : M.runReturn γ N u alg (Measure.dirac s) ≤
      (M.bellman γ)^[N] u s :=
    hint ▸ runReturn_le_integral_bellman_iterate hR hu huB alg
  have : Nonempty (Algorithm 𝓢 𝓐 ℝ) :=
    ⟨policyAlg (fun _ ↦ Classical.arbitrary 𝓐) measurable_const⟩
  refine le_antisymm (ciSup_le hle) (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  -- the Markov policy playing `δ`-greedy policies is `(∑ n < N, γ ^ n) * δ`-optimal
  set c : ℝ := ∑ n ∈ range N, (γ : ℝ) ^ n
  have hc : 0 ≤ c := sum_nonneg fun n _ ↦ by positivity
  set δ : ℝ := ε / (c + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hcδ : c * δ ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  set d : ℕ → 𝓢 → 𝓐 := fun n ↦ M.approxGreedy γ δ ((M.bellman γ)^[N - n - 1] u)
  have hd (n : ℕ) : Measurable (d n) := measurable_approxGreedy (measurable_bellman_iterate hu _)
  have h := integral_bellman_iterate_sub_sum_le_runReturn (μ := Measure.dirac s) (ε := fun _ ↦ δ)
    hR hu huB hd fun n _ ↦ isApproxGreedy_approxGreedy hδ _
  rw [hint, ← sum_mul] at h
  calc (M.bellman γ)^[N] u s
      ≤ M.runReturn γ N u (Algorithm.markov fun n ↦ Kernel.deterministic (d n) (hd n))
          (Measure.dirac s) + c * δ := by linarith
    _ ≤ (⨆ alg : Algorithm 𝓢 𝓐 ℝ, M.runReturn γ N u alg (Measure.dirac s)) + ε :=
      add_le_add (le_ciSup ⟨_, Set.forall_mem_range.2 hle⟩ _) hcδ

end Optimality

/-- **Optimality of the greedy policies** [P, Theorems 4.3.3, 4.4.2]: for finitely many actions,
bounded rewards and a bounded measurable terminal value `u`, the Markov deterministic policy that
plays at round `n` the policy greedy for `T^[N - n - 1] u` attains the optimal `N`-step return
`∫ T^[N] u dμ` from every probability measure `μ`, where `T` is the Bellman optimality
operator. -/
theorem runReturn_markov_greedy [Fintype 𝓐] [Nonempty 𝓐] [IsProbabilityMeasure μ]
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu : Measurable u) (huB : ∀ s, |u s| ≤ B) :
    M.runReturn γ N u (Algorithm.markov fun n ↦ Kernel.deterministic
        (M.greedy γ ((M.bellman γ)^[N - n - 1] u))
        (measurable_greedy (measurable_bellman_iterate hu _))) μ =
      ∫ s, (M.bellman γ)^[N] u s ∂μ := by
  refine le_antisymm (runReturn_le_integral_bellman_iterate hR hu huB _) ?_
  have h := integral_bellman_iterate_sub_sum_le_runReturn (μ := μ) (N := N) (γ := γ)
    (ε := fun _ ↦ 0) hR hu huB (fun n ↦ measurable_greedy (measurable_bellman_iterate hu _))
    fun n _ ↦ isApproxGreedy_greedy _
  simpa using h

end Learning.MDP
