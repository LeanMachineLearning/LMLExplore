/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.Bellman
public import LMLExplore.MarkovDecisionProcess.MarkovPolicy
public import LMLExplore.MeasureTheory.Integral.DominatedConvergence
public import LMLExplore.SequentialLearning.Algorithm

/-!
# Values of the runs of an algorithm in a Markov decision process

Every algorithm `alg : Algorithm 𝓢 𝓐 ℝ` is a history-dependent policy of an MDP `M`. Run in the
environment `M.env μ` from the initial law `μ`, it collects the mean rewards
`r (S n, A n) = meanReward M.R (S n, A n)` along its state-action trajectory. This file defines
* its discounted value `M.runValue γ alg μ`, the expectation of `∑' n, γ ^ n * r (S n, A n)`
  under the trajectory measure `trajMeasure alg (M.env μ)`;
* its `N`-step return with discount `γ` and terminal reward `u`, `M.runReturn γ N u alg μ`, the
  expectation of `∑ n < N, γ ^ n * r (S n, A n) + γ ^ N * u (S N)`; the undiscounted return is
  the case `γ = 1`;
* the optimal value `M.optValue γ s`, the supremum of `M.runValue γ alg (dirac s)` over all
  algorithms, and the optimal action value `M.optQValue γ (s, a) = r (s, a) + γ * ∫ v* dP (s, a)`.

These quantities do not depend on the probability space that carries a run: along every run
`IsAlgEnvSeq S A Y alg (M.env μ) P`, the value and the return are the expectations under `P` of
the same sums, and also of the sums with the realized rewards `Y n` in place of their means. They
depend on the run only through the laws of the state-action pairs `(S n, A n)`; for instance the
value is `∑' n, γ ^ n * ∫ r d law (S n, A n)`. For a Markov policy `π`, these laws are the
marginals `stateMarginal (fun _ ↦ M.P) π μ n ⊗ₘ π n`, which gives the value and the return of
`π` in closed form.

With rewards bounded by `C` and `γ < 1`, the value of every algorithm, and the optimal value, are
bounded by `C / (1 - γ)` in absolute value.

## Main definitions

* `Learning.MDP.runValue M γ alg μ`: the discounted value of the algorithm `alg` from `μ`.
* `Learning.MDP.runReturn M γ N u alg μ`: the `N`-step return of `alg` from `μ`, with discount
  `γ` and terminal reward `u`.
* `Learning.MDP.optValue M γ s`: the optimal discounted value at the state `s`.
* `Learning.MDP.optQValue M γ p`: the optimal action value at the state-action pair `p`.

## Main statements

For every run `IsAlgEnvSeq S A Y alg (M.env μ) P` with rewards bounded by `C`, and `γ < 1`:
* `Learning.MDP.runValue_eq_tsum`: `M.runValue γ alg μ = ∑' n, γ ^ n * ∫ r d law (S n, A n)`;
* `Learning.MDP.runValue_eq_integral`, `Learning.MDP.runValue_eq_integral_feedback`: the value
  is the expectation of `∑' n, γ ^ n * r (S n, A n)`, and that of `∑' n, γ ^ n * Y n`;
* `Learning.MDP.runReturn_eq_sum`, `Learning.MDP.runReturn_eq_integral`,
  `Learning.MDP.runReturn_eq_integral_feedback`: the same statements for the `N`-step return.

Moreover:
* `Learning.MDP.runValue_markov`, `Learning.MDP.runReturn_markov`: the value and the return of a
  Markov policy `π`, in terms of its state marginals `stateMarginal (fun _ ↦ M.P) π μ n`;
* `Learning.MDP.abs_runValue_le`, `Learning.MDP.abs_optValue_le`: the bound `C / (1 - γ)`;
* `Learning.MDP.abs_runReturn_le`: the bound `(∑ n < N, γ ^ n) * C + γ ^ N * B` on the `N`-step
  return;
* `Learning.MDP.runValue_le_optValue`, `Learning.MDP.optValue_le_iff`: the optimal value at `s`
  is the least upper bound of the values of the algorithms started at `s`.

## References

* [P] M. L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*,
  Wiley, 1994, §4.1 and §5.1.
-/

public section

open MeasureTheory ProbabilityTheory Learning Finset LMLExplore
open scoped NNReal

namespace Learning.MDP

variable {𝓢 𝓐 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐} [Nonempty 𝓢]
  {M : MDP 𝓢 𝓐 ℝ} {γ : ℝ≥0} {C B : ℝ} {N : ℕ} {u : 𝓢 → ℝ}

/-! ### Definitions -/

variable (M γ) in
/-- The discounted value of the algorithm `alg` in the MDP `M` from the initial law `μ`: the
expectation of `∑' n, γ ^ n * r (S n, A n)` under the law of the runs of `alg` in `M.env μ`, where
`r` is the mean reward and `S n`, `A n` are the state and the action of round `n`. -/
noncomputable def runValue (alg : Algorithm 𝓢 𝓐 ℝ) (μ : Measure 𝓢) : ℝ :=
  ∫ ω, ∑' n, (γ : ℝ) ^ n * meanReward M.R (IT.obs n ω, IT.action n ω)
    ∂(trajMeasure alg (M.env μ))

variable (M γ) in
lemma runValue_def (alg : Algorithm 𝓢 𝓐 ℝ) (μ : Measure 𝓢) :
    M.runValue γ alg μ = ∫ ω, ∑' n, (γ : ℝ) ^ n * meanReward M.R (IT.obs n ω, IT.action n ω)
      ∂(trajMeasure alg (M.env μ)) :=
  (rfl)

variable (M γ) in
/-- The `N`-step return of the algorithm `alg` in the MDP `M` from the initial law `μ`, with
discount `γ` and terminal reward `u`: the expectation of
`∑ n < N, γ ^ n * r (S n, A n) + γ ^ N * u (S N)` under the law of the runs of `alg` in
`M.env μ`, where `r` is the mean reward and `S n`, `A n` are the state and the action of round
`n`. The undiscounted return is the case `γ = 1`. -/
noncomputable def runReturn (N : ℕ) (u : 𝓢 → ℝ) (alg : Algorithm 𝓢 𝓐 ℝ) (μ : Measure 𝓢) : ℝ :=
  ∫ ω, (∑ n ∈ range N, (γ : ℝ) ^ n * meanReward M.R (IT.obs n ω, IT.action n ω) +
    (γ : ℝ) ^ N * u (IT.obs N ω)) ∂(trajMeasure alg (M.env μ))

variable (M γ) in
lemma runReturn_def (N : ℕ) (u : 𝓢 → ℝ) (alg : Algorithm 𝓢 𝓐 ℝ) (μ : Measure 𝓢) :
    M.runReturn γ N u alg μ =
      ∫ ω, (∑ n ∈ range N, (γ : ℝ) ^ n * meanReward M.R (IT.obs n ω, IT.action n ω) +
        (γ : ℝ) ^ N * u (IT.obs N ω)) ∂(trajMeasure alg (M.env μ)) :=
  (rfl)

variable (M γ) in
/-- The optimal discounted value `v* s` of the MDP `M` at the state `s`: the supremum over all
algorithms, that is over all history-dependent policies, of their discounted values from `s`. -/
noncomputable def optValue (s : 𝓢) : ℝ :=
  ⨆ alg : Algorithm 𝓢 𝓐 ℝ, M.runValue γ alg (Measure.dirac s)

variable (M γ) in
lemma optValue_def (s : 𝓢) :
    M.optValue γ s = ⨆ alg : Algorithm 𝓢 𝓐 ℝ, M.runValue γ alg (Measure.dirac s) :=
  (rfl)

variable (M γ) in
/-- The optimal action value `Q* (s, a) = r (s, a) + γ * ∫ v* ∂(P (s, a))`: the value of playing
`a` in the state `s`, then collecting the optimal value at the next state. -/
noncomputable def optQValue (p : 𝓢 × 𝓐) : ℝ :=
  meanReward M.R p + γ * ∫ s', M.optValue γ s' ∂(M.P p)

variable (M γ) in
lemma optQValue_def (p : 𝓢 × 𝓐) :
    M.optQValue γ p = meanReward M.R p + γ * ∫ s', M.optValue γ s' ∂(M.P p) :=
  (rfl)

variable (M γ) in
/-- The optimal action value is the one-step lookahead of the optimal value. -/
lemma optQValue_eq_lookahead : M.optQValue γ = M.lookahead γ (M.optValue γ) := by
  ext p
  rw [optQValue_def, lookahead_def]

/-! ### Bounds -/

omit [Nonempty 𝓢] in
/-- With rewards bounded by `C`, the discounted sums of the mean rewards along a trajectory are
bounded by `C / (1 - γ)`. -/
private lemma abs_tsum_meanReward_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (x : ℕ → 𝓢 × 𝓐) :
    |∑' n, (γ : ℝ) ^ n * meanReward M.R (x n)| ≤ C / (1 - γ) := by
  have h_le (n : ℕ) : ‖(γ : ℝ) ^ n * meanReward M.R (x n)‖ ≤ (γ : ℝ) ^ n * C := by
    rw [norm_mul, norm_pow, NNReal.norm_eq]
    gcongr
    exact norm_meanReward_le M.R (hR (x n))
  have h_geom := (hasSum_geometric_of_lt_one γ.coe_nonneg hγ).mul_right C
  rw [← Real.norm_eq_abs, div_eq_inv_mul]
  exact (Summable.of_norm_bounded h_geom.summable h_le).hasSum.norm_le_of_bounded h_geom h_le

/-- With rewards bounded by `C` and `γ < 1`, the discounted value of every algorithm is bounded by
`C / (1 - γ)` in absolute value. -/
theorem abs_runValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (alg : Algorithm 𝓢 𝓐 ℝ) (μ : Measure 𝓢) :
    |M.runValue γ alg μ| ≤ C / (1 - γ) := by
  rw [runValue_def]
  exact abs_integral_le_of_abs_le fun ω ↦
    abs_tsum_meanReward_le hγ hR fun n ↦ (IT.obs n ω, IT.action n ω)

/-- With rewards bounded by `C` and a terminal reward bounded by `B`, the `N`-step return with
discount `γ` of every algorithm is bounded by `(∑ n < N, γ ^ n) * C + γ ^ N * B` in absolute
value. -/
theorem abs_runReturn_le (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu : ∀ s, |u s| ≤ B)
    (alg : Algorithm 𝓢 𝓐 ℝ) (μ : Measure 𝓢) :
    |M.runReturn γ N u alg μ| ≤ (∑ n ∈ range N, (γ : ℝ) ^ n) * C + (γ : ℝ) ^ N * B := by
  rw [runReturn_def]
  refine abs_integral_le_of_abs_le fun ω ↦ (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ ↦ ?_)
    rw [abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    exact norm_meanReward_le M.R (hR (IT.obs n ω, IT.action n ω))
  · rw [abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    exact hu _

/-! ### Values along a run -/

section Runs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {S : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝓢 𝓐 ℝ} {μ : Measure 𝓢}

/-- Along a run in an MDP with rewards bounded by `C`, the expectation of the discounted sum of
the mean rewards is the discounted sum of their expectations. -/
private lemma integral_tsum_meanReward (h : IsAlgEnvSeq S A Y alg (M.env μ) P) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    ∫ ω, ∑' n, (γ : ℝ) ^ n * meanReward M.R (S n ω, A n ω) ∂P =
      ∑' n, (γ : ℝ) ^ n * ∫ p, meanReward M.R p ∂(P.map fun ω ↦ (S n ω, A n ω)) := by
  have hm (n : ℕ) : Measurable fun ω ↦ (S n ω, A n ω) := h.measurable_obs_action n
  have h_tsum := integral_tsum_smul_of_norm_le (μ := P)
    (summable_geometric_of_lt_one γ.coe_nonneg hγ) (C := C)
    (X := fun n ω ↦ meanReward M.R (S n ω, A n ω))
    (fun n ↦ ((measurable_meanReward M.R).comp (hm n)).aestronglyMeasurable)
    (fun n ↦ .of_forall fun ω ↦ norm_meanReward_le M.R (hR (S n ω, A n ω)))
  simp only [smul_eq_mul] at h_tsum
  rw [h_tsum]
  refine tsum_congr fun n ↦ ?_
  rw [integral_map (hm n).aemeasurable (measurable_meanReward M.R).aestronglyMeasurable]

/-- Along a run in an MDP, the expectation of the discounted `N`-step sum of the mean rewards
plus the discounted terminal reward is the discounted sum of their expectations. -/
private lemma integral_sum_meanReward_add (h : IsAlgEnvSeq S A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu_meas : Measurable u) (hu : ∀ s, |u s| ≤ B) :
    ∫ ω, (∑ n ∈ range N, (γ : ℝ) ^ n * meanReward M.R (S n ω, A n ω) +
        (γ : ℝ) ^ N * u (S N ω)) ∂P =
      ∑ n ∈ range N, (γ : ℝ) ^ n * ∫ p, meanReward M.R p ∂(P.map fun ω ↦ (S n ω, A n ω)) +
        (γ : ℝ) ^ N * ∫ s, u s ∂(P.map (S N)) := by
  have hm (n : ℕ) : Measurable fun ω ↦ (S n ω, A n ω) := h.measurable_obs_action n
  have hr (p : 𝓢 × 𝓐) : |meanReward M.R p| ≤ C := norm_meanReward_le M.R (hR p)
  have h_int (n : ℕ) : Integrable (fun ω ↦ meanReward M.R (S n ω, A n ω)) P :=
    integrable_of_abs_le ((measurable_meanReward M.R).comp (hm n)) (fun ω ↦ hr _) P
  have hu_int : Integrable (fun ω ↦ u (S N ω)) P :=
    integrable_of_abs_le (f := fun ω ↦ u (S N ω)) (hu_meas.comp (h.measurable_obs N))
      (fun ω ↦ hu _) P
  rw [integral_add (integrable_finsetSum _ fun n _ ↦ (h_int n).const_mul _)
      (hu_int.const_mul _),
    integral_finsetSum _ fun n _ ↦ (h_int n).const_mul _, integral_const_mul,
    integral_map (h.measurable_obs N).aemeasurable hu_meas.aestronglyMeasurable]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  rw [integral_const_mul,
    integral_map (hm n).aemeasurable (measurable_meanReward M.R).aestronglyMeasurable]

/-- **Marginal formula of the discounted value**: along every run of `alg` in `M.env μ`, with
bounded rewards and `γ < 1`, the discounted value of `alg` is
`∑' n, γ ^ n * ∫ r d law (S n, A n)`. -/
theorem runValue_eq_tsum (h : IsAlgEnvSeq S A Y alg (M.env μ) P) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.runValue γ alg μ =
      ∑' n, (γ : ℝ) ^ n * ∫ p, meanReward M.R p ∂(P.map fun ω ↦ (S n ω, A n ω)) := by
  rw [runValue_def, integral_tsum_meanReward (IT.isAlgEnvSeq_trajMeasure alg (M.env μ)) hγ hR]
  simp_rw [h.map_obs_action]

/-- Along every run of `alg` in `M.env μ`, with bounded rewards and `γ < 1`, the discounted value
of `alg` is the expectation of `∑' n, γ ^ n * r (S n, A n)`. -/
theorem runValue_eq_integral (h : IsAlgEnvSeq S A Y alg (M.env μ) P) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.runValue γ alg μ = ∫ ω, ∑' n, (γ : ℝ) ^ n * meanReward M.R (S n ω, A n ω) ∂P := by
  rw [runValue_eq_tsum h hγ hR, integral_tsum_meanReward h hγ hR]

/-- Along every run of `alg` in `M.env μ`, with bounded rewards and `γ < 1`, the discounted value
of `alg` is the expectation of the discounted sum `∑' n, γ ^ n * Y n` of the realized rewards. -/
theorem runValue_eq_integral_feedback (h : IsAlgEnvSeq S A Y alg (M.env μ) P) (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.runValue γ alg μ = ∫ ω, ∑' n, (γ : ℝ) ^ n * Y n ω ∂P := by
  have h_tsum := integral_tsum_smul_of_norm_le (μ := P)
    (summable_geometric_of_lt_one γ.coe_nonneg hγ) (C := C) (X := Y)
    (fun n ↦ (h.measurable_feedback n).aestronglyMeasurable)
    (ae_abs_feedback_le h hR)
  simp only [smul_eq_mul] at h_tsum
  rw [h_tsum, runValue_eq_tsum h hγ hR]
  simp_rw [integral_feedback h hR]

/-- **Marginal formula of the `N`-step return**: along every run of `alg` in `M.env μ`, with
bounded rewards and a bounded measurable terminal reward `u`, the `N`-step return of `alg` with
discount `γ` is `∑ n < N, γ ^ n * ∫ r d law (S n, A n) + γ ^ N * ∫ u d law (S N)`. -/
theorem runReturn_eq_sum (h : IsAlgEnvSeq S A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu_meas : Measurable u) (hu : ∀ s, |u s| ≤ B) :
    M.runReturn γ N u alg μ =
      ∑ n ∈ range N, (γ : ℝ) ^ n * ∫ p, meanReward M.R p ∂(P.map fun ω ↦ (S n ω, A n ω)) +
        (γ : ℝ) ^ N * ∫ s, u s ∂(P.map (S N)) := by
  rw [runReturn_def, integral_sum_meanReward_add (IT.isAlgEnvSeq_trajMeasure alg (M.env μ)) hR
    hu_meas hu, h.map_obs]
  simp_rw [h.map_obs_action]

/-- Along every run of `alg` in `M.env μ`, with bounded rewards and a bounded measurable terminal
reward `u`, the `N`-step return of `alg` with discount `γ` is the expectation of
`∑ n < N, γ ^ n * r (S n, A n) + γ ^ N * u (S N)`. -/
theorem runReturn_eq_integral (h : IsAlgEnvSeq S A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu_meas : Measurable u) (hu : ∀ s, |u s| ≤ B) :
    M.runReturn γ N u alg μ =
      ∫ ω, (∑ n ∈ range N, (γ : ℝ) ^ n * meanReward M.R (S n ω, A n ω) +
        (γ : ℝ) ^ N * u (S N ω)) ∂P := by
  rw [runReturn_eq_sum h hR hu_meas hu, integral_sum_meanReward_add h hR hu_meas hu]

/-- Along every run of `alg` in `M.env μ`, with bounded rewards and a bounded measurable terminal
reward `u`, the `N`-step return of `alg` with discount `γ` is the expectation of
`∑ n < N, γ ^ n * Y n + γ ^ N * u (S N)`, with the realized rewards `Y n`. -/
theorem runReturn_eq_integral_feedback (h : IsAlgEnvSeq S A Y alg (M.env μ) P)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu_meas : Measurable u) (hu : ∀ s, |u s| ≤ B) :
    M.runReturn γ N u alg μ =
      ∫ ω, (∑ n ∈ range N, (γ : ℝ) ^ n * Y n ω + (γ : ℝ) ^ N * u (S N ω)) ∂P := by
  have h_int (n : ℕ) : Integrable (Y n) P :=
    .of_bound (h.measurable_feedback n).aestronglyMeasurable C
      (ae_abs_feedback_le h hR n)
  have hu_int : Integrable (fun ω ↦ u (S N ω)) P :=
    integrable_of_abs_le (f := fun ω ↦ u (S N ω)) (hu_meas.comp (h.measurable_obs N))
      (fun ω ↦ hu _) P
  rw [integral_add (integrable_finsetSum _ fun n _ ↦ (h_int n).const_mul _)
      (hu_int.const_mul _),
    integral_finsetSum _ fun n _ ↦ (h_int n).const_mul _, integral_const_mul,
    runReturn_eq_sum h hR hu_meas hu,
    integral_map (h.measurable_obs N).aemeasurable hu_meas.aestronglyMeasurable]
  simp_rw [integral_const_mul, integral_feedback h hR]

end Runs

/-! ### Markov policies -/

section Markov

variable {π : ℕ → Kernel 𝓢 𝓐} [∀ n, IsMarkovKernel (π n)] {μ : Measure 𝓢}
  [IsProbabilityMeasure μ]

/-- With bounded rewards and `γ < 1`, the discounted value of the Markov policy `π` from the
probability measure `μ` is `∑' n, γ ^ n * ∫ r d(μₙ ⊗ₘ π n)`, where
`μₙ = stateMarginal (fun _ ↦ M.P) π μ n` is the law of the state of round `n`. -/
theorem runValue_markov (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) :
    M.runValue γ (Algorithm.markov π) μ =
      ∑' n, (γ : ℝ) ^ n *
        ∫ p, meanReward M.R p ∂(stateMarginal (fun _ ↦ M.P) π μ n ⊗ₘ π n) := by
  have h := IT.isAlgEnvSeq_trajMeasure (Algorithm.markov π) (M.env μ)
  rw [runValue_eq_tsum h hγ hR]
  simp_rw [(hasLaw_obs_action_markov h _).map_eq]

/-- With bounded rewards and a bounded measurable terminal reward `u`, the `N`-step return with
discount `γ` of the Markov policy `π` from the probability measure `μ` is
`∑ n < N, γ ^ n * ∫ r d(μₙ ⊗ₘ π n) + γ ^ N * ∫ u dμ_N`, where
`μₙ = stateMarginal (fun _ ↦ M.P) π μ n` is the law of the state of round `n`. -/
theorem runReturn_markov (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (hu_meas : Measurable u)
    (hu : ∀ s, |u s| ≤ B) :
    M.runReturn γ N u (Algorithm.markov π) μ =
      ∑ n ∈ range N, (γ : ℝ) ^ n *
          ∫ p, meanReward M.R p ∂(stateMarginal (fun _ ↦ M.P) π μ n ⊗ₘ π n) +
        (γ : ℝ) ^ N * ∫ s, u s ∂(stateMarginal (fun _ ↦ M.P) π μ N) := by
  have h := IT.isAlgEnvSeq_trajMeasure (Algorithm.markov π) (M.env μ)
  rw [runReturn_eq_sum h hR hu_meas hu, (hasLaw_obs_markov h N).map_eq]
  simp_rw [(hasLaw_obs_action_markov h _).map_eq]

end Markov

/-! ### The optimal value -/

section OptValue

/-- The discounted values of the algorithms started at `s` are bounded above, by `C / (1 - γ)`
for rewards bounded by `C`. -/
private lemma bddAbove_runValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    BddAbove (Set.range fun alg : Algorithm 𝓢 𝓐 ℝ ↦ M.runValue γ alg (Measure.dirac s)) :=
  ⟨C / (1 - γ), Set.forall_mem_range.2 fun alg ↦
    (le_abs_self _).trans (abs_runValue_le hγ hR alg _)⟩

/-- With bounded rewards and `γ < 1`, the discounted value of every algorithm started at `s` is at
most the optimal value at `s`. -/
theorem runValue_le_optValue (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C)
    (alg : Algorithm 𝓢 𝓐 ℝ) (s : 𝓢) :
    M.runValue γ alg (Measure.dirac s) ≤ M.optValue γ s :=
  le_ciSup (bddAbove_runValue hγ hR s) alg

variable [Nonempty 𝓐]

/-- With bounded rewards and `γ < 1`, the optimal value at `s` is at most `c` if and only if the
discounted value of every algorithm started at `s` is at most `c`. -/
theorem optValue_le_iff (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) {s : 𝓢} {c : ℝ} :
    M.optValue γ s ≤ c ↔ ∀ alg : Algorithm 𝓢 𝓐 ℝ, M.runValue γ alg (Measure.dirac s) ≤ c :=
  -- the algorithm playing a fixed action shows that there are algorithms
  have : Nonempty (Algorithm 𝓢 𝓐 ℝ) :=
    ⟨policyAlg (fun _ ↦ Classical.arbitrary 𝓐) measurable_const⟩
  ciSup_le_iff (bddAbove_runValue hγ hR s)

/-- With rewards bounded by `C` and `γ < 1`, the optimal value is bounded by `C / (1 - γ)` in
absolute value. -/
theorem abs_optValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (s : 𝓢) :
    |M.optValue γ s| ≤ C / (1 - γ) := by
  -- the algorithm playing a fixed action is a witness for the lower bound
  let a : 𝓐 := Classical.arbitrary 𝓐
  let alg : Algorithm 𝓢 𝓐 ℝ := policyAlg (fun _ ↦ a) measurable_const
  refine abs_le.2 ⟨?_, (optValue_le_iff hγ hR).2 fun alg ↦
    (le_abs_self _).trans (abs_runValue_le hγ hR alg _)⟩
  exact (neg_le_of_abs_le (abs_runValue_le hγ hR alg _)).trans (runValue_le_optValue hγ hR alg s)

/-- With rewards bounded by `C` and `γ < 1`, the optimal action value is bounded by
`C / (1 - γ)` in absolute value. -/
theorem abs_optQValue_le (hγ : γ < 1) (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (p : 𝓢 × 𝓐) :
    |M.optQValue γ p| ≤ C / (1 - γ) := by
  rw [optQValue_eq_lookahead]
  refine (abs_lookahead_le hR (abs_optValue_le hγ hR) p).trans_eq ?_
  have : (1 - γ : ℝ) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hγ.ne')
  field_simp
  ring

end OptValue

end Learning.MDP
