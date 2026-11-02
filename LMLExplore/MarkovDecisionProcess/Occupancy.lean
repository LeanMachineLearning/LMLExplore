/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.MarkovDecisionProcess.RunValue

/-!
# Discounted occupancy measures of a Markov decision process

Every algorithm `alg : Algorithm 𝓢 𝓐 𝓡`, run in the environment `M.env μ` of an MDP `M` from the
initial law `μ`, visits the state-action pairs `(S n, A n)`. Its discounted state-action occupancy
measure is
`M.occupancy γ alg μ = (1 - γ) • ∑ n, γ ^ n • law (S n, A n)`,
a probability measure on `𝓢 × 𝓐` for `γ < 1`. It summarizes the run for every discounted
criterion: for `γ < 1` and bounded real rewards, the discounted value of `alg` is
`(1 - γ)⁻¹ * ∫ r d(M.occupancy γ alg μ)`, where `r` is the mean reward. For a probability measure
`μ`, its first marginal satisfies the flow equation
`x (B ×ˢ univ) = (1 - γ) * μ B + γ * ∫⁻ p, M.P p B ∂x`,
which expresses that the law of the state of round `n + 1` is the law of the state-action pair of
round `n` composed with the transition kernel. Occupancy measures turn statements about runs into
statements about measures on `𝓢 × 𝓐`: they are the variables of the linear programs of discounted
MDPs, and the performance difference lemma is an integral against them.

The occupancy measure depends on the run only through the laws of the pairs `(S n, A n)`, so it
can be computed along every run `IsAlgEnvSeq S A Y alg (M.env μ) P`, and for a Markov policy `π`
from its marginals `M.stateMarginal π μ n ⊗ₘ π n`.

## Main definitions

* `Learning.MDP.occupancy M γ alg μ`: the discounted state-action occupancy measure of `alg`.

## Main statements

* `Learning.MDP.occupancy_eq_sum`, `Learning.MDP.integral_occupancy`: along every run, the
  occupancy measure is `(1 - γ) • ∑ n, γ ^ n • law (S n, A n)`, and the integral of an integrable
  function `f` against it is `(1 - γ) * ∑' n, γ ^ n * ∫ f d law (S n, A n)`;
* `Learning.MDP.isProbabilityMeasure_occupancy`: for `γ < 1`, the occupancy measure is a
  probability measure;
* `Learning.MDP.runValue_eq_integral_occupancy`: for `γ < 1` and bounded real rewards, the
  discounted value of `alg` is `(1 - γ)⁻¹ * ∫ r d(M.occupancy γ alg μ)`;
* `Learning.MDP.occupancy_map_fst`, `Learning.MDP.occupancy_prod_univ`: the flow equation, for a
  probability measure `μ`;
* `Learning.MDP.occupancy_markov`, `Learning.MDP.occupancy_markov_const`: the occupancy measures
  of Markov and stationary policies, in terms of their state-action marginals.

## References

* [P] M. L. Puterman, *Markov Decision Processes: Discrete Stochastic Dynamic Programming*,
  Wiley, 1994, §6.9.
* [AJKS] A. Agarwal, N. Jiang, S. M. Kakade, W. Sun, *Reinforcement Learning: Theory and
  Algorithms*, 2022, §1.5.
-/

public section

open MeasureTheory ProbabilityTheory Learning Set LMLExplore
open scoped NNReal ENNReal

namespace Learning.MDP

variable {𝓢 𝓐 𝓡 : Type*} {m𝓢 : MeasurableSpace 𝓢} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓡 : MeasurableSpace 𝓡} [Nonempty 𝓢] {M : MDP 𝓢 𝓐 𝓡} {γ : ℝ≥0} {C : ℝ}

/-! ### Definition -/

variable (M γ) in
/-- The discounted state-action occupancy measure of the algorithm `alg` in the MDP `M` from the
initial law `μ`: `(1 - γ) • ∑ n, γ ^ n • law (S n, A n)`, where `S n` and `A n` are the state and
the action of round `n` of the runs of `alg` in `M.env μ`. For `γ < 1` it is a probability
measure. -/
noncomputable def occupancy (alg : Algorithm 𝓢 𝓐 𝓡) (μ : Measure 𝓢) : Measure (𝓢 × 𝓐) :=
  (1 - γ : ℝ≥0∞) • Measure.sum fun n ↦ (γ : ℝ≥0∞) ^ n •
    (trajMeasure alg (M.env μ)).map fun ω ↦ (IT.obs n ω, IT.action n ω)

variable (M γ) in
lemma occupancy_def (alg : Algorithm 𝓢 𝓐 𝓡) (μ : Measure 𝓢) :
    M.occupancy γ alg μ = (1 - γ : ℝ≥0∞) • Measure.sum fun n ↦ (γ : ℝ≥0∞) ^ n •
      (trajMeasure alg (M.env μ)).map fun ω ↦ (IT.obs n ω, IT.action n ω) :=
  (rfl)

/-! ### Occupancy measures along a run -/

section Runs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {S : ℕ → Ω → 𝓢} {A : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓡} {alg : Algorithm 𝓢 𝓐 𝓡} {μ : Measure 𝓢}

/-- Along every run of `alg` in `M.env μ`, the occupancy measure of `alg` is
`(1 - γ) • ∑ n, γ ^ n • law (S n, A n)`. -/
theorem occupancy_eq_sum (h : IsAlgEnvSeq S A Y alg (M.env μ) P) :
    M.occupancy γ alg μ = (1 - γ : ℝ≥0∞) • Measure.sum fun n ↦ (γ : ℝ≥0∞) ^ n •
      P.map fun ω ↦ (S n ω, A n ω) := by
  simp_rw [occupancy_def, h.map_obs_action]

/-- Along every run of `alg` in `M.env μ`, the occupancy measure of `alg` gives to a measurable
set `s` the mass `(1 - γ) * ∑' n, γ ^ n * P ((S n, A n) ∈ s)`. -/
theorem occupancy_apply (h : IsAlgEnvSeq S A Y alg (M.env μ) P) {s : Set (𝓢 × 𝓐)}
    (hs : MeasurableSet s) :
    M.occupancy γ alg μ s =
      (1 - γ : ℝ≥0∞) * ∑' n, (γ : ℝ≥0∞) ^ n * P ((fun ω ↦ (S n ω, A n ω)) ⁻¹' s) := by
  rw [occupancy_eq_sum h, Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ hs]
  congr 1
  refine tsum_congr fun n ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply ((h.measurable_obs n).prodMk (h.measurable_action n)) hs]

/-- Along every run of `alg` in `M.env μ`, for `γ < 1`, the integral of a function `f` integrable
against the occupancy measure is `(1 - γ) * ∑' n, γ ^ n * ∫ f d law (S n, A n)`. -/
theorem integral_occupancy (h : IsAlgEnvSeq S A Y alg (M.env μ) P) (hγ : γ < 1)
    {f : 𝓢 × 𝓐 → ℝ} (hf : Integrable f (M.occupancy γ alg μ)) :
    ∫ p, f p ∂(M.occupancy γ alg μ) =
      (1 - γ) * ∑' n, (γ : ℝ) ^ n * ∫ p, f p ∂(P.map fun ω ↦ (S n ω, A n ω)) := by
  have h0 : (1 - γ : ℝ≥0∞) ≠ 0 := (tsub_pos_of_lt (by exact_mod_cast hγ)).ne'
  rw [occupancy_eq_sum h] at hf ⊢
  rw [integral_smul_measure, integral_sum_measure
      ((integrable_smul_measure h0 (ENNReal.sub_ne_top ENNReal.one_ne_top)).1 hf)]
  simp [integral_smul_measure, ENNReal.toReal_sub_of_le (ENNReal.coe_le_one_iff.2 hγ.le)]

end Runs

section Measure

variable {alg : Algorithm 𝓢 𝓐 𝓡} {μ : Measure 𝓢}

/-- The mass of the occupancy measure. -/
private lemma occupancy_univ :
    M.occupancy γ alg μ univ = (1 - γ : ℝ≥0∞) * (1 - γ : ℝ≥0∞)⁻¹ := by
  rw [occupancy_apply (IT.isAlgEnvSeq_trajMeasure alg (M.env μ)) MeasurableSet.univ]
  simp [ENNReal.tsum_geometric]

/-- For `γ < 1`, the occupancy measure of every algorithm is a probability measure. -/
theorem isProbabilityMeasure_occupancy (hγ : γ < 1) :
    IsProbabilityMeasure (M.occupancy γ alg μ) := by
  refine ⟨?_⟩
  rw [occupancy_univ]
  refine ENNReal.mul_inv_cancel ?_ ?_
  · exact (tsub_pos_of_lt (by exact_mod_cast hγ)).ne'
  · exact ENNReal.sub_ne_top ENNReal.one_ne_top

/-- The occupancy measure is finite: a probability measure for `γ < 1`, and zero otherwise. -/
instance : IsFiniteMeasure (M.occupancy γ alg μ) := by
  by_cases hγ : γ < 1
  · have := isProbabilityMeasure_occupancy (M := M) (alg := alg) (μ := μ) hγ
    infer_instance
  · -- for `1 ≤ γ`, the factor `1 - γ` vanishes
    have h0 : (1 - γ : ℝ≥0∞) = 0 := by simpa [tsub_eq_zero_iff_le, not_lt] using hγ
    rw [occupancy_def, h0, zero_smul]
    infer_instance

end Measure

/-! ### The value as an integral against the occupancy measure -/

/-- **The value as an integral against the occupancy measure**: with bounded rewards and `γ < 1`,
the discounted value of every algorithm is `(1 - γ)⁻¹ * ∫ r d(M.occupancy γ alg μ)`, where `r` is
the mean reward. -/
theorem runValue_eq_integral_occupancy {M : MDP 𝓢 𝓐 ℝ} (hγ : γ < 1)
    (hR : ∀ p, ∀ᵐ x ∂(M.R p), |x| ≤ C) (alg : Algorithm 𝓢 𝓐 ℝ) (μ : Measure 𝓢) :
    M.runValue γ alg μ = (1 - γ : ℝ)⁻¹ * ∫ p, meanReward M.R p ∂(M.occupancy γ alg μ) := by
  have h := IT.isAlgEnvSeq_trajMeasure alg (M.env μ)
  have h0 : (1 - γ : ℝ) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hγ.ne')
  rw [integral_occupancy h hγ (integrable_of_abs_le (measurable_meanReward M.R)
      (fun p ↦ norm_meanReward_le M.R (hR p)) _), inv_mul_cancel_left₀ h0,
    runValue_eq_tsum h hγ hR]

/-! ### The flow equation -/

section Flow

variable {alg : Algorithm 𝓢 𝓐 𝓡} {μ : Measure 𝓢} [IsProbabilityMeasure μ]

/-- **The flow equation** of occupancy measures: the first marginal of the occupancy measure `x`
of every algorithm from the probability measure `μ` is `(1 - γ) • μ + γ • (M.P ∘ₘ x)`. -/
theorem occupancy_map_fst :
    (M.occupancy γ alg μ).map Prod.fst =
      (1 - γ : ℝ≥0∞) • μ + (γ : ℝ≥0∞) • (M.P ∘ₘ M.occupancy γ alg μ) := by
  have h := IT.isAlgEnvSeq_trajMeasure alg (M.env μ)
  ext B hB
  -- both sides are `(1 - γ)` times discounted sums of the laws of the states
  have h_lhs : (M.occupancy γ alg μ).map Prod.fst B =
      (1 - γ : ℝ≥0∞) * ∑' n, (γ : ℝ≥0∞) ^ n * trajMeasure alg (M.env μ) (IT.obs n ⁻¹' B) := by
    rw [Measure.map_apply measurable_fst hB, occupancy_apply h (measurable_fst hB)]
    simp only [preimage_preimage]
  have h_comp : (M.P ∘ₘ M.occupancy γ alg μ) B =
      (1 - γ : ℝ≥0∞) *
        ∑' n, (γ : ℝ≥0∞) ^ n * trajMeasure alg (M.env μ) (IT.obs (n + 1) ⁻¹' B) := by
    rw [occupancy_def, Measure.comp_smul, Measure.bind_sum _ _ M.P.aemeasurable,
      Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ hB]
    congr 1
    refine tsum_congr fun n ↦ ?_
    rw [Measure.comp_smul, Measure.smul_apply, smul_eq_mul, ← (hasLaw_obs_add_one h n).map_eq,
      Measure.map_apply (IT.measurable_obs _) hB]
  have h_zero : μ B = trajMeasure alg (M.env μ) (IT.obs 0 ⁻¹' B) := by
    rw [← Measure.map_apply (IT.measurable_obs 0) hB, (hasLaw_obs_zero h).map_eq]
  rw [h_lhs, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    h_comp, h_zero, tsum_eq_zero_add' ENNReal.summable]
  simp_rw [pow_succ', mul_assoc, ENNReal.tsum_mul_left]
  ring

/-- **The flow equation** of occupancy measures, setwise: the occupancy measure `x` of every
algorithm from the probability measure `μ` satisfies, for every measurable set `B` of states,
`x (B ×ˢ univ) = (1 - γ) * μ B + γ * ∫⁻ p, M.P p B ∂x`. -/
theorem occupancy_prod_univ {B : Set 𝓢} (hB : MeasurableSet B) :
    M.occupancy γ alg μ (B ×ˢ univ) =
      (1 - γ : ℝ≥0∞) * μ B + γ * ∫⁻ p, M.P p B ∂(M.occupancy γ alg μ) := by
  rw [← Measure.bind_apply hB M.P.aemeasurable, prod_univ, ← Measure.map_apply measurable_fst hB,
    occupancy_map_fst, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
    smul_eq_mul]

end Flow

/-! ### Markov policies -/

section Markov

variable {μ : Measure 𝓢} [IsProbabilityMeasure μ]

/-- The occupancy measure of the Markov policy `π` from the probability measure `μ` is
`(1 - γ) • ∑ n, γ ^ n • (μₙ ⊗ₘ π n)`, where `μₙ = M.stateMarginal π μ n` is the law of the
state of round `n`. -/
theorem occupancy_markov {π : ℕ → Kernel 𝓢 𝓐} [∀ n, IsMarkovKernel (π n)] :
    M.occupancy γ (Algorithm.markov π) μ = (1 - γ : ℝ≥0∞) • Measure.sum fun n ↦
      (γ : ℝ≥0∞) ^ n • (M.stateMarginal π μ n ⊗ₘ π n) := by
  have h := IT.isAlgEnvSeq_trajMeasure (Algorithm.markov π) (M.env μ)
  simp_rw [occupancy_eq_sum h, (hasLaw_obs_action_markov h _).map_eq]

/-- The occupancy measure of the stationary policy `π` from the probability measure `μ` is
`(1 - γ) • ∑ n, γ ^ n • ((M.saKernel π ^ n) ∘ₘ (μ ⊗ₘ π))`, a discounted sum of the laws of the
state-action Markov chain of `π`. -/
theorem occupancy_markov_const {π : Kernel 𝓢 𝓐} [IsMarkovKernel π] :
    M.occupancy γ (Algorithm.markov fun _ ↦ π) μ = (1 - γ : ℝ≥0∞) • Measure.sum fun n ↦
      (γ : ℝ≥0∞) ^ n • ((M.saKernel π ^ n : Kernel (𝓢 × 𝓐) (𝓢 × 𝓐)) ∘ₘ (μ ⊗ₘ π)) := by
  simp_rw [occupancy_markov, stateMarginal_const_compProd]

end Markov

end Learning.MDP
