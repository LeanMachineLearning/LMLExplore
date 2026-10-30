/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.Online.Bandit.Algorithms.Regret.UCB
public import LMLExplore.Bandits.Regret

/-!
# Gap-free regret bound for UCB

LML proves a gap-dependent bound on the expected regret of its UCB algorithm `ucbAlgorithm K c`
for σ²-sub-Gaussian rewards and `c > 2 σ²` (`Bandits.UCB.regret_le_of_gt_two'`), which blows up
when some gap is small. This file proves the gap-free (minimax) bound
`2 √(8 c K n log (n + 1)) + (4 + 2 σ² / (c - 2 σ²)) ∑ a, Δ_a` at horizon `n`, the analogue of
[LS, Theorem 7.2] for LML's index `μ̂_a + √(2 c log (n + 1) / T_a)`.

## Main statements

* `UCB.expectation_pullCount_le_of_gt_two`: the bound
  `8 c log (n + 1) / Δ_a ^ 2 + 4 + 2 σ² / (c - 2 σ²)` on the expected number of pulls of an arm
  with positive gap `Δ_a`.
* `ucb_regret_le_sqrt`: the gap-free regret bound.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Learning Bandits

open scoped NNReal

namespace LMLExplore.Bandits

variable {K : ℕ} [NeZero K] {c : ℝ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ} {σ2 : ℝ≥0}

/-- For σ²-sub-Gaussian rewards and `c > 2 σ²`, the UCB algorithm `ucbAlgorithm K c` pulls an arm
`a` with positive gap `Δ_a` at most `8 c log (n + 1) / Δ_a ^ 2 + 4 + 2 σ² / (c - 2 σ²)` times in
expectation during the first `n` rounds. -/
theorem UCB.expectation_pullCount_le_of_gt_two
    (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0)
    (hc : 2 * σ2 < c) (a : Fin K) (h_gap : 0 < gap ν a) (n : ℕ) :
    P[fun ω ↦ (pullCount A a n ω : ℝ)] ≤
      8 * c * log (n + 1) / gap ν a ^ 2 + (4 + 2 * σ2 / (c - 2 * σ2)) := by
  -- LML's bound is stated for the exploration constant `c' * σ2`, with `c' = c / σ2 > 2`.
  have hσ2' : (0 : ℝ) < σ2 := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hσ2)
  have h' : IsAlgEnvSeq O A R (ucbAlgorithm K (c / σ2 * σ2)) (stationaryEnv ν) P := by
    rwa [div_mul_cancel₀ _ hσ2'.ne']
  have hc' : 2 < c / σ2 := by rwa [lt_div_iff₀ hσ2']
  refine (UCB.expectation_pullCount_le h' hν hσ2 (by linarith) a h_gap n).trans ?_
  have h_const : 2 + 2 * UCB.constSum (c / σ2) n ≤ 4 + 2 / (c / σ2 - 2) := by
    rw [show (4 : ℝ) + 2 / (c / σ2 - 2) = 2 + 2 * (1 + 1 / (c / σ2 - 2)) by ring]
    gcongr
    exact UCB.constSum_le hc' n
  have h_eq : 2 / (c / σ2 - 2) = 2 * σ2 / (c - 2 * σ2) := by
    have : c - 2 * σ2 ≠ 0 := by linarith
    field_simp
  rw [show (8 : ℝ) * (c / σ2) * σ2 = 8 * c by rw [mul_assoc, div_mul_cancel₀ _ hσ2'.ne'],
    ← h_eq]
  linarith

/-- **Gap-free regret bound for UCB**, the analogue of [LS, Theorem 7.2]. For σ²-sub-Gaussian
rewards and `c > 2 σ²`, the expected regret of the UCB algorithm `ucbAlgorithm K c` at horizon `n`
is at most `2 √(8 c K n log (n + 1)) + (4 + 2 σ² / (c - 2 σ²)) ∑ a, Δ_a`. -/
theorem ucb_regret_le_sqrt (h : IsAlgEnvSeq O A R (ucbAlgorithm K c) (stationaryEnv ν) P)
    (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)) (hσ2 : σ2 ≠ 0)
    (hc : 2 * σ2 < c) (n : ℕ) :
    P[regret ν A n] ≤
      2 * √(8 * c * K * n * log (n + 1)) + (4 + 2 * σ2 / (c - 2 * σ2)) * ∑ a, gap ν a := by
  have hc_pos : 0 < c := lt_of_le_of_lt (by positivity) hc
  have h_log : 0 ≤ log (n + 1) := log_nonneg (by simp)
  have h_denom : 0 < c - 2 * σ2 := by linarith
  have h_bound := integral_regret_le_two_mul_sqrt_add_of_forall_integral_pullCount_le
    h.measurable_action (by positivity) (add_nonneg (by norm_num) (by positivity))
    fun a h_gap ↦ UCB.expectation_pullCount_le_of_gt_two h hν hσ2 hc a h_gap n
  rwa [Fintype.card_fin, show 8 * c * log (n + 1) * K * n = 8 * c * K * n * log (n + 1) by ring]
    at h_bound

end LMLExplore.Bandits
