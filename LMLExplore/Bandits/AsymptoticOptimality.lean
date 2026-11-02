/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Asymptotics.Lemmas
public import LMLExplore.Bandits.AsymptoticallyOptimalUCB
public import LMLExplore.Bandits.KLUCB
public import LMLExplore.Bandits.LaiRobbins

/-!
# Consistency and asymptotic optimality of UCB-type algorithms

An algorithm whose expected regret is `O(log n)` on every bandit of a class is consistent over that
class [LS, Definition 16.1]. The asymptotically optimal UCB algorithm `ucbF σ2` [LS, Algorithm 6]
and the KL-UCB algorithm `klucb` [LS, Algorithm 8] have logarithmic regret by [LS, Theorems 8.1 and
10.6], so they are consistent over the σ²-sub-Gaussian bandits and over the bandits with rewards in
`[0, 1]` respectively.

Consistency is the hypothesis of the Lai–Robbins lower bound [LS, Theorem 16.2]. For Gaussian
bandits with variance `σ²`, the Lai–Robbins constant `∑_{a : Δ_a > 0} 2 σ² / Δ_a` is also the
constant of the asymptotic upper bound of `ucbF σ2` [LS, (8.2)], so `ucbF σ2` is asymptotically
optimal on these bandits: its expected regret is `c* log n + o(log n)` with
`c* = ∑_{a : Δ_a > 0} 2 σ² / Δ_a` [LS, §16.2]. Likewise, for Bernoulli bandits with largest mean
`μ*`, the Lai–Robbins constant `∑_{a : Δ_a > 0} Δ_a / d(μ_a, μ*)`, with `d` the binary relative
entropy, is the constant of the asymptotic upper bound of `klucb` [LS, Theorem 10.6], so `klucb` is
asymptotically optimal on these bandits.

## Main statements

* `UCBF.isConsistent`: `ucbF σ2` is consistent over the σ²-sub-Gaussian bandits, for `σ² ≠ 0`.
* `UCBF.isConsistent_gaussianBandit`: `ucbF σ2` is consistent over the Gaussian bandits with
  variance `σ²`.
* `KLUCB.isConsistent`: `klucb` is consistent over the bandits with rewards in `[0, 1]`.
* `tendsto_ucbF_regret_div_log_gaussianBandit`: on a Gaussian bandit with variance `σ²`, the
  expected regret of `ucbF σ2` satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`.
* `isLittleO_ucbF_regret_sub_mul_log_gaussianBandit`: the same statement in the form
  `E[R_n] = c* log n + o(log n)`.
* `KLUCB.isConsistent_bernoulliBandit`: `klucb` is consistent over the Bernoulli bandits.
* `tendsto_klucb_regret_div_log_bernoulliBandit`: on a Bernoulli bandit with means `p`, the
  expected regret of `klucb` satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`.
* `isLittleO_klucb_regret_sub_mul_log_bernoulliBandit`: the same statement in the form
  `E[R_n] = c* log n + o(log n)`.

In the Bernoulli statements, `Δ_a / d(p_a, μ*)` is computed from the real number
`d(p_a, μ*).toReal`, as in `klucb_regret_eventually_le`. For an arm with positive gap it is `0`
exactly when `μ* = 1`, where `d(p_a, 1) = ∞`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapters 8, 10 and 16.
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset Real Learning Bandits Asymptotics
open scoped NNReal Topology unitInterval

namespace LMLExplore.Bandits

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [StandardBorelSpace α] {σ2 : ℝ≥0}

/-- The asymptotically optimal UCB algorithm `ucbF σ2` is consistent over the σ²-sub-Gaussian
bandits, for `σ² ≠ 0`: its expected regret on each of them is `o(n ^ p)` for every `p > 0`. -/
theorem UCBF.isConsistent (hσ2 : σ2 ≠ 0) :
    IsConsistent (ucbF σ2)
      {ν : Kernel α ℝ | ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) σ2 (ν a)} :=
  isConsistent_of_eventually_le_mul_log fun _ hν _ ↦
    ⟨_, ucbF_regret_eventually_le (IT.isAlgEnvSeq_trajMeasure _ _) hν hσ2 (lt_add_one _)⟩

/-- The asymptotically optimal UCB algorithm `ucbF σ2` is consistent over the Gaussian bandits with
variance `σ² ≠ 0`. -/
theorem UCBF.isConsistent_gaussianBandit (hσ2 : σ2 ≠ 0) :
    IsConsistent (ucbF σ2) (Set.range fun μ : α → ℝ ↦ gaussianBandit μ σ2) :=
  (UCBF.isConsistent hσ2).mono <| Set.range_subset_iff.mpr fun μ a ↦
    hasSubgaussianMGF_gaussianBandit μ σ2 a

/-- The KL-UCB algorithm is consistent over the bandits with rewards in `[0, 1]`: its expected
regret on each of them is `o(n ^ p)` for every `p > 0`. -/
theorem KLUCB.isConsistent :
    IsConsistent klucb {ν : Kernel α ℝ | ∀ a, ∀ᵐ x ∂(ν a), x ∈ Set.Icc 0 1} :=
  isConsistent_of_eventually_le_mul_log fun _ hν _ ↦
    ⟨_, klucb_regret_eventually_le (IT.isAlgEnvSeq_trajMeasure _ _) hν (lt_add_one _)⟩

/-- The KL-UCB algorithm is consistent over the Bernoulli bandits. -/
theorem KLUCB.isConsistent_bernoulliBandit :
    IsConsistent klucb (Set.range fun p : α → I ↦ bernoulliBandit p) :=
  KLUCB.isConsistent.mono <| Set.range_subset_iff.mpr fun p a ↦ ae_mem_Icc_bernoulliBandit p a

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {μ : α → ℝ} {p : α → I}

/-- **Asymptotic optimality of UCB for Gaussian bandits** [LS, §16.2]. On a Gaussian bandit with
variance `σ² ≠ 0`, the expected regret of the asymptotically optimal UCB algorithm `ucbF σ2`
satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`, the Lai–Robbins constant of the Gaussian
bandits with variance `σ²`. -/
theorem tendsto_ucbF_regret_div_log_gaussianBandit (hσ2 : σ2 ≠ 0)
    (h : IsAlgEnvSeq O A R (ucbF σ2) (stationaryEnv (gaussianBandit μ σ2)) P) :
    Tendsto (fun n : ℕ ↦ P[regret (gaussianBandit μ σ2) A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        2 * σ2 / gap (gaussianBandit μ σ2) a)) := by
  -- The upper bound is [LS, (8.2)]; the lower bound is the Lai–Robbins lower bound.
  refine tendsto_div_of_eventually_mul_le
    ((eventually_gt_atTop 1).mono fun n hn ↦ log_pos (by exact_mod_cast hn)) (fun c hc ↦ ?_)
    fun c hc ↦ ucbF_regret_eventually_le h (hasSubgaussianMGF_gaussianBandit μ σ2) hσ2 hc
  filter_upwards [eventually_mul_log_le_integral_regret_gaussianBandit hσ2
    (UCBF.isConsistent_gaussianBandit hσ2) μ hc] with n hn
  rwa [← h.integral_regret_eq_integral_trajMeasure] at hn

/-- **Asymptotic optimality of UCB for Gaussian bandits** [LS, §16.2]. On a Gaussian bandit with
variance `σ² ≠ 0`, the expected regret of the asymptotically optimal UCB algorithm `ucbF σ2` is
`c* log n + o(log n)`, where `c* = ∑_{a : Δ_a > 0} 2 σ² / Δ_a` is the Lai–Robbins constant of the
Gaussian bandits with variance `σ²`. -/
theorem isLittleO_ucbF_regret_sub_mul_log_gaussianBandit (hσ2 : σ2 ≠ 0)
    (h : IsAlgEnvSeq O A R (ucbF σ2) (stationaryEnv (gaussianBandit μ σ2)) P) :
    (fun n : ℕ ↦ P[regret (gaussianBandit μ σ2) A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        2 * σ2 / gap (gaussianBandit μ σ2) a) * log n) =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_ucbF_regret_div_log_gaussianBandit hσ2 h)

/-- **Asymptotic optimality of KL-UCB for Bernoulli bandits** [LS, §16.2]. On a Bernoulli bandit
with means `p` and largest mean `μ* = max_b p_b`, the expected regret of the KL-UCB algorithm
satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`, the Lai–Robbins constant of the
Bernoulli bandits. As in `klucb_regret_eventually_le`, the terms are computed from the real number
`d(p_a, μ*).toReal`, so that they vanish when `μ* = 1`. -/
theorem tendsto_klucb_regret_div_log_bernoulliBandit
    (h : IsAlgEnvSeq O A R klucb (stationaryEnv (bernoulliBandit p)) P) :
    Tendsto (fun n : ℕ ↦ P[regret (bernoulliBandit p) A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap (bernoulliBandit p) a),
        gap (bernoulliBandit p) a / (klBer (p a) (⨆ b, (p b : ℝ))).toReal)) := by
  set ν := bernoulliBandit p
  -- The constant of `klucb_regret_eventually_le`, written with the means `p`.
  have hbest : (ν (bestArm ν))[id] = ⨆ b, (p b : ℝ) := by
    have h_gap := gap_eq_bestArm_sub (ν := ν) (a := Classical.arbitrary α)
    simp_rw [gap, ν, integral_id_bernoulliBandit] at h_gap ⊢
    linarith
  have hconst : ∀ a, (klBer (ν a)[id] (ν (bestArm ν))[id]).toReal =
      (klBer (p a) (⨆ b, (p b : ℝ))).toReal := fun a ↦ by
    rw [hbest, integral_id_bernoulliBandit]
  refine tendsto_div_of_eventually_mul_le
    ((eventually_gt_atTop 1).mono fun n hn ↦ log_pos (by exact_mod_cast hn)) (fun c hc ↦ ?_)
    fun c hc ↦ ?_
  · -- The Lai–Robbins lower bound.
    filter_upwards [eventually_mul_log_le_integral_regret_bernoulliBandit
      KLUCB.isConsistent_bernoulliBandit p hc] with n hn
    rwa [← h.integral_regret_eq_integral_trajMeasure] at hn
  · -- The upper bound of [LS, Theorem 10.6].
    simp_rw [← hconst] at hc
    exact klucb_regret_eventually_le h (ae_mem_Icc_bernoulliBandit p) hc

/-- **Asymptotic optimality of KL-UCB for Bernoulli bandits** [LS, §16.2]. On a Bernoulli bandit
with means `p` and largest mean `μ* = max_b p_b`, the expected regret of the KL-UCB algorithm is
`c* log n + o(log n)`, where `c* = ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)` is the Lai–Robbins constant
of the Bernoulli bandits, with the terms computed from `d(p_a, μ*).toReal`. -/
theorem isLittleO_klucb_regret_sub_mul_log_bernoulliBandit
    (h : IsAlgEnvSeq O A R klucb (stationaryEnv (bernoulliBandit p)) P) :
    (fun n : ℕ ↦ P[regret (bernoulliBandit p) A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap (bernoulliBandit p) a),
        gap (bernoulliBandit p) a / (klBer (p a) (⨆ b, (p b : ℝ))).toReal) * log n)
      =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_klucb_regret_div_log_bernoulliBandit h)

end LMLExplore.Bandits
