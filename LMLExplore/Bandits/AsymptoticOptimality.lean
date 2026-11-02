/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

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
`c* = ∑_{a : Δ_a > 0} 2 σ² / Δ_a` [LS, §16.2].

## Main statements

* `UCBF.isConsistent`: `ucbF σ2` is consistent over the σ²-sub-Gaussian bandits, for `σ² ≠ 0`.
* `UCBF.isConsistent_gaussianBandit`: `ucbF σ2` is consistent over the Gaussian bandits with
  variance `σ²`.
* `KLUCB.isConsistent`: `klucb` is consistent over the bandits with rewards in `[0, 1]`.
* `tendsto_ucbF_regret_div_log_gaussianBandit`: on a Gaussian bandit with variance `σ²`, the
  expected regret of `ucbF σ2` satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`.
* `isLittleO_ucbF_regret_sub_mul_log_gaussianBandit`: the same statement in the form
  `E[R_n] = c* log n + o(log n)`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapters 8, 10 and 16.
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset Real Learning Bandits Asymptotics
open scoped NNReal Topology

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

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {μ : α → ℝ}

/-- **Asymptotic optimality of UCB for Gaussian bandits** [LS, §16.2]. On a Gaussian bandit with
variance `σ² ≠ 0`, the expected regret of the asymptotically optimal UCB algorithm `ucbF σ2`
satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`, the Lai–Robbins constant of the Gaussian
bandits with variance `σ²`. -/
theorem tendsto_ucbF_regret_div_log_gaussianBandit (hσ2 : σ2 ≠ 0)
    (h : IsAlgEnvSeq O A R (ucbF σ2) (stationaryEnv (gaussianBandit μ σ2)) P) :
    Tendsto (fun n : ℕ ↦ P[regret (gaussianBandit μ σ2) A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        2 * σ2 / gap (gaussianBandit μ σ2) a)) := by
  have hlog : ∀ᶠ n : ℕ in atTop, 0 < log n :=
    (eventually_gt_atTop 1).mono fun n hn ↦ log_pos (by exact_mod_cast hn)
  refine tendsto_order.mpr ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · -- The Lai–Robbins lower bound, for a constant `c'` between `c` and the sum.
    obtain ⟨c', hcc', hc'⟩ := exists_between hc
    have hlow := eventually_mul_log_le_integral_regret_gaussianBandit hσ2
      (UCBF.isConsistent_gaussianBandit hσ2) μ hc'
    filter_upwards [hlow, hlog] with n hn hn_log
    rw [← h.integral_regret_eq_integral_trajMeasure] at hn
    rw [lt_div_iff₀ hn_log]
    exact (mul_lt_mul_of_pos_right hcc' hn_log).trans_le hn
  · -- The upper bound [LS, (8.2)], for a constant `c'` between the sum and `c`.
    obtain ⟨c', hc', hc'c⟩ := exists_between hc
    filter_upwards [ucbF_regret_eventually_le h (hasSubgaussianMGF_gaussianBandit μ σ2) hσ2 hc',
      hlog] with n hn hn_log
    rw [div_lt_iff₀ hn_log]
    exact hn.trans_lt (mul_lt_mul_of_pos_right hc'c hn_log)

/-- **Asymptotic optimality of UCB for Gaussian bandits** [LS, §16.2]. On a Gaussian bandit with
variance `σ² ≠ 0`, the expected regret of the asymptotically optimal UCB algorithm `ucbF σ2` is
`c* log n + o(log n)`, where `c* = ∑_{a : Δ_a > 0} 2 σ² / Δ_a` is the Lai–Robbins constant of the
Gaussian bandits with variance `σ²`. -/
theorem isLittleO_ucbF_regret_sub_mul_log_gaussianBandit (hσ2 : σ2 ≠ 0)
    (h : IsAlgEnvSeq O A R (ucbF σ2) (stationaryEnv (gaussianBandit μ σ2)) P) :
    (fun n : ℕ ↦ P[regret (gaussianBandit μ σ2) A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        2 * σ2 / gap (gaussianBandit μ σ2) a) * log n) =o[atTop] fun n : ℕ ↦ log n := by
  have hlog : ∀ᶠ n : ℕ in atTop, log n ≠ 0 :=
    (eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne'
  refine (isLittleO_iff_tendsto' (hlog.mono fun n hn h0 ↦ absurd h0 hn)).mpr ?_
  have h_lim := (tendsto_ucbF_regret_div_log_gaussianBandit hσ2 h).sub_const
    (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
      2 * σ2 / gap (gaussianBandit μ σ2) a)
  rw [sub_self] at h_lim
  refine h_lim.congr' (hlog.mono fun n hn ↦ ?_)
  dsimp only
  rw [sub_div, mul_div_cancel_right₀ _ hn]

end LMLExplore.Bandits
