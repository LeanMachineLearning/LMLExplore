/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Asymptotics.Lemmas
public import LMLExplore.Bandits.AsymptoticallyOptimalUCB
public import LMLExplore.Bandits.KLUCB
public import LMLExplore.Bandits.LaiRobbins
public import LMLExplore.Bandits.ThompsonSampling.Gaussian
public import LMLExplore.Bandits.ThompsonSampling.Optimality

/-!
# Consistency and asymptotic optimality of UCB-type algorithms and Thompson sampling

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
asymptotically optimal on these bandits. Gaussian Thompson sampling `gaussianTS σ2` with a flat
prior has the same asymptotic upper bound on Gaussian bandits with variance `σ²`
[LS, Theorem 36.3], so it is asymptotically optimal on these bandits too.

More generally, let `ρ a` be a measure on `ℝ` for every arm `a`, all with the same set of means
(one family for every arm, or Gaussian families with different known variances). On the bandits
whose arm `a` has a law in the exponential family of `ρ a`, the KL-UCB algorithm `klucbFam ρ` for
these families [GC11; CGMMS13] is consistent, and its expected regret is `c* log n + o(log n)`
with `c* = ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`, the Lai–Robbins constant of these bandits
[BK96]. The common set of means makes the largest mean `μ*` a mean of the family of every arm, so
that `c*` is finite.

Thompson sampling with the Jeffreys priors of these families has the same asymptotic regret
[KKM13, Theorem 1], when the Jeffreys posteriors are proper after some observations and the
Jeffreys priors are finite on the natural parameters of the means at most `m`, for every mean `m`
of the families: its upper bound is `expFamilyTS_jeffreysPrior_regret_eventually_le`, which makes
it consistent, and the Lai–Robbins lower bound matches it. The Bernoulli family, whose Jeffreys
prior is finite and whose Thompson sampling draws the means from beta laws [KKM13, Figure 1], is
an instance, on the Bernoulli bandits with means in `(0, 1)`.

## Main statements

* `UCBF.isConsistent`: `ucbF σ2` is consistent over the σ²-sub-Gaussian bandits, for `σ² ≠ 0`.
* `UCBF.isConsistent_gaussianBandit`: `ucbF σ2` is consistent over the Gaussian bandits with
  variance `σ²`.
* `KLUCB.isConsistent`: `klucb` is consistent over the bandits with rewards in `[0, 1]`.
* `tendsto_ucbF_regret_div_log_gaussianBandit`: on a Gaussian bandit with variance `σ²`, the
  expected regret of `ucbF σ2` satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`.
* `isLittleO_ucbF_regret_sub_mul_log_gaussianBandit`: the same statement in the form
  `E[R_n] = c* log n + o(log n)`.
* `GaussianTS.isConsistent_gaussianBandit`: `gaussianTS σ2` is consistent over the Gaussian bandits
  with variance `σ²`.
* `tendsto_gaussianTS_regret_div_log_gaussianBandit`: [LS, Theorem 36.3], asymptotic part: on a
  Gaussian bandit with variance `σ²`, the expected regret of `gaussianTS σ2` satisfies
  `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`.
* `isLittleO_gaussianTS_regret_sub_mul_log_gaussianBandit`: the same statement in the form
  `E[R_n] = c* log n + o(log n)`.
* `KLUCB.isConsistent_bernoulliBandit`: `klucb` is consistent over the Bernoulli bandits.
* `tendsto_klucb_regret_div_log_bernoulliBandit`: on a Bernoulli bandit with means `p`, the
  expected regret of `klucb` satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`.
* `isLittleO_klucb_regret_sub_mul_log_bernoulliBandit`: the same statement in the form
  `E[R_n] = c* log n + o(log n)`.
* `klucbFam_regret_eventually_le_of_mem_image_expFamily`: on a bandit whose arms are members of
  exponential families, where `μ*` is a mean of the family of every arm `a` with positive gap and
  `μ_a` a mean of the family of the best arm, the expected regret of `klucbFam ρ` satisfies
  `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`.
* `KLUCBFam.isConsistent`: `klucbFam ρ` is consistent over these bandits.
* `tendsto_klucbFam_regret_div_log`, `isLittleO_klucbFam_regret_sub_mul_log`: on each of them, the
  expected regret of `klucbFam ρ` is `c* log n + o(log n)`, with
  `c* = ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`.
* `tendsto_klucbFam_gaussianReal_regret_div_log`,
  `isLittleO_klucbFam_gaussianReal_regret_sub_mul_log`: the Gaussian instance with known variances
  `σ2 a`, with `c* = ∑_{a : Δ_a > 0} 2 σ2_a / Δ_a`.
* `expFamilyTS_jeffreysPrior_regret_eventually_le_of_mem_image_expFamily`: on a bandit whose arms
  are members of exponential families, the expected regret of Thompson sampling with the Jeffreys
  priors satisfies `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`.
* `expFamilyTS_jeffreysPrior_regret_eventually_le_of_common_means`: the same bound for families
  with a common set of means, proper Jeffreys posteriors and Jeffreys priors finite below every
  mean.
* `ExpFamilyTS.isConsistent_jeffreysPrior`: Thompson sampling with the Jeffreys priors is
  consistent over these bandits.
* `tendsto_expFamilyTS_jeffreysPrior_regret_div_log`,
  `isLittleO_expFamilyTS_jeffreysPrior_regret_sub_mul_log`: [KKM13, Theorem 1]: on each of them,
  the expected regret of Thompson sampling with the Jeffreys priors is `c* log n + o(log n)`, with
  `c* = ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`.
* `tendsto_expFamilyTS_jeffreysPrior_regret_div_log_bernoulliBandit`,
  `isLittleO_expFamilyTS_jeffreysPrior_regret_sub_mul_log_bernoulliBandit`: the Bernoulli instance,
  on a Bernoulli bandit with means `p_a ∈ (0, 1)`, with `c* = ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`.

In the Bernoulli statements, `Δ_a / d(p_a, μ*)` is computed from the real number
`d(p_a, μ*).toReal`, as in `klucb_regret_eventually_le`. For an arm with positive gap it is `0`
exactly when `μ* = 1`, where `d(p_a, 1) = ∞`; for Thompson sampling, all the means lie in
`(0, 1)`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Chapters 8, 10, 16 and 36.
* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011.
* [CGMMS13] O. Cappé, A. Garivier, O.-A. Maillard, R. Munos and G. Stoltz, *Kullback–Leibler upper
  confidence bounds for optimal sequential allocation*, Annals of Statistics, 2013.
* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013.
* [BK96] A. N. Burnetas and M. N. Katehakis, *Optimal adaptive policies for sequential allocation
  problems*, Advances in Applied Mathematics, 1996.
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset Real Learning Bandits Asymptotics
open scoped ENNReal NNReal Topology unitInterval

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

/-- Gaussian Thompson sampling `gaussianTS σ2` is consistent over the Gaussian bandits with variance
`σ² ≠ 0`. -/
theorem GaussianTS.isConsistent_gaussianBandit (hσ2 : σ2 ≠ 0) :
    IsConsistent (gaussianTS σ2) (Set.range fun μ : α → ℝ ↦ gaussianBandit μ σ2) :=
  isConsistent_of_eventually_le_mul_log <| Set.forall_mem_range.mpr fun _ _ ↦
    ⟨_, gaussianTS_regret_eventually_le hσ2 (IT.isAlgEnvSeq_trajMeasure _ _) (lt_add_one _)⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {μ : α → ℝ} {p : α → I}

/-- **Asymptotic optimality of UCB for Gaussian bandits** [LS, §16.2]. On a Gaussian bandit with
variance `σ² ≠ 0`, the expected regret of the asymptotically optimal UCB algorithm `ucbF σ2`
satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`, the Lai–Robbins constant of the Gaussian
bandits with variance `σ²`. -/
theorem tendsto_ucbF_regret_div_log_gaussianBandit (hσ2 : σ2 ≠ 0)
    (h : IsAlgEnvSeq O A R (ucbF σ2) (Environment.bandit (gaussianBandit μ σ2)) P) :
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
    (h : IsAlgEnvSeq O A R (ucbF σ2) (Environment.bandit (gaussianBandit μ σ2)) P) :
    (fun n : ℕ ↦ P[regret (gaussianBandit μ σ2) A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        2 * σ2 / gap (gaussianBandit μ σ2) a) * log n) =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_ucbF_regret_div_log_gaussianBandit hσ2 h)

/-- **[LS, Theorem 36.3], asymptotic part: asymptotic optimality of Gaussian Thompson sampling.**
On a Gaussian bandit with variance `σ² ≠ 0`, the expected regret of Gaussian Thompson sampling
`gaussianTS σ2` with a flat prior satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ² / Δ_a`, the
Lai–Robbins constant of the Gaussian bandits with variance `σ²`. -/
theorem tendsto_gaussianTS_regret_div_log_gaussianBandit (hσ2 : σ2 ≠ 0)
    (h : IsAlgEnvSeq O A R (gaussianTS σ2) (Environment.bandit (gaussianBandit μ σ2)) P) :
    Tendsto (fun n : ℕ ↦ P[regret (gaussianBandit μ σ2) A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        2 * σ2 / gap (gaussianBandit μ σ2) a)) := by
  -- The upper bound is `gaussianTS_regret_eventually_le`; the lower bound is the
  -- Lai–Robbins lower bound.
  refine tendsto_div_of_eventually_mul_le
    ((eventually_gt_atTop 1).mono fun n hn ↦ log_pos (by exact_mod_cast hn)) (fun c hc ↦ ?_)
    fun c hc ↦ gaussianTS_regret_eventually_le hσ2 h hc
  filter_upwards [eventually_mul_log_le_integral_regret_gaussianBandit hσ2
    (GaussianTS.isConsistent_gaussianBandit hσ2) μ hc] with n hn
  rwa [← h.integral_regret_eq_integral_trajMeasure] at hn

/-- **[LS, Theorem 36.3], asymptotic part: asymptotic optimality of Gaussian Thompson sampling.**
On a Gaussian bandit with variance `σ² ≠ 0`, the expected regret of Gaussian Thompson sampling
`gaussianTS σ2` is `c* log n + o(log n)`, where `c* = ∑_{a : Δ_a > 0} 2 σ² / Δ_a` is the
Lai–Robbins constant of the Gaussian bandits with variance `σ²`. -/
theorem isLittleO_gaussianTS_regret_sub_mul_log_gaussianBandit (hσ2 : σ2 ≠ 0)
    (h : IsAlgEnvSeq O A R (gaussianTS σ2) (Environment.bandit (gaussianBandit μ σ2)) P) :
    (fun n : ℕ ↦ P[regret (gaussianBandit μ σ2) A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap (gaussianBandit μ σ2) a),
        2 * σ2 / gap (gaussianBandit μ σ2) a) * log n) =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_gaussianTS_regret_div_log_gaussianBandit hσ2 h)

/-- **Asymptotic optimality of KL-UCB for Bernoulli bandits** [LS, §16.2]. On a Bernoulli bandit
with means `p` and largest mean `μ* = max_b p_b`, the expected regret of the KL-UCB algorithm
satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`, the Lai–Robbins constant of the
Bernoulli bandits. As in `klucb_regret_eventually_le`, the terms are computed from the real number
`d(p_a, μ*).toReal`, so that they vanish when `μ* = 1`. -/
theorem tendsto_klucb_regret_div_log_bernoulliBandit
    (h : IsAlgEnvSeq O A R klucb (Environment.bandit (bernoulliBandit p)) P) :
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
    (h : IsAlgEnvSeq O A R klucb (Environment.bandit (bernoulliBandit p)) P) :
    (fun n : ℕ ↦ P[regret (bernoulliBandit p) A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap (bernoulliBandit p) a),
        gap (bernoulliBandit p) a / (klBer (p a) (⨆ b, (p b : ℝ))).toReal) * log n)
      =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_klucb_regret_div_log_bernoulliBandit h)

section ExpFamily

variable {ρ : α → Measure ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- **Asymptotic regret of KL-UCB on exponential families.** Let `ρ a` be a measure on `ℝ` for
every arm `a`, and let the law of every arm `a` be a member `(ρ a)_η` of the exponential family of
`ρ a`, with `η` in the interior of `integrableExpSet id (ρ a)`. Assume that for every arm `a` with
positive gap, the largest mean `μ*` is a mean of the family of `ρ a` and `μ_a` is a mean of the
family of the best arm. For every `c > ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`, the expected
regret at horizon `n` of the KL-UCB algorithm for the families `ρ` is eventually at most
`c log n`; that is, `limsup_n E[R_n] / log n ≤ ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`. -/
theorem klucbFam_regret_eventually_le_of_mem_image_expFamily
    (hν : ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a)))
    (hμs : ∀ a, 0 < gap ν a → (ν (bestArm ν))[id] ∈ (ρ a).expFamilyMeans id)
    (hμb : ∀ a, 0 < gap ν a → (ν a)[id] ∈ (ρ (bestArm ν)).expFamilyMeans id)
    (h : IsAlgEnvSeq O A R (klucbFam ρ) (Environment.bandit ν) P) {c : ℝ}
    (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id] < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n := by
  have hμ (a : α) := Measure.integral_mem_expFamilyMeans_of_mem_image (hν a)
  rcases (univ.filter (fun a ↦ 0 < gap ν a)).eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
  · -- If every gap vanishes, the regret is `0`.
    have hc0 : 0 < c := by simpa [hS] using hc
    have hgap (a : α) : gap ν a = 0 :=
      le_antisymm (not_lt.mp (filter_eq_empty_iff.mp hS (mem_univ a))) gap_nonneg
    refine .of_forall fun n ↦ ?_
    rw [integral_regret_eq_sum_gap_mul_integral_pullCount h.measurable_action]
    simpa [hgap] using mul_nonneg hc0.le (log_natCast_nonneg n)
  -- The families of the arms with positive gap and of the best arm have the two distinct means
  -- `μ_a < μ*`, so that none of them is a Dirac mass.
  have hga₀ := (mem_filter.mp ha₀).2
  have hρ (a : α) (ha : 0 < gap ν a) : ∀ c, ¬ id =ᵐ[ρ a] fun _ ↦ c :=
    not_ae_eq_const_of_gap_pos (hμ a) (hμs a ha) ha
  have hρs : ∀ c, ¬ id =ᵐ[ρ (bestArm ν)] fun _ ↦ c :=
    not_ae_eq_const_of_gap_pos (hμb a₀ hga₀) (hμ _) hga₀
  -- These arms are dominated by the members of their means, which are their own laws.
  exact klucbFam_regret_eventually_le h (fun a _ ↦ hμ a) (hμ _)
    (fun a ha ↦ mgfDominatedOn_expFamily_natParam_integral_of_mem_image (hρ a ha) (hν a) _)
    (mgfDominatedOn_expFamily_natParam_integral_of_mem_image hρs (hν _) _) hρs hμs hc

/-- **KL-UCB is consistent over exponential families.** Let `ρ a` be a measure on `ℝ` for every
arm `a`, all with the same set of means. The KL-UCB algorithm for the families `ρ` is consistent
over the bandits whose arm `a` has a law in the exponential family of `ρ a`, a member `(ρ a)_η`
with `η` in the interior of `integrableExpSet id (ρ a)`. -/
theorem KLUCBFam.isConsistent (hM : ∀ a b, (ρ a).expFamilyMeans id = (ρ b).expFamilyMeans id) :
    IsConsistent (klucbFam ρ)
      {ν : Kernel α ℝ | ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a))} :=
  isConsistent_of_eventually_le_mul_log fun _ hν _ ↦
    ⟨_, klucbFam_regret_eventually_le_of_mem_image_expFamily hν
      (fun a _ ↦ hM (bestArm _) a ▸ Measure.integral_mem_expFamilyMeans_of_mem_image (hν _))
      (fun a _ ↦ hM a (bestArm _) ▸ Measure.integral_mem_expFamilyMeans_of_mem_image (hν a))
      (IT.isAlgEnvSeq_trajMeasure _ _) (lt_add_one _)⟩

/-- **Asymptotic optimality of KL-UCB for exponential families** [GC11; CGMMS13; LS, §16.2].
Let `ρ a` be a measure on `ℝ` for every arm `a`, all with the same set of means, and let the law
of every arm `a` be a member of the exponential family of `ρ a`. The expected regret of the KL-UCB
algorithm for the families `ρ` satisfies
`E[R_n] / log n → ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`, the Lai–Robbins constant of the
bandits whose arms are members of these families. -/
theorem tendsto_klucbFam_regret_div_log
    (hM : ∀ a b, (ρ a).expFamilyMeans id = (ρ b).expFamilyMeans id)
    (hν : ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a)))
    (h : IsAlgEnvSeq O A R (klucbFam ρ) (Environment.bandit ν) P) :
    Tendsto (fun n : ℕ ↦ P[regret ν A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
        gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id])) := by
  -- The upper bound is `klucbFam_regret_eventually_le_of_mem_image_expFamily`; the lower bound is
  -- the Lai–Robbins lower bound.
  have hμs (a : α) (_ : 0 < gap ν a) : (ν (bestArm ν))[id] ∈ (ρ a).expFamilyMeans id :=
    hM (bestArm ν) a ▸ Measure.integral_mem_expFamilyMeans_of_mem_image (hν _)
  refine tendsto_div_of_eventually_mul_le
    ((eventually_gt_atTop 1).mono fun n hn ↦ log_pos (by exact_mod_cast hn)) (fun c hc ↦ ?_)
    fun c hc ↦ klucbFam_regret_eventually_le_of_mem_image_expFamily hν hμs
      (fun a _ ↦ hM a (bestArm ν) ▸ Measure.integral_mem_expFamilyMeans_of_mem_image (hν a)) h hc
  filter_upwards [eventually_mul_log_le_integral_regret_expFamily (KLUCBFam.isConsistent hM) hν
    hμs hc] with n hn
  rwa [← h.integral_regret_eq_integral_trajMeasure] at hn

/-- **Asymptotic optimality of KL-UCB for exponential families** [GC11; CGMMS13; LS, §16.2].
Let `ρ a` be a measure on `ℝ` for every arm `a`, all with the same set of means, and let the law
of every arm `a` be a member of the exponential family of `ρ a`. The expected regret of the KL-UCB
algorithm for the families `ρ` is `c* log n + o(log n)`, where
`c* = ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)` is the Lai–Robbins constant of the bandits whose
arms are members of these families. -/
theorem isLittleO_klucbFam_regret_sub_mul_log
    (hM : ∀ a b, (ρ a).expFamilyMeans id = (ρ b).expFamilyMeans id)
    (hν : ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a)))
    (h : IsAlgEnvSeq O A R (klucbFam ρ) (Environment.bandit ν) P) :
    (fun n : ℕ ↦ P[regret ν A n] - (∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
        gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id]) * log n)
      =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_klucbFam_regret_div_log hM hν h)

/-- **Asymptotic optimality of KL-UCB for Gaussian arms with known variances.** Let the law of
every arm `a` be `𝒩(μ_a, σ2_a)` with `σ2_a ≠ 0`. The expected regret of the KL-UCB algorithm for
the Gaussian families of variances `σ2 a`, generated by any members `𝒩(m a, σ2 a)`, satisfies
`E[R_n] / log n → ∑_{a : Δ_a > 0} 2 σ2_a / Δ_a`, the Lai–Robbins constant of the Gaussian bandits
with these variances. For a common variance `σ2`, that algorithm is `ucbF σ2`
(`klucbFam_gaussianReal`). -/
theorem tendsto_klucbFam_gaussianReal_regret_div_log (m : α → ℝ) {σ2 : α → ℝ≥0}
    (hσ2 : ∀ a, σ2 a ≠ 0) (hν : ∀ a, ν a = gaussianReal (μ a) (σ2 a))
    (h : IsAlgEnvSeq O A R (klucbFam fun a ↦ gaussianReal (m a) (σ2 a)) (Environment.bandit ν)
      P) :
    Tendsto (fun n : ℕ ↦ P[regret ν A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), 2 * σ2 a / gap ν a)) := by
  -- Every Gaussian family of variance `σ2 a` has all real numbers as means, and `ν a` is its
  -- member of mean `μ a`.
  have hmeans (a : α) : (gaussianReal (m a) (σ2 a)).expFamilyMeans id = Set.univ :=
    Set.eq_univ_of_forall (mem_expFamilyMeans_gaussianReal _ (hσ2 a))
  have hmem (a : α) : ν a ∈ (gaussianReal (m a) (σ2 a)).expFamily id ''
      interior (integrableExpSet id (gaussianReal (m a) (σ2 a))) := by
    rw [hν a, ← expFamily_natParam_gaussianReal (m a) (hσ2 a) (μ a)]
    exact Measure.expFamily_natParam_mem_image (mem_expFamilyMeans_gaussianReal _ (hσ2 a) _)
  rw [← sum_gap_div_expFamilyDiv_gaussianReal m hσ2]
  exact tendsto_klucbFam_regret_div_log (fun a b ↦ (hmeans a).trans (hmeans b).symm) hmem h

/-- **Asymptotic optimality of KL-UCB for Gaussian arms with known variances.** Let the law of
every arm `a` be `𝒩(μ_a, σ2_a)` with `σ2_a ≠ 0`. The expected regret of the KL-UCB algorithm for
the Gaussian families of variances `σ2 a`, generated by any members `𝒩(m a, σ2 a)`, is
`c* log n + o(log n)`, where `c* = ∑_{a : Δ_a > 0} 2 σ2_a / Δ_a` is the Lai–Robbins constant of the
Gaussian bandits with these variances. -/
theorem isLittleO_klucbFam_gaussianReal_regret_sub_mul_log (m : α → ℝ) {σ2 : α → ℝ≥0}
    (hσ2 : ∀ a, σ2 a ≠ 0) (hν : ∀ a, ν a = gaussianReal (μ a) (σ2 a))
    (h : IsAlgEnvSeq O A R (klucbFam fun a ↦ gaussianReal (m a) (σ2 a)) (Environment.bandit ν)
      P) :
    (fun n : ℕ ↦ P[regret ν A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a), 2 * σ2 a / gap ν a) * log n)
      =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_klucbFam_gaussianReal_regret_div_log m hσ2 hν h)

end ExpFamily

section ExpFamilyTS

variable {ρ : α → Measure ℝ} [∀ a, SFinite (ρ a)] {ν : Kernel α ℝ} [IsMarkovKernel ν]

/-- **Asymptotic regret of Thompson sampling with the Jeffreys prior on exponential families**
[KKM13, Theorem 1, upper bound]. Let `ρ a` be a measure on `ℝ` for every arm `a`, and let the law
of every arm `a` be a member `(ρ a)_η` of the exponential family of `ρ a`, with `η` in the interior
of `integrableExpSet id (ρ a)`. Assume that for every arm `a` with positive gap, the largest mean
`μ*` is a mean of the family of `ρ a`, `μ_a` is a mean of the family of the best arm, and the
Jeffreys posterior of `ρ a` is proper after some observations, and that the Jeffreys prior of the
family of the best arm is finite on the natural parameters of the means at most `m`, for every
`m < μ*`. For every `c > ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`, the expected regret at horizon
`n` of Thompson sampling with the Jeffreys priors of the families `ρ` is eventually at most
`c log n`. -/
theorem expFamilyTS_jeffreysPrior_regret_eventually_le_of_mem_image_expFamily
    (hν : ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a)))
    (hμs : ∀ a, 0 < gap ν a → (ν (bestArm ν))[id] ∈ (ρ a).expFamilyMeans id)
    (hμb : ∀ a, 0 < gap ν a → (ν a)[id] ∈ (ρ (bestArm ν)).expFamilyMeans id)
    (hprop : ∀ a, 0 < gap ν a →
      ∃ s₀ S₀, (ρ a).expFamilyPosterior id ((ρ a).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hπs : ∀ m < (ν (bestArm ν))[id], (ρ (bestArm ν)).jeffreysPrior id
      {θ | deriv (cgf id (ρ (bestArm ν))) θ ≤ m} ≠ ∞)
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id) (Environment.bandit ν)
      P) {c : ℝ}
    (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id] < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n := by
  have hμ (a : α) := Measure.integral_mem_expFamilyMeans_of_mem_image (hν a)
  rcases (univ.filter (fun a ↦ 0 < gap ν a)).eq_empty_or_nonempty with hS | ⟨a₀, ha₀⟩
  · -- If every gap vanishes, there is no arm to bound.
    refine integral_regret_eventually_le_of_forall_integral_pullCount_eventually_le
      h.measurable_action (.of_forall fun n ↦ log_natCast_nonneg n) 0
      (fun a ha ↦ absurd (mem_filter.mpr ⟨mem_univ a, ha⟩) (hS ▸ notMem_empty a)) ?_
    simpa [hS] using hc
  -- The families of the arms with positive gap and of the best arm have the two distinct means
  -- `μ_a < μ*`, so that none of them is a Dirac mass.
  have hga₀ := (mem_filter.mp ha₀).2
  have hρ (a : α) (ha : 0 < gap ν a) : ∀ c, ¬ id =ᵐ[ρ a] fun _ ↦ c :=
    not_ae_eq_const_of_gap_pos (hμ a) (hμs a ha) ha
  have hρs : ∀ c, ¬ id =ᵐ[ρ (bestArm ν)] fun _ ↦ c :=
    not_ae_eq_const_of_gap_pos (hμb a₀ hga₀) (hμ _) hga₀
  -- These arms are dominated by the members of their means, which are their own laws.
  exact expFamilyTS_jeffreysPrior_regret_eventually_le h (fun a _ ↦ hμ a)
    (fun a ha ↦ mgfDominatedOn_expFamily_natParam_integral_of_mem_image (hρ a ha) (hν a) _)
    hprop hμs (hμ _) (mgfDominatedOn_expFamily_natParam_integral_of_mem_image hρs (hν _) _) hρs
    hπs hc

/-- **Asymptotic regret of Thompson sampling with the Jeffreys prior on exponential families with
common means** [KKM13, Theorem 1, upper bound]. Let `ρ a` be a measure on `ℝ` for every arm `a`,
all with the same set of means, whose Jeffreys posteriors are proper after some observations, and
whose Jeffreys priors are finite on the natural parameters of the means at most `m`, for every mean
`m` of the families. Let the law of every arm `a` be a member of the exponential family of `ρ a`.
For every `c > ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`, the expected regret at horizon `n` of
Thompson sampling with the Jeffreys priors of the families `ρ` is eventually at most `c log n`. -/
theorem expFamilyTS_jeffreysPrior_regret_eventually_le_of_common_means
    (hM : ∀ a b, (ρ a).expFamilyMeans id = (ρ b).expFamilyMeans id)
    (hprop : ∀ a, ∃ s₀ S₀, (ρ a).expFamilyPosterior id ((ρ a).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hπ : ∀ a, ∀ m ∈ (ρ a).expFamilyMeans id,
      (ρ a).jeffreysPrior id {θ | deriv (cgf id (ρ a)) θ ≤ m} ≠ ∞)
    (hν : ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a)))
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id) (Environment.bandit ν)
      P) {c : ℝ}
    (hc : ∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
      gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id] < c) :
    ∀ᶠ n : ℕ in atTop, P[regret ν A n] ≤ c * log n :=
  have hμ (a : α) := Measure.integral_mem_expFamilyMeans_of_mem_image (hν a)
  expFamilyTS_jeffreysPrior_regret_eventually_le_of_mem_image_expFamily hν
    (fun a _ ↦ hM (bestArm ν) a ▸ hμ _) (fun a _ ↦ hM a (bestArm ν) ▸ hμ a) (fun a _ ↦ hprop a)
    (fun _ hm ↦ ne_top_of_le_ne_top (hπ _ _ (hμ _)) (measure_mono fun _ hθ ↦ le_trans hθ hm.le))
    h hc

/-- **Thompson sampling with the Jeffreys prior is consistent over exponential families.** Let
`ρ a` be a measure on `ℝ` for every arm `a`, all with the same set of means, whose Jeffreys
posteriors are proper after some observations, and whose Jeffreys priors are finite on the natural
parameters of the means at most `m`, for every mean `m` of the families. Thompson sampling with the
Jeffreys priors of the families `ρ` is consistent over the bandits whose arm `a` has a law in the
exponential family of `ρ a`, a member `(ρ a)_η` with `η` in the interior of
`integrableExpSet id (ρ a)`. -/
theorem ExpFamilyTS.isConsistent_jeffreysPrior
    (hM : ∀ a b, (ρ a).expFamilyMeans id = (ρ b).expFamilyMeans id)
    (hprop : ∀ a, ∃ s₀ S₀, (ρ a).expFamilyPosterior id ((ρ a).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hπ : ∀ a, ∀ m ∈ (ρ a).expFamilyMeans id,
      (ρ a).jeffreysPrior id {θ | deriv (cgf id (ρ a)) θ ≤ m} ≠ ∞) :
    IsConsistent (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id)
      {ν : Kernel α ℝ | ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a))} :=
  isConsistent_of_eventually_le_mul_log fun _ hν _ ↦
    ⟨_, expFamilyTS_jeffreysPrior_regret_eventually_le_of_common_means hM hprop hπ hν
      (IT.isAlgEnvSeq_trajMeasure _ _) (lt_add_one _)⟩

/-- **Asymptotic optimality of Thompson sampling with the Jeffreys prior on exponential families**
[KKM13, Theorem 1]. Let `ρ a` be a measure on `ℝ` for every arm `a`, all with the same set of
means, whose Jeffreys posteriors are proper after some observations, and whose Jeffreys priors are
finite on the natural parameters of the means at most `m`, for every mean `m` of the families. Let
the law of every arm `a` be a member of the exponential family of `ρ a`. The expected regret of
Thompson sampling with the Jeffreys priors of the families `ρ` satisfies
`E[R_n] / log n → ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)`, the Lai–Robbins constant of the
bandits whose arms are members of these families. -/
theorem tendsto_expFamilyTS_jeffreysPrior_regret_div_log
    (hM : ∀ a b, (ρ a).expFamilyMeans id = (ρ b).expFamilyMeans id)
    (hprop : ∀ a, ∃ s₀ S₀, (ρ a).expFamilyPosterior id ((ρ a).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hπ : ∀ a, ∀ m ∈ (ρ a).expFamilyMeans id,
      (ρ a).jeffreysPrior id {θ | deriv (cgf id (ρ a)) θ ≤ m} ≠ ∞)
    (hν : ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a)))
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id) (Environment.bandit ν)
      P) :
    Tendsto (fun n : ℕ ↦ P[regret ν A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
        gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id])) := by
  -- The upper bound is `expFamilyTS_jeffreysPrior_regret_eventually_le_of_common_means`; the
  -- lower bound is the Lai–Robbins lower bound.
  have hμs (a : α) (_ : 0 < gap ν a) : (ν (bestArm ν))[id] ∈ (ρ a).expFamilyMeans id :=
    hM (bestArm ν) a ▸ Measure.integral_mem_expFamilyMeans_of_mem_image (hν _)
  refine tendsto_div_of_eventually_mul_le
    ((eventually_gt_atTop 1).mono fun n hn ↦ log_pos (by exact_mod_cast hn)) (fun c hc ↦ ?_)
    fun c hc ↦ expFamilyTS_jeffreysPrior_regret_eventually_le_of_common_means hM hprop hπ hν h hc
  filter_upwards [eventually_mul_log_le_integral_regret_expFamily
    (ExpFamilyTS.isConsistent_jeffreysPrior hM hprop hπ) hν hμs hc] with n hn
  rwa [← h.integral_regret_eq_integral_trajMeasure] at hn

/-- **Asymptotic optimality of Thompson sampling with the Jeffreys prior on exponential families**
[KKM13, Theorem 1]. Under the assumptions of `tendsto_expFamilyTS_jeffreysPrior_regret_div_log`,
the expected regret of Thompson sampling with the Jeffreys priors of the families `ρ` is
`c* log n + o(log n)`, where `c* = ∑_{a : Δ_a > 0} Δ_a / d_{ρ a}(μ_a, μ*)` is the Lai–Robbins
constant of the bandits whose arms are members of these families. -/
theorem isLittleO_expFamilyTS_jeffreysPrior_regret_sub_mul_log
    (hM : ∀ a b, (ρ a).expFamilyMeans id = (ρ b).expFamilyMeans id)
    (hprop : ∀ a, ∃ s₀ S₀, (ρ a).expFamilyPosterior id ((ρ a).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hπ : ∀ a, ∀ m ∈ (ρ a).expFamilyMeans id,
      (ρ a).jeffreysPrior id {θ | deriv (cgf id (ρ a)) θ ≤ m} ≠ ∞)
    (hν : ∀ a, ν a ∈ (ρ a).expFamily id '' interior (integrableExpSet id (ρ a)))
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id) (Environment.bandit ν)
      P) :
    (fun n : ℕ ↦ P[regret ν A n] - (∑ a ∈ univ.filter (fun a ↦ 0 < gap ν a),
        gap ν a / (ρ a).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id]) * log n)
      =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_expFamilyTS_jeffreysPrior_regret_div_log hM hprop hπ hν h)

end ExpFamilyTS

section BernoulliTS

variable (η₀ : ℝ)

/-- **Asymptotic optimality of Thompson sampling with the Jeffreys prior for Bernoulli bandits**
[KKM13, Theorem 1 and Figure 1]. On a Bernoulli bandit with means `p_a ∈ (0, 1)` and largest mean
`μ* = max_b p_b`, the expected regret of Thompson sampling with the Jeffreys prior of the Bernoulli
family, which samples the mean of an arm with `S` successes in `s` pulls from
`Beta(S + 1 / 2, s - S + 1 / 2)`, satisfies `E[R_n] / log n → ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)`,
the Lai–Robbins constant of the Bernoulli bandits with means in `(0, 1)`. The family is generated
by `Ber((1 : ℝ), 0, unitInterval.sigmoid η₀)`, for any `η₀`. -/
theorem tendsto_expFamilyTS_jeffreysPrior_regret_div_log_bernoulliBandit
    (hp : ∀ a, (p a : ℝ) ∈ Set.Ioo 0 1)
    (h : IsAlgEnvSeq O A R (expFamilyTS (fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid η₀))
      fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid η₀).jeffreysPrior id)
      (Environment.bandit (bernoulliBandit p)) P) :
    Tendsto (fun n : ℕ ↦ P[regret (bernoulliBandit p) A n] / log n) atTop
      (𝓝 (∑ a ∈ univ.filter (fun a ↦ 0 < gap (bernoulliBandit p) a),
        gap (bernoulliBandit p) a / (klBer (p a) (⨆ b, (p b : ℝ))).toReal)) := by
  -- The arm laws are members of the family, and the largest mean `μ*` lies in `(0, 1)`.
  have hν (a : α) : bernoulliBandit p a ∈ Ber((1 : ℝ), 0, unitInterval.sigmoid η₀).expFamily id ''
      interior (integrableExpSet id Ber((1 : ℝ), 0, unitInterval.sigmoid η₀)) := by
    have hmem := Measure.expFamily_natParam_mem_image
      ((expFamilyMeans_bernoulliMeasure_sigmoid η₀).symm ▸ hp a)
    rwa [expFamily_natParam_bernoulliMeasure_sigmoid η₀ (hp a), Subtype.coe_eta,
      ← bernoulliBandit_apply p a] at hmem
  set ν := bernoulliBandit p
  have hbest : (ν (bestArm ν))[id] = ⨆ b, (p b : ℝ) := by
    simp_rw [← iSup_integral_eq_integral_bestArm, ν, integral_id_bernoulliBandit]
  have hμs : (⨆ b, (p b : ℝ)) ∈ Set.Ioo 0 1 := hbest ▸ integral_id_bernoulliBandit p _ ▸ hp _
  -- The divergence of the family is the binary relative entropy.
  have hconst (a : α) :
      Ber((1 : ℝ), 0, unitInterval.sigmoid η₀).expFamilyDiv id (ν a)[id] (ν (bestArm ν))[id] =
        (klBer (p a) (⨆ b, (p b : ℝ))).toReal := by
    rw [hbest, integral_id_bernoulliBandit, expFamilyDiv_bernoulliMeasure_sigmoid η₀ (hp a) hμs,
      toReal_klBer (Set.Ioo_subset_Icc_self (hp a)) (Set.Ioo_subset_Icc_self hμs)
        (klBer_ne_top hμs)]
  simp_rw [← hconst]
  exact tendsto_expFamilyTS_jeffreysPrior_regret_div_log (fun _ _ ↦ rfl)
    (fun _ ↦ ⟨1, 0, (isProbabilityMeasure_expFamilyPosterior_bernoulliMeasure_sigmoid_jeffreysPrior
      η₀ (by norm_num) (by norm_num)).ne_zero⟩) (fun _ _ _ ↦ measure_ne_top _ _) hν h

/-- **Asymptotic optimality of Thompson sampling with the Jeffreys prior for Bernoulli bandits**
[KKM13, Theorem 1 and Figure 1]. On a Bernoulli bandit with means `p_a ∈ (0, 1)` and largest mean
`μ* = max_b p_b`, the expected regret of Thompson sampling with the Jeffreys prior of the Bernoulli
family, generated by `Ber((1 : ℝ), 0, unitInterval.sigmoid η₀)`, is `c* log n + o(log n)`, where
`c* = ∑_{a : Δ_a > 0} Δ_a / d(p_a, μ*)` is the Lai–Robbins constant of the Bernoulli bandits with
means in `(0, 1)`. -/
theorem isLittleO_expFamilyTS_jeffreysPrior_regret_sub_mul_log_bernoulliBandit
    (hp : ∀ a, (p a : ℝ) ∈ Set.Ioo 0 1)
    (h : IsAlgEnvSeq O A R (expFamilyTS (fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid η₀))
      fun _ ↦ Ber((1 : ℝ), 0, unitInterval.sigmoid η₀).jeffreysPrior id)
      (Environment.bandit (bernoulliBandit p)) P) :
    (fun n : ℕ ↦ P[regret (bernoulliBandit p) A n] -
      (∑ a ∈ univ.filter (fun a ↦ 0 < gap (bernoulliBandit p) a),
        gap (bernoulliBandit p) a / (klBer (p a) (⨆ b, (p b : ℝ))).toReal) * log n)
      =o[atTop] fun n : ℕ ↦ log n :=
  isLittleO_sub_mul_of_tendsto_div
    ((eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne')
    (tendsto_expFamilyTS_jeffreysPrior_regret_div_log_bernoulliBandit η₀ hp h)

end BernoulliTS

end LMLExplore.Bandits
