/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Bandits.ThompsonSampling.Basic
public import LMLExplore.Probability.Distributions.ExponentialFamily.Chernoff
public import LMLExplore.Probability.Distributions.ExponentialFamily.Posterior.Concentration
import LMLExplore.Analysis.SpecialFunctions.Exp

/-!
# Thompson sampling with the Jeffreys prior rarely over-samples a suboptimal arm

Let `ρ` be a natural exponential family on `ℝ` (the statistic `id`, not `ρ`-almost everywhere
constant), with log-partition function `ψ`, natural parameters `Θ`, set of means `M` and
divergence `d(μ, μ')` in the mean parametrization, and let `π_J` be its Jeffreys prior. Thompson
sampling with the Jeffreys prior [KKM13] perturbs an arm pulled `s ≥ 1` times with sum of rewards
`S` by the mean `ψ'(θ)` of a natural parameter `θ` drawn from the posterior after `s` observations
with sum `S`. Write `G_s` for the probability that this perturbation exceeds a level `c`.

For an arm whose rewards `X₀, X₁, …` are independent and dominated by the member of mean `μ < c`
of the family (for example rewards with law that member), the generic bound of
follow-the-perturbed-leader [LS, Theorem 36.2] (`ExpFamilyTS.lintegral_pullCount_le`) needs the
expected number of sample sizes `s < n` at which `G_s > 1 / n`, computed from the first `s`
rewards. This file shows that for every rate `β < d(μ, c)` this number is at most
`log n / β + C`, with `C` independent of `n`: Thompson sampling with the Jeffreys prior pulls a
suboptimal arm of mean `μ` at most `log n / d(μ, c) + o(log n)` times because its posterior looks
better than `c`. This is the term (B) of the proof of [KKM13, Theorem 2], bounded through the
posterior concentration theorem [KKM13, Theorem 4] as in [KKM13, Lemma 6], and the analogue for
exponential families of [LS, Exercise 36.6(b)] for Gaussian Thompson sampling.

The bound has two parts. By the posterior concentration theorem [KKM13, Theorem 4], there is an
accuracy `δ > 0` such that `G_s ≤ exp (-s β)` for every large `s` and every sum `S` of the first
`s` observations with `|S - s μ| ≤ s δ`; on that event `G_s > 1 / n` forces `s β < log n`. Off that
event, the Cramér–Chernoff bounds of the family make the probability of the sample size `s` at
most `exp (-s d(μ + δ, μ)) + exp (-s d(μ - δ, μ))`, which is summable.

The Jeffreys posterior is assumed to be proper after some number of observations, as in [KKM13];
it is then proper after every large enough number of observations whose empirical mean is close
to `μ`.

## Main statements

* `LMLExplore.Bandits.expFamilyTSStackLaw_Ioi`: the perturbation of an arm with a proper posterior
  exceeds `c` with the posterior probability that `c < ψ'(θ)`.
* `LMLExplore.Bandits.exists_expFamilyTSStackLaw_jeffreysPrior_Ioi_le`: posterior concentration
  for Thompson sampling with the Jeffreys prior: for `μ < c` and `β < d(μ, c)`, there are `δ > 0`
  and `N` with `G_s ≤ exp (-s β)` after `s ≥ N` observations of sum `S` with `|S - s μ| ≤ s δ`.
* `ProbabilityTheory.iIndepFun.exists_sum_measure_inv_lt_expFamilyTSStackLaw_jeffreysPrior_Ioi_le`:
  for independent variables dominated by the member of mean `μ < c` and `0 < β < d(μ, c)`, there
  is `C` with `∑_{s < n} P(G_s > 1 / n) ≤ log n / β + C` for every `n`.
* `LMLExplore.Bandits.exists_sum_streamMeasure_inv_lt_expFamilyTSStackLaw_jeffreysPrior_Ioi_le`:
  the same bound in the reward-stack model `streamMeasure ν` of a stochastic bandit.
* `LMLExplore.Bandits.ExpFamilyTS.exists_lintegral_pullCount_le_add_log`: [LS, Theorem 36.2] for
  Thompson sampling with the Jeffreys priors, with this bound on its last term:
  `E[T_i(n)] ≤ 1 + E[∑_{s < n} (G_{j s}⁻¹ - 1)] + log n / β + C`.

## References

* [KKM13] N. Korda, E. Kaufmann and R. Munos, *Thompson sampling for 1-dimensional exponential
  family bandits*, NeurIPS 2013, Section 3 (Lemma 6 and the proof of Theorem 2) and Section 4
  (Theorem 4).
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Theorem 36.2 and Exercise 36.6.
-/

public section

open MeasureTheory ProbabilityTheory Real Set Learning Bandits

open scoped ENNReal

namespace LMLExplore.Bandits

variable {ρ ν : Measure ℝ} {s : ℕ} {S : ℝ}

/-- The perturbation of an arm pulled `s ≠ 0` times with sum of rewards `S`, whose posterior is not
`0`, exceeds a level `c` with the posterior probability that the mean `ψ'(θ)` exceeds `c`. -/
lemma expFamilyTSStackLaw_Ioi (hs : s ≠ 0) (h : ρ.expFamilyPosterior id ν s S ≠ 0) (c : ℝ) :
    expFamilyTSStackLaw ρ ν s S (Ioi (c : EReal)) =
      ρ.expFamilyPosterior id ν s S {θ | c < deriv (cgf id ρ) θ} := by
  rw [expFamilyTSStackLaw_of_ne_zero hs h, Measure.map_apply (by fun_prop) measurableSet_Ioi]
  congr 1
  ext θ
  simp

/-- An accuracy `δ > 0` for the posterior concentration of the mean `μ` against the level `c`:
`μ ± 2 δ` are means of the family, `δ ≤ c - μ`, and the exponent `d(μ, c) - δ (η(c) - η(μ))` of
`Measure.exists_expFamilyPosterior_jeffreysPrior_setOf_le_deriv_cgf_le` exceeds a given
`β < d(μ, c)`. -/
private lemma exists_accuracy {μ c β : ℝ} (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ] fun _ ↦ c)
    (hμ : μ ∈ ρ.expFamilyMeans id) (hc : c ∈ ρ.expFamilyMeans id) (hμc : μ < c)
    (hβd : β < ρ.expFamilyDiv id μ c) :
    ∃ δ > 0, δ ≤ c - μ ∧ μ - 2 * δ ∈ ρ.expFamilyMeans id ∧ μ + 2 * δ ∈ ρ.expFamilyMeans id ∧
      β < ρ.expFamilyDiv id μ c - δ * (ρ.natParam id c - ρ.natParam id μ) := by
  set d := ρ.expFamilyDiv id μ c
  set g := ρ.natParam id c - ρ.natParam id μ
  have hg : 0 ≤ g := sub_nonneg.2 (Measure.monotoneOn_natParam hμ hc hμc.le)
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 (Measure.isOpen_expFamilyMeans hT) μ hμ
  set δ := min (min (ε₀ / 3) (c - μ)) ((d - β) / (2 * (g + 1))) with hδ_def
  have hδ : 0 < δ :=
    lt_min (lt_min (by positivity) (sub_pos.2 hμc)) (div_pos (sub_pos.2 hβd) (by positivity))
  have hδε : δ ≤ ε₀ / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hδg : δ * (g + 1) ≤ (d - β) / 2 := by
    have h := min_le_right (min (ε₀ / 3) (c - μ)) ((d - β) / (2 * (g + 1)))
    rw [← hδ_def, le_div_iff₀ (by positivity)] at h
    linarith
  have hmem (x : ℝ) (hx : |x - μ| = 2 * δ) : x ∈ ρ.expFamilyMeans id :=
    hball (by rw [Metric.mem_ball, Real.dist_eq]; linarith)
  refine ⟨δ, hδ, (min_le_left _ _).trans (min_le_right _ _),
    hmem _ (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by linarith)]),
    hmem _ (by rw [add_sub_cancel_left, abs_of_pos (by linarith)]), by nlinarith⟩

/-- **Posterior concentration for Thompson sampling with the Jeffreys prior** [KKM13, Theorem 4].
Let `μ < c` be means of the natural exponential family of `ρ`, and let the posterior of the
Jeffreys prior be proper after some observations. For every `β < d(μ, c)` there are an accuracy
`δ > 0`, with `μ - δ` and `μ + δ` means of the family, and `N` such that after `s ≥ N`
observations whose sum `S` satisfies `|S - s μ| ≤ s δ`, the perturbation of Thompson sampling with
the Jeffreys prior exceeds `c` with probability at most `exp (-s β)`. -/
theorem exists_expFamilyTSStackLaw_jeffreysPrior_Ioi_le {μ c β : ℝ}
    (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans id)
    (hc : c ∈ ρ.expFamilyMeans id) (hμc : μ < c)
    (hprop : ∃ s₀ S₀, ρ.expFamilyPosterior id (ρ.jeffreysPrior id) s₀ S₀ ≠ 0)
    (hβd : β < ρ.expFamilyDiv id μ c) :
    ∃ δ > 0, μ - δ ∈ ρ.expFamilyMeans id ∧ μ + δ ∈ ρ.expFamilyMeans id ∧
      ∃ N : ℕ, ∀ s ≥ N, ∀ S, |S - s * μ| ≤ s * δ →
        expFamilyTSStackLaw ρ (ρ.jeffreysPrior id) s S (Ioi (c : EReal)) ≤
          ENNReal.ofReal (exp (-(s * β))) := by
  obtain ⟨s₀, S₀, hprop⟩ := hprop
  obtain ⟨δ, hδ, hδc, hlo, hhi, hβδ⟩ := exists_accuracy hT hμ hc hμc hβd
  set b := ρ.expFamilyDiv id μ c - δ * (ρ.natParam id c - ρ.natParam id μ) with hb
  -- on the accuracy event, the posterior is proper after `N₁` observations
  obtain ⟨N₁, hN₁⟩ := Measure.exists_forall_expFamilyPosterior_jeffreysPrior_ne_zero hT hμ
    (by linarith : δ < 2 * δ) hlo hhi hprop
  have hZ := (Measure.expFamilyPosterior_jeffreysPrior_ne_zero_iff hT hμ).1
    (hN₁ N₁ le_rfl (N₁ * (μ + δ)) (by
      rw [show (N₁ : ℝ) * (μ + δ) - N₁ * μ = N₁ * δ by ring, abs_of_nonneg (by positivity)]))
  -- the posterior probability of `c ≤ ψ'(θ)` is at most `C s exp (-s b)` [KKM13, Theorem 4]
  obtain ⟨C, N₂, hN₂⟩ := Measure.exists_expFamilyPosterior_jeffreysPrior_setOf_le_deriv_cgf_le
    hT hμ hc hδ.le hδc N₁ hZ
  rw [← hb] at hN₂
  -- `C s ≤ exp (s (b - β))`, so `C s exp (-s b) ≤ exp (-s β)`, for `s ≥ N₃`
  set N₃ := ⌈2 * C / (b - β) ^ 2⌉₊
  have hN₃ (s : ℕ) (hs : N₃ ≤ s) : C * s * exp (-(s * b)) ≤ exp (-(s * β)) := by
    have hs' : 2 * C / (b - β) ^ 2 ≤ s := (Nat.le_ceil _).trans (by exact_mod_cast hs)
    rw [div_le_iff₀ (by nlinarith)] at hs'
    have h_exp := quadratic_le_exp_of_nonneg (by nlinarith : (0 : ℝ) ≤ s * (b - β))
    have h_le : C * s ≤ exp (s * (b - β)) := by
      nlinarith [mul_le_mul_of_nonneg_right hs' (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
    calc C * s * exp (-(s * b)) ≤ exp (s * (b - β)) * exp (-(s * b)) := by gcongr
      _ = exp (-(s * β)) := by
          rw [← exp_add]
          ring_nf
  refine ⟨δ, hδ, Measure.Icc_subset_expFamilyMeans hlo hhi ⟨by linarith, by linarith⟩,
    Measure.Icc_subset_expFamilyMeans hlo hhi ⟨by linarith, by linarith⟩,
    max (max N₁ N₂) (max N₃ 1), fun s hs S hS ↦ ?_⟩
  simp only [ge_iff_le, max_le_iff] at hs
  rw [expFamilyTSStackLaw_Ioi (by omega) (hN₁ s hs.1.1 S hS) c]
  calc ρ.expFamilyPosterior id (ρ.jeffreysPrior id) s S {θ | c < deriv (cgf id ρ) θ}
      ≤ ρ.expFamilyPosterior id (ρ.jeffreysPrior id) s S {θ | c ≤ deriv (cgf id ρ) θ} :=
        measure_mono (ofPred_subset_ofPred.2 fun _ hθ ↦ hθ.le)
    _ ≤ ENNReal.ofReal (C * s * exp (-(s * b))) := hN₂ s hs.1.2 S hS
    _ ≤ ENNReal.ofReal (exp (-(s * β))) := ENNReal.ofReal_le_ofReal (hN₃ s hs.2.1)

end LMLExplore.Bandits

namespace ProbabilityTheory

open LMLExplore LMLExplore.Bandits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℕ → Ω → ℝ} {ρ : Measure ℝ}
  {μ c β : ℝ}

/-- **Over-sampling by Thompson sampling with the Jeffreys prior** [KKM13, Lemma 6 and term (B) of
the proof of Theorem 2]. Let `X₀, X₁, …` be independent and dominated by the member of mean `μ` of
the natural exponential family of `ρ`, let `c > μ` be a mean of the family, and let the posterior of
the Jeffreys prior be proper after some observations. Write `G_s` for the probability that the
perturbation of Thompson sampling with the Jeffreys prior, after the observations
`X₀, …, X_{s-1}`, exceeds `c`. Then for every `0 < β < d(μ, c)` there is a constant `C` such that
for every horizon `n`, the expected number of sample sizes `s < n` with `G_s > 1 / n` is at most
`log n / β + C`. -/
theorem iIndepFun.exists_sum_measure_inv_lt_expFamilyTSStackLaw_jeffreysPrior_Ioi_le
    (h_indep : iIndepFun X P)
    (hX : ∀ k, MGFDominatedOn (X k) P id (ρ.expFamily id (ρ.natParam id μ)) univ)
    (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans id)
    (hc : c ∈ ρ.expFamilyMeans id) (hμc : μ < c)
    (hprop : ∃ s₀ S₀, ρ.expFamilyPosterior id (ρ.jeffreysPrior id) s₀ S₀ ≠ 0)
    (hβ : 0 < β) (hβd : β < ρ.expFamilyDiv id μ c) :
    ∃ C : ℝ, ∀ n : ℕ, ∑ s ∈ Finset.range n, P {ω | (n : ℝ≥0∞)⁻¹ <
        expFamilyTSStackLaw ρ (ρ.jeffreysPrior id) s (∑ k ∈ Finset.range s, X k ω)
          (Ioi (c : EReal))} ≤ ENNReal.ofReal (log n / β + C) := by
  have := h_indep.isProbabilityMeasure
  obtain ⟨δ, hδ, hlo, hhi, N, hN⟩ :=
    exists_expFamilyTSStackLaw_jeffreysPrior_Ioi_le hT hμ hc hμc hprop hβd
  set a₁ := ρ.expFamilyDiv id (μ + δ) μ
  set a₂ := ρ.expFamilyDiv id (μ - δ) μ
  have ha₁ : 0 < a₁ := Measure.expFamilyDiv_pos hhi hμ (by linarith)
  have ha₂ : 0 < a₂ := Measure.expFamilyDiv_pos hlo hμ (by linarith)
  -- the probability of the sample size `s` is at most `1` if `s < N` or `s β ≤ log n`, and
  -- otherwise at most the probability that the empirical mean is off by `δ`
  have h_term (n s : ℕ) : P {ω | (n : ℝ≥0∞)⁻¹ <
      expFamilyTSStackLaw ρ (ρ.jeffreysPrior id) s (∑ k ∈ Finset.range s, X k ω)
        (Ioi (c : EReal))} ≤ ENNReal.ofReal ((if s < N then 1 else 0) +
          (if s * β ≤ log n then 1 else exp (-(a₁ * s))) + exp (-(a₂ * s))) := by
    by_cases h : s < N ∨ s * β ≤ log n
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (0 : ℝ) ≤ if s < N then 1 else 0 := by positivity
      have h2 : (0 : ℝ) ≤ if s * β ≤ log n then 1 else exp (-(a₁ * s)) := by positivity
      rcases h with h | h
      · simp only [h, ite_true] at h1 ⊢
        linarith [exp_pos (-(a₂ * s))]
      · simp only [h, ite_true] at h2 ⊢
        linarith [exp_pos (-(a₂ * s))]
    push Not at h
    obtain ⟨hsN, hlog⟩ := h
    simp only [not_lt.2 hsN, not_le.2 hlog, ite_false, zero_add]
    have h_dev := h_indep.measureReal_sum_ge_or_sum_le_le_exp_add_exp_expFamilyDiv
      (s := Finset.range s) (fun k _ ↦ hX k) hμ hhi hlo (by linarith) (by linarith)
    rw [Finset.card_range, mul_comm (s : ℝ) a₁, mul_comm (s : ℝ) a₂] at h_dev
    refine (measure_mono fun ω hω ↦ ?_).trans
      ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 h_dev)
    -- with an accurate empirical mean, `1 / n < G_s ≤ exp (-s β)` forces `s β < log n`
    by_contra h_not
    simp only [mem_ofPred_eq, not_or, not_le] at hω h_not
    have hlt := hω.trans_le (hN s hsN _ (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩))
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hlt
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (exp_pos _)] at hlt
    have h_log := Real.log_lt_log (by positivity) hlt
    rw [Real.log_inv, Real.log_exp] at h_log
    linarith
  -- summing over the sample sizes: at most `N` sizes below `N`, at most `1 + log n / β` sizes
  -- with `s β ≤ log n`, and two geometric series
  refine ⟨N + (1 + a₁⁻¹) + (1 + a₂⁻¹), fun n ↦ ?_⟩
  refine (Finset.sum_le_sum fun s _ ↦ h_term n s).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun s _ ↦ by positivity]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 : ∑ s ∈ Finset.range n, (if s < N then (1 : ℝ) else 0) ≤ N := by
    rw [Finset.sum_boole]
    exact_mod_cast (Finset.card_le_card fun s hs ↦
      Finset.mem_range.2 (Finset.mem_filter.1 hs).2).trans (Finset.card_range N).le
  have h2 := sum_range_ite_mul_le_exp_neg_mul_le hβ (log_natCast_nonneg n) ha₁ n
  have h3 := sum_range_exp_neg_mul_le_one_add_inv ha₂ n
  linarith

end ProbabilityTheory

namespace LMLExplore.Bandits

/-- **Over-sampling by Thompson sampling with the Jeffreys prior in the reward-stack model.** Let
the rewards of arm `i` be dominated by the member of mean `μ` of the natural exponential family of
`ρ`, let `c > μ` be a mean of the family, and let the posterior of the Jeffreys prior be proper
after some observations. In the reward-stack model `streamMeasure ν`, write `G_{i s}` for the
probability that the perturbation of `i` after its first `s` rewards exceeds `c`. Then for every
`0 < β < d(μ, c)` there is a constant `C` such that for every horizon `n`, the expected number of
sample sizes `s < n` with `G_{i s} > 1 / n` is at most `log n / β + C`. -/
theorem exists_sum_streamMeasure_inv_lt_expFamilyTSStackLaw_jeffreysPrior_Ioi_le {α : Type*}
    [MeasurableSpace α] {ν : Kernel α ℝ} [IsMarkovKernel ν] {i : α} {μ c β : ℝ}
    (hν : MGFDominatedOn id (ν i) id (ρ.expFamily id (ρ.natParam id μ)) univ)
    (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ] fun _ ↦ c) (hμ : μ ∈ ρ.expFamilyMeans id)
    (hc : c ∈ ρ.expFamilyMeans id) (hμc : μ < c)
    (hprop : ∃ s₀ S₀, ρ.expFamilyPosterior id (ρ.jeffreysPrior id) s₀ S₀ ≠ 0)
    (hβ : 0 < β) (hβd : β < ρ.expFamilyDiv id μ c) :
    ∃ C : ℝ, ∀ n : ℕ, ∑ s ∈ Finset.range n, streamMeasure ν {x | (n : ℝ≥0∞)⁻¹ <
        expFamilyTSStackLaw ρ (ρ.jeffreysPrior id) s (∑ k ∈ Finset.range s, x k i)
          (Ioi (c : EReal))} ≤ ENNReal.ofReal (log n / β + C) :=
  iIndepFun.exists_sum_measure_inv_lt_expFamilyTSStackLaw_jeffreysPrior_Ioi_le
    (iIndepFun_eval_streamMeasure'' ν i)
    (fun k ↦ (identDistrib_eval_eval_id_streamMeasure ν k i).mgfDominatedOn.trans hν)
    hT hμ hc hμc hprop hβ hβd

namespace ExpFamilyTS

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {ρ : α → Measure ℝ} [∀ a, SFinite (ρ a)]

/-- **[LS, Theorem 36.2] for Thompson sampling with the Jeffreys prior, with the over-sampling
bound** [KKM13, term (B) of the proof of Theorem 2]. In a run of Thompson sampling with the
Jeffreys priors of the families `ρ a` against the stochastic bandit `Environment.bandit ν`, let
`i ≠ j` be arms, let the rewards of `i` be dominated by the member of mean `μ` of the family
`ρ i`, let `c > μ` be a mean of that family, and let its Jeffreys posterior be proper after some
observations. Then for every `0 < β < d(μ, c)` there is a constant `C` such that for every
horizon `n`, `E[T_i(n)] ≤ 1 + E[∑_{s < n} (G_{j s}⁻¹ - 1)] + log n / β + C`, where `G_{j s}` is the
probability that the perturbation of arm `j` after its first `s` rewards in the reward-stack model
`streamMeasure ν` exceeds `c`. -/
theorem exists_lintegral_pullCount_le_add_log [IsProbabilityMeasure P] {ν : Kernel α ℝ}
    [IsMarkovKernel ν]
    (h : IsAlgEnvSeq O A R (expFamilyTS ρ fun a ↦ (ρ a).jeffreysPrior id)
      (Environment.bandit ν) P)
    {i j : α} (hij : i ≠ j) {μ c β : ℝ}
    (hν : MGFDominatedOn id (ν i) id ((ρ i).expFamily id ((ρ i).natParam id μ)) univ)
    (hT : ∀ c, ¬ (id : ℝ → ℝ) =ᵐ[ρ i] fun _ ↦ c) (hμ : μ ∈ (ρ i).expFamilyMeans id)
    (hc : c ∈ (ρ i).expFamilyMeans id) (hμc : μ < c)
    (hprop : ∃ s₀ S₀, (ρ i).expFamilyPosterior id ((ρ i).jeffreysPrior id) s₀ S₀ ≠ 0)
    (hβ : 0 < β) (hβd : β < (ρ i).expFamilyDiv id μ c) :
    ∃ C : ℝ, ∀ n : ℕ, ∫⁻ ω, (pullCount A i n ω : ℝ≥0∞) ∂P ≤
      1 + ∑ s ∈ Finset.range n, ∫⁻ x,
          (expFamilyTSStackLaw (ρ j) ((ρ j).jeffreysPrior id) s (∑ k ∈ Finset.range s, x k j)
            (Ioi (c : EReal)))⁻¹ - 1 ∂(streamMeasure ν) +
        ENNReal.ofReal (log n / β + C) := by
  obtain ⟨C, hC⟩ := exists_sum_streamMeasure_inv_lt_expFamilyTSStackLaw_jeffreysPrior_Ioi_le hν hT
    hμ hc hμc hprop hβ hβd
  exact ⟨C, fun n ↦ (lintegral_pullCount_le h hij c n).trans (add_le_add le_rfl (hC n))⟩

end ExpFamilyTS

end LMLExplore.Bandits
