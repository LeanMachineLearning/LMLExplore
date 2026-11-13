/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Identification.Task.Classical
public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.SequentialLearning.ExpFamilyDeviation
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# `δ`-correct GLR thresholds for arms dominated by exponential families

Let the models of an identification task be vectors of means `μ : α → ℝ` of arms with real
observations, and let the arm `a` be described by the exponential family `(ρ a, T a)` on a
measurable space `𝓧`, with extended divergence `dbar_a(x, μ_a)`
(`MeasureTheory.Measure.expFamilyRate`): the Cramér rate function at `x` of the statistic `T a`
under the member of mean `μ_a`. After `n` rounds with history `h`, pull counts `N_a` and empirical
means `μ̂_a`, the *generalized likelihood ratio evidence* of the arms of a set `S` against a vector
of means `λ` is `Z_n(h, λ) = ∑ a ∈ S, N_a dbar_a(μ̂_a, λ_a)`
(`LMLExplore.Identification.expFamilyEvidence`); the evidence of all the arms is the case
`S = univ`. When the divergences between the arm laws are those of the families, the value of the
evidence of all the arms at a vector of means of the families is the plug-in statistic of the
empirical means (`IdentTask.plugInCost`) as long as the empirical means are means of the families,
and it extends that statistic to empirical means on the boundary of the means, such as the
empirical means `0` and `1` of Bernoulli arms, where the plug-in statistic of the empirical means
is not meaningful.

If the rewards of each arm `a` of the model `μ` are dominated, in moment generating function, by
the member of mean `μ a` of `(ρ a, T a)`, then along a run of any sampling rule the evidence
against `μ` exceeds `K log (2 n (n + 1)) + x` at some round `n` with probability at most
`f(x) = (x / K) ^ K exp (K - x)` for `x ≥ K`, where `K` is the number of arms
(`LMLExplore.measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le`). Hence the
GLRT with this evidence and the thresholds `K log (2 n (n + 1)) + x` stops with an incorrect
answer with probability at most `f(x)`, for every task and every sampling rule, and with the level
`x_δ` of `Identification/GLR.lean` it is `δ`-correct [GK16, Proposition 12; LS, Lemma 33.7].
Gaussian arms of variance `σ²` are the members of the family of `𝒩(0, σ²)` with the identity
statistic, for which the evidence is `∑ a, N_a (μ̂_a - λ_a)² / (2 σ²)`, the statistic of
`Identification/GaussianThreshold.lean`; Bernoulli arms, and rewards in `[0, 1]`, which are
dominated by the Bernoulli law of the same mean, are other instances.

The threshold `K log (2 n (n + 1)) + x` grows with the number of arms, because the evidence of all
the arms is controlled at once. The same bound holds for the evidence `∑ a ∈ S, N_a dbar_a` of the
arms of any set `S`, with `#S` in place of `K`. In best arm identification, a wrong answer `i` is
ruled out by the evidence of the pair `i, b` on the half-space `{λ | λ i ≤ λ b}`, for each
`b ≠ i`, and the GLRT with these pieces (`LMLExplore.Identification.coverGlrt`) only errs when the
evidence of a pair of the best arm `a` with another arm against the true model exceeds its
threshold `2 log (2 n (n + 1)) + x`. A union bound over the `K - 1` such pairs makes it `δ`-correct
with the level `x_{δ / (K - 1)}`, a threshold of order `4 log n + log (K / δ)` [GK16,
Proposition 12]. Top-`m` identification is the same, with the pairs of an arm outside the `m`
best arms and an arm among them.

Peeling the numbers of pulls of each arm over dyadic slices instead of a union bound over them
(`LMLExplore.measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_expFamilyRate_le`) bounds by
`f(x)` the probability that the evidence against `μ` exceeds
`2 (K (η log₂ n + log (2 / (1 - exp (-η)))) + x)` at some round, for every `η > 0`. With
`η = p log 2 / (2 K)` these thresholds are at most `p log n + c_{p,K} + 2 x`, where
`c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))`, since `log₂ n log 2 ≤ log n`. Hence the
thresholds `log (C n ^ p / δ)` of [GK16, Proposition 12] are `δ`-correct, for every exponent
`p > 0`, as soon as `C ≥ δ exp (c_{p,K} + 2 x_δ)`. The constant depends on `δ`, through
`x_δ = log (1 / δ) + O(log log (1 / δ))`: [GK16] states the result with a constant `C(α, K)`
independent of `δ`, which its proof does not give, since the last step of the proof drops the `δ`
inside the logarithm of the condition on `C`.
The deviational thresholds are adapted from the formalization in the Garivier2016Optimal project
(Rémy Degenne, <https://github.com/RemyDegenne/Garivier2016Optimal>, file
`Garivier2016Optimal/ForLMLExplore/Identification/DeviationalThreshold.lean`).

## Main definitions

* `LMLExplore.Identification.expFamilyEvidence ρ T S n h λ`: the generalized likelihood ratio
  evidence `∑ a ∈ S, N_a dbar_a(μ̂_a, λ_a)` of the arms of `S` against the vector of means `λ`.

## Main statements

* `LMLExplore.Identification.IdentTask.plugInCost_empMean'_eq_expFamilyEvidence`: when the
  divergences between the arm laws are those of the families and the empirical means are means of
  the families, the evidence is the plug-in statistic of the empirical means.
* `LMLExplore.Identification.measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le`:
  along a run of any sampling rule on the model `μ`, the evidence of the arms of `S` against `μ`
  exceeds the threshold `#S log (2 n (n + 1)) + x` at some round with probability at most
  `(x / #S) ^ #S exp (#S - x)`; the `_univ` form states the case `S = univ` of all the arms.
* `LMLExplore.Identification.measure_exists_mem_exists_unionBoundThreshold_lt_expFamilyEvidence_le`:
  for a set `Q` of pairs of distinct arms, the evidence of some pair of `Q` exceeds the threshold
  `2 log (2 n (n + 1)) + x` at some round with probability at most `#Q (x / 2) ^ 2 exp (2 - x)`;
  its real-measure form is
  `measureReal_exists_mem_exists_unionBoundThreshold_lt_expFamilyEvidence_le`.
* `LMLExplore.Identification.IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_le`:
  for every task and every sampling rule, the GLRT with the evidence and these thresholds stops with
  an answer that is not correct for `μ` with probability at most `f(x)`.
* `LMLExplore.Identification.IdentTask.isDeltaPAC_glrt_expFamilyEvidence`: with the level `x_δ`,
  the GLRT is `δ`-PAC on the task as soon as it stops almost surely on every admissible model.
* `LMLExplore.Identification.measureReal_histOutputMeasure_coverGlrt_baiTask_le`,
  `LMLExplore.Identification.isDeltaPAC_coverGlrt_baiTask`: the pairwise GLRT of best arm
  identification errs with probability at most `(K - 1) (x / 2) ^ 2 exp (2 - x)`, and is `δ`-PAC
  with the level `x_{δ / (K - 1)}`.
* `LMLExplore.Identification.measureReal_histOutputMeasure_coverGlrt_topMTask_le`,
  `LMLExplore.Identification.isDeltaPAC_coverGlrt_topMTask`: the pairwise GLRT of top-`m`
  identification errs with probability at most `(K - m) m (x / 2) ^ 2 exp (2 - x)`, and is `δ`-PAC
  with the level `x_{δ / ((K - m) m)}`.
* `LMLExplore.Identification.measure_exists_lt_expFamilyEvidence_le_of_le`,
  `LMLExplore.Identification.measure_exists_lt_expFamilyEvidence_le_of_mul_log_le`: along a run of
  any sampling rule, the evidence of the arms of `S` against `μ` exceeds thresholds at least
  `2 (#S (η log₂ n + log (2 / (1 - exp (-η)))) + x)`, or at least `p log n + c_{p,#S} + 2 x`, at
  some round with probability at most `(x / #S) ^ #S exp (#S - x)`.
* `IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_le_of_mul_log_le`: the GLRT
  with thresholds at least `p log n + c_{p,K} + 2 x` stops with an incorrect answer with
  probability at most `f(x)`.
* `IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_log_mul_rpow_div_le`:
  [GK16, Proposition 12], with `C ≥ δ exp (c_{p,K} + 2 x_δ)`: the GLRT with the thresholds
  `log (C n ^ p / δ)` stops with an incorrect answer with probability at most `δ`.
* `IdentTask.isDeltaPAC_glrt_expFamilyEvidence_log_mul_rpow_div`: with these thresholds, the GLRT
  is `δ`-PAC as soon as it stops almost surely on every model.

## References

* [GC11] A. Garivier and O. Cappé, *The KL-UCB algorithm for bounded stochastic bandits and
  beyond*, COLT 2011, Theorem 10, for the peeling.
* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real

open scoped ENNReal Finset

namespace LMLExplore.Identification

variable {α 𝓧 : Type*} [DecidableEq α] {m𝓧 : MeasurableSpace 𝓧} {ρ : α → Measure 𝓧}
  {T : α → 𝓧 → ℝ}

/-- The *generalized likelihood ratio evidence* of the arms of a set `S` against the vector of
means `λ` after `n` rounds with history `h`, for arms described by the exponential families
`(ρ a, T a)`: `∑ a ∈ S, N_a dbar_a(μ̂_a, λ_a)`, with the pull counts `N_a` and the empirical means
`μ̂_a` of `h` and the extended divergence `dbar_a` of the family of `a`
(`MeasureTheory.Measure.expFamilyRate`). The evidence of all the arms is the case `S = univ`; the
evidence of a pair of arms `{a, b}` is the statistic of the pairwise stopping rules of best arm
identification. -/
noncomputable def expFamilyEvidence (ρ : α → Measure 𝓧) (T : α → 𝓧 → ℝ) (S : Finset α) (n : ℕ)
    (h : Hist Unit α ℝ n) (l : α → ℝ) : ℝ≥0∞ :=
  ∑ a ∈ S, pullCount' n h a * (ρ a).expFamilyRate (T a) (empMean' n h a) (l a)

lemma expFamilyEvidence_def (ρ : α → Measure 𝓧) (T : α → 𝓧 → ℝ) (S : Finset α) (n : ℕ)
    (h : Hist Unit α ℝ n) (l : α → ℝ) :
    expFamilyEvidence ρ T S n h l =
      ∑ a ∈ S, pullCount' n h a * (ρ a).expFamilyRate (T a) (empMean' n h a) (l a) :=
  (rfl)

/-- The evidence against a vector of means is a measurable function of the history. -/
lemma measurable_expFamilyEvidence {mα : MeasurableSpace α} [MeasurableSingletonClass α]
    (S : Finset α) (n : ℕ) (l : α → ℝ) :
    Measurable fun h : Hist Unit α ℝ n ↦ expFamilyEvidence ρ T S n h l := by
  simp_rw [expFamilyEvidence_def]
  refine Finset.measurable_sum _ fun a _ ↦ Measurable.mul ?_ ?_
  · exact measurable_from_nat.comp (measurable_pullCount' n a)
  · exact (Measure.lowerSemicontinuous_expFamilyRate_left (l a)).measurable.comp
      (measurable_empMean' n a)

namespace IdentTask

variable [Fintype α] {ℐ : Type*} {mα : MeasurableSpace α} {task : IdentTask α (α → ℝ) ℐ ℝ}

/-- When the divergences between the arm laws are those of the families on their vectors of means,
the evidence against a vector `λ` of means of the families is the plug-in statistic of the
empirical means, as long as the empirical means `μ̂_a` of the history are means of the families. -/
lemma plugInCost_empMean'_eq_expFamilyEvidence
    (hν : ∀ μ μ' : α → ℝ, (∀ c, μ c ∈ (ρ c).expFamilyMeans (T c)) →
      (∀ c, μ' c ∈ (ρ c).expFamilyMeans (T c)) →
      ∀ c, klDiv (task.ν μ c) (task.ν μ' c) =
        ENNReal.ofReal ((ρ c).expFamilyDiv (T c) (μ c) (μ' c)))
    {n : ℕ} {h : Hist Unit α ℝ n} (hemp : ∀ a, empMean' n h a ∈ (ρ a).expFamilyMeans (T a))
    {l : α → ℝ} (hl : ∀ a, l a ∈ (ρ a).expFamilyMeans (T a)) :
    task.plugInCost empMean' n h l = expFamilyEvidence ρ T Finset.univ n h l := by
  rw [plugInCost_def, cost_def, expFamilyEvidence_def]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hν _ _ hemp hl a, ENNReal.ofReal_natCast,
    Measure.expFamilyRate_eq_ofReal_expFamilyDiv (hemp a) (hl a)]

end IdentTask

variable {mα : MeasurableSpace α} [MeasurableSingletonClass α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ}
  {O : ℕ → Ω → Unit} {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {μ : α → ℝ} {x δ : ℝ}

/-- **Deviation of the generalized likelihood ratio evidence for arms dominated by exponential
families**, along a run of any sampling rule, for the arms of a set `S`. If the rewards of each arm
`a ∈ S` of the bandit `ν` are dominated on `Set.univ`, in moment generating function, by the member
of mean `μ a` of the exponential family `(ρ a, T a)`, then for a level `x ≥ #S`, the probability
that at some round `n` the evidence of the arms of `S` against `μ` exceeds the threshold
`#S log (2 n (n + 1)) + x` is at most `(x / #S) ^ #S exp (#S - x)`. -/
theorem measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le [Countable α]
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (S : Finset α)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hx : (#S : ℝ) ≤ x) :
    P {ω | ∃ n, unionBoundThreshold #S x n < expFamilyEvidence ρ T S n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le hseq S hμ hν hx)
  obtain ⟨n, hn⟩ := hω
  rw [unionBoundThreshold_def] at hn
  refine ⟨n, hn.le.trans_eq ?_⟩
  simp only [expFamilyEvidence_def, pullCount_eq_pullCount' (O := O) (R' := R),
    empMean_eq_empMean' (O := O)]

/-- **Deviation of the generalized likelihood ratio evidence for arms dominated by exponential
families**, along a run of any sampling rule, for all the `K` arms: the case `S = univ` of
`measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le`. If the rewards of each arm `a` of the
bandit `ν` are dominated on `Set.univ`, in moment generating function, by the member of mean `μ a`
of the exponential family `(ρ a, T a)`, then for a level `x ≥ K`, the probability that at some
round `n` the evidence against `μ` exceeds the threshold `K log (2 n (n + 1)) + x` is at most
`(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le_univ [Countable α] [Fintype α]
    {ν : Kernel α ℝ} [IsMarkovKernel ν] (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hx : Fintype.card α ≤ x) :
    P {ω | ∃ n, unionBoundThreshold (Fintype.card α) x n <
        expFamilyEvidence ρ T Finset.univ n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  have h_dev := measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le Finset.univ
    (fun a _ ↦ hμ a) (fun a _ ↦ hν a) hseq (x := x) (by rwa [Finset.card_univ])
  rwa [Finset.card_univ] at h_dev

namespace IdentTask

variable [Fintype α] {ℐ : Type*} {task : IdentTask α (α → ℝ) ℐ ℝ} {mℐ : MeasurableSpace ℐ}
  (rec : (n : ℕ) → Hist Unit α ℝ n → ℐ) (hrec : ∀ n, Measurable (rec n))

/-- **Error probability of the GLRT for arms dominated by exponential families**
([GK16, Proposition 12], [LS, Lemma 33.7]), for every task and every sampling rule. If the rewards
of each arm `a` of an admissible model `μ` are dominated on `Set.univ`, in moment generating
function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for a level
`x ≥ K`, the GLRT with the generalized likelihood ratio evidence and the thresholds
`K log (2 n (n + 1)) + x` stops with an answer that is not correct for `μ` with probability at most
`(x / K) ^ K exp (K - x)`. -/
theorem measureReal_histOutputMeasure_glrt_expFamilyEvidence_le
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α) x n <
      task.glr (expFamilyEvidence ρ T Finset.univ) n h (rec n h)})
    (hμM : μ ∈ task.M) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hc : MeasurableSet (task.correct μ)) (hx : Fintype.card α ≤ x) :
    (histOutputMeasure
        (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n) rec hrec hstop)
          (Environment.bandit (task.ν μ))).real
        {p | p.1 ∈ (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n) rec hrec hstop).stopSet ∧
          p.2 ∉ task.correct μ} ≤
      (x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x) := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (task.ν μ))
  refine (task.measureReal_histOutputMeasure_glrt_le (expFamilyEvidence ρ T Finset.univ) alg _ rec
    hrec hstop hseq hμM hc).trans ?_
  rw [measureReal_def]
  have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hx
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le_univ hμ hν hseq hx)

/-- **The GLRT for arms dominated by exponential families is `δ`-PAC**
([GK16, Proposition 12], [LS, Lemma 33.7]), for every task and every sampling rule. If on every
admissible model `μ` the rewards of each arm `a` are dominated on `Set.univ`, in moment generating
function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for
`δ ∈ (0, 1]`, the GLRT with the generalized likelihood ratio evidence and the thresholds
`K log (2 n (n + 1)) + x_δ` is `δ`-PAC on the task, provided it stops almost surely on every
admissible model. -/
theorem isDeltaPAC_glrt_expFamilyEvidence (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) δ) n <
        task.glr (expFamilyEvidence ρ T Finset.univ) n h (rec n h)})
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) δ := by
  refine task.isDeltaPAC_glrt (expFamilyEvidence ρ T Finset.univ) alg _ rec hrec hstop hc
    (fun θ hθ ↦ ?_) h_stops
  rw [measureReal_def]
  have h_dev := measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le_univ (hμ θ hθ)
    (hν θ hθ) (IT.isAlgEnvSeq_trajMeasure alg _) (card_le_unionBoundLevel hδ hδ1)
  exact ENNReal.toReal_le_of_le_ofReal hδ.le
    (h_dev.trans (ENNReal.ofReal_le_ofReal (div_pow_mul_exp_sub_unionBoundLevel_le hδ hδ1)))

end IdentTask

/-! ### The deviational thresholds `log (C n ^ p / δ)` -/

section Deviational

/-- With `η = p log 2 / (2 K)`, the peeled thresholds `2 K (η log₂ n + κ)` are at most
`p log n + 2 K κ`, since `log₂ n log 2 ≤ log n`. -/
private lemma two_mul_card_mul_le {p : ℝ} (hp : 0 < p) {K : ℕ} (hK : K ≠ 0) (n : ℕ) (κ : ℝ) :
    2 * (K * (p * log 2 / (2 * K) * Nat.log 2 n + κ)) ≤ p * log n + 2 * K * κ := by
  have h := Real.natLog_le_logb n 2
  rw [Real.logb, Nat.cast_ofNat, le_div_iff₀ (log_pos one_lt_two)] at h
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK)
  calc 2 * (K * (p * log 2 / (2 * K) * Nat.log 2 n + κ))
  _ = p * (Nat.log 2 n * log 2) + 2 * K * κ := by field_simp
  _ ≤ p * log n + 2 * K * κ := by gcongr

/-- For `C ≥ δ exp (c + 2 x)` and `n ≥ 1`, the threshold `log (C n ^ p / δ)` is at least
`p log n + c + 2 x`. -/
private lemma mul_log_add_le_log_mul_rpow_div {p C δ c x : ℝ} (hδ : 0 < δ)
    (hC : δ * exp (c + 2 * x) ≤ C) {n : ℕ} (hn : n ≠ 0) :
    p * log n + c + 2 * x ≤ log (C * n ^ p / δ) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have h := log_le_log (by positivity) hC
  rw [log_mul hδ.ne' (exp_pos _).ne', log_exp] at h
  rw [log_div (by positivity) hδ.ne', log_mul hC0.ne' (by positivity), log_rpow hn]
  linarith

variable {β : (n : ℕ) → Hist Unit α ℝ n → ℝ≥0∞} {p : ℝ}

/-- **Peeled deviation of the generalized likelihood ratio evidence for arms dominated by
exponential families**, along a run of any sampling rule, for the arms of a set `S`. If the
rewards of each arm `a ∈ S` of the bandit `ν` are dominated on `Set.univ`, in moment generating
function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for `η > 0`, a
level `x ≥ #S` and thresholds `β` at least `2 (#S (η log₂ n + log (2 / (1 - exp (-η)))) + x)` at
every round `n ≥ 1`, with `log₂ n = Nat.log 2 n`, the probability that at some round the evidence
of the arms of `S` against `μ` exceeds the threshold is at most `(x / #S) ^ #S exp (#S - x)`. -/
theorem measure_exists_lt_expFamilyEvidence_le_of_le [Countable α] {ν : Kernel α ℝ}
    [IsMarkovKernel ν] (S : Finset α) {η : ℝ} (hη : 0 < η)
    (hβ : ∀ n, n ≠ 0 → ∀ h, ENNReal.ofReal (2 * (#S *
      (η * Nat.log 2 n + log (2 / (1 - exp (-η)))) + x)) ≤ β n h)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hx : (#S : ℝ) ≤ x) :
    P {ω | ∃ n, β n (history O A R n ω) < expFamilyEvidence ρ T S n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_two_mul_card_mul_add_le_sum_pullCount_mul_expFamilyRate_le hseq S hμ hν hη
      hx)
  obtain ⟨n, hn⟩ := hω
  have h_eq : expFamilyEvidence ρ T S n (history O A R n ω) μ =
      ∑ a ∈ S, pullCount A a n ω * (ρ a).expFamilyRate (T a) (empMean A R a n ω) (μ a) := by
    simp only [expFamilyEvidence_def, pullCount_eq_pullCount' (O := O) (R' := R),
      empMean_eq_empMean' (O := O)]
  -- no arm is pulled before the first round, so the evidence vanishes there
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [h_eq] at hn
    simp at hn
  exact ⟨n, (hβ n hn0 _).trans (hn.le.trans_eq h_eq)⟩

/-- **Deviation of the generalized likelihood ratio evidence for arms dominated by exponential
families, for thresholds `p log n + c_{p,#S} + 2 x`**, along a run of any sampling rule, for the
arms of a nonempty set `S`. If the rewards of each arm `a ∈ S` of the bandit `ν` are dominated on
`Set.univ`, in moment generating function, by the member of mean `μ a` of the exponential family
`(ρ a, T a)`, then for `p > 0`, a level `x ≥ #S` and thresholds `β` at least
`p log n + c_{p,#S} + 2 x` at every round `n ≥ 1`, where
`c_{p,k} = 2 k log (2 / (1 - exp (-(p log 2 / (2 k)))))`, the probability that at some round the
evidence of the arms of `S` against `μ` exceeds the threshold is at most
`(x / #S) ^ #S exp (#S - x)`. -/
theorem measure_exists_lt_expFamilyEvidence_le_of_mul_log_le [Countable α] {ν : Kernel α ℝ}
    [IsMarkovKernel ν] {S : Finset α} (hS : S.Nonempty) (hp : 0 < p)
    (hβ : ∀ n : ℕ, n ≠ 0 → ∀ h, ENNReal.ofReal (p * log n + 2 * #S *
      log (2 / (1 - exp (-(p * log 2 / (2 * #S))))) + 2 * x) ≤ β n h)
    (hμ : ∀ a ∈ S, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a ∈ S, MGFDominatedOn id (ν a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit ν) P) (hx : (#S : ℝ) ≤ x) :
    P {ω | ∃ n, β n (history O A R n ω) < expFamilyEvidence ρ T S n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / #S) ^ #S * exp (#S - x)) := by
  have hη : 0 < p * log 2 / (2 * #S) := by
    have := log_pos one_lt_two
    have := hS.card_pos
    positivity
  refine measure_exists_lt_expFamilyEvidence_le_of_le S hη
    (fun n hn h ↦ (ENNReal.ofReal_le_ofReal ?_).trans (hβ n hn h)) hμ hν hseq hx
  linarith [two_mul_card_mul_le hp hS.card_pos.ne' n
    (log (2 / (1 - exp (-(p * log 2 / (2 * #S))))))]

namespace IdentTask

variable [Fintype α] {ℐ : Type*} {task : IdentTask α (α → ℝ) ℐ ℝ} {mℐ : MeasurableSpace ℐ}
  (rec : (n : ℕ) → Hist Unit α ℝ n → ℐ) (hrec : ∀ n, Measurable (rec n))

/-- **Error probability of the GLRT for arms dominated by exponential families, with thresholds
`p log n + c_{p,K} + 2 x`**, for every task and every sampling rule. If the rewards of each arm `a`
of an admissible model `μ` are dominated on `Set.univ`, in moment generating function, by the
member of mean `μ a` of the exponential family `(ρ a, T a)`, then for `p > 0`, a level `x ≥ K` and
thresholds `β` at least `p log n + c_{p,K} + 2 x` at every round `n ≥ 1`, where
`c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))`, the GLRT with the generalized likelihood
ratio evidence and the thresholds `β` stops with an answer that is not correct for `μ` with
probability at most `(x / K) ^ K exp (K - x)`. -/
theorem measureReal_histOutputMeasure_glrt_expFamilyEvidence_le_of_mul_log_le [Nonempty α]
    (hp : 0 < p)
    (hβ : ∀ n : ℕ, n ≠ 0 → ∀ h, ENNReal.ofReal (p * log n + 2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) + 2 * x) ≤ β n h)
    (hstop : ∀ n, MeasurableSet
      {h | β n h < task.glr (expFamilyEvidence ρ T Finset.univ) n h (rec n h)})
    (hμM : μ ∈ task.M) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hc : MeasurableSet (task.correct μ)) (hx : Fintype.card α ≤ x) :
    (histOutputMeasure (task.glrt (expFamilyEvidence ρ T Finset.univ) alg β rec hrec hstop)
          (Environment.bandit (task.ν μ))).real
        {q | q.1 ∈ (task.glrt (expFamilyEvidence ρ T Finset.univ) alg β rec hrec hstop).stopSet ∧
          q.2 ∉ task.correct μ} ≤
      (x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x) := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (task.ν μ))
  have h_dev := measure_exists_lt_expFamilyEvidence_le_of_mul_log_le Finset.univ_nonempty hp
    (by simpa only [Finset.card_univ] using hβ) (fun a _ ↦ hμ a) (fun a _ ↦ hν a) hseq
    (x := x) (by rwa [Finset.card_univ])
  rw [Finset.card_univ] at h_dev
  refine (task.measureReal_histOutputMeasure_glrt_le (expFamilyEvidence ρ T Finset.univ) alg _ rec
    hrec hstop hseq hμM hc).trans ?_
  rw [measureReal_def]
  have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hx
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h_dev

/-- **The deviational thresholds of the GLRT for arms dominated by exponential families**
([GK16, Proposition 12], with a constant depending on `δ`), for every task and every sampling rule.
If the rewards of each arm `a` of an admissible model `μ` are dominated on `Set.univ`, in moment
generating function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for
`p > 0`, `δ ∈ (0, 1]` and `C ≥ δ exp (c_{p,K} + 2 x_δ)`, where
`c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))` and `x_δ = unionBoundLevel K δ`, the GLRT
with the generalized likelihood ratio evidence and the thresholds `log (C n ^ p / δ)` stops with an
answer that is not correct for `μ` with probability at most `δ`. [GK16] states it for `p > 1`,
with a constant independent of `δ`, which its proof does not give. -/
theorem measureReal_histOutputMeasure_glrt_expFamilyEvidence_log_mul_rpow_div_le [Nonempty α]
    {C : ℝ} (hp : 0 < p) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : δ * exp (2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) +
        2 * unionBoundLevel (Fintype.card α) δ) ≤ C)
    (hstop : ∀ n : ℕ, MeasurableSet {h | ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ)) <
      task.glr (expFamilyEvidence ρ T Finset.univ) n h (rec n h)})
    (hμM : μ ∈ task.M) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hc : MeasurableSet (task.correct μ)) :
    (histOutputMeasure (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
          (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop)
          (Environment.bandit (task.ν μ))).real
        {q | q.1 ∈ (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
          (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop).stopSet ∧
          q.2 ∉ task.correct μ} ≤ δ :=
  (measureReal_histOutputMeasure_glrt_expFamilyEvidence_le_of_mul_log_le rec hrec hp
    (fun _ hn _ ↦ ENNReal.ofReal_le_ofReal (mul_log_add_le_log_mul_rpow_div hδ hC hn)) hstop
    hμM hμ hν hc (card_le_unionBoundLevel hδ hδ1)).trans
    (div_pow_mul_exp_sub_unionBoundLevel_le hδ hδ1)

/-- **The GLRT with the deviational thresholds is `δ`-PAC** ([GK16, Proposition 12], with a
constant depending on `δ`), for every task and every sampling rule. If on every admissible model
`θ` the rewards of each arm `a` are dominated on `Set.univ`, in moment generating function, by the
member of mean `θ a` of the exponential family `(ρ a, T a)`, then for `p > 0`, `δ ∈ (0, 1]` and
`C ≥ δ exp (c_{p,K} + 2 x_δ)`, where `c_{p,K} = 2 K log (2 / (1 - exp (-(p log 2 / (2 K)))))` and
`x_δ = unionBoundLevel K δ`, the GLRT with the generalized likelihood ratio evidence and the
thresholds `log (C n ^ p / δ)` is `δ`-PAC on the task, provided it stops almost surely on every
admissible model. -/
theorem isDeltaPAC_glrt_expFamilyEvidence_log_mul_rpow_div [Nonempty α] {C : ℝ} (hp : 0 < p)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : δ * exp (2 * Fintype.card α *
      log (2 / (1 - exp (-(p * log 2 / (2 * Fintype.card α))))) +
        2 * unionBoundLevel (Fintype.card α) δ) ≤ C)
    (hstop : ∀ n : ℕ, MeasurableSet {h | ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ)) <
      task.glr (expFamilyEvidence ρ T Finset.univ) n h (rec n h)})
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
      (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop)
      (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.glrt (expFamilyEvidence ρ T Finset.univ) alg
      (fun n _ ↦ ENNReal.ofReal (log (C * (n : ℝ) ^ p / δ))) rec hrec hstop) δ :=
  isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le hc (fun θ hθ ↦
    measureReal_histOutputMeasure_glrt_expFamilyEvidence_log_mul_rpow_div_le rec hrec hp hδ hδ1 hC
      hstop hθ (hμ θ hθ) (hν θ hθ) (hc θ hθ)) h_stops

end IdentTask

end Deviational

/-! ### Pairwise GLRT for best arm and top-`m` identification -/

section Pairwise

open Finset

variable {Θ : Type*} {ν : Θ → Kernel α ℝ} [∀ θ, IsMarkovKernel (ν θ)] {mean : Θ → α → ℝ}

/-- **Deviation of the evidence of pairs of arms**, along a run of any sampling rule. If the
rewards of each arm `a` of the bandit `ν₀` are dominated on `Set.univ`, in moment generating
function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for a finite set
`Q` of pairs of distinct arms and a level `x ≥ 2`, the probability that for some pair `(a, b) ∈ Q`
the evidence of the arms `a, b` against `μ` exceeds the threshold `2 log (2 n (n + 1)) + x` at
some round `n` is at most `#Q (x / 2) ^ 2 exp (2 - x)`. -/
theorem measure_exists_mem_exists_unionBoundThreshold_lt_expFamilyEvidence_le [Countable α]
    {ν₀ : Kernel α ℝ} [IsMarkovKernel ν₀] (Q : Finset (α × α)) (hQ : ∀ p ∈ Q, p.1 ≠ p.2)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (ν₀ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit ν₀) P) (hx : 2 ≤ x) :
    P {ω | ∃ p ∈ Q, ∃ n, unionBoundThreshold 2 x n <
        expFamilyEvidence ρ T {p.1, p.2} n (history O A R n ω) μ} ≤
      #Q * ENNReal.ofReal ((x / 2) ^ 2 * exp (2 - x)) := by
  refine (measure_mono (t := ⋃ p ∈ Q, {ω | ∃ n, unionBoundThreshold 2 x n <
      expFamilyEvidence ρ T {p.1, p.2} n (history O A R n ω) μ})
    fun ω hω ↦ by obtain ⟨p, hp, hω⟩ := hω; exact Set.mem_biUnion hp hω).trans
    ((measure_biUnion_finset_le Q _).trans ?_)
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp ↦ ?_
  have hcard : #{p.1, p.2} = 2 := card_pair (hQ p hp)
  have h := measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le {p.1, p.2}
    (fun a _ ↦ hμ a) (fun a _ ↦ hν a) hseq (x := x) (by rw [hcard]; exact_mod_cast hx)
  rwa [hcard, Nat.cast_ofNat] at h

/-- **Deviation of the evidence of pairs of arms**, in real measure: the probability that for some
pair `(a, b) ∈ Q` of distinct arms the evidence of the arms `a, b` against `μ` exceeds the threshold
`2 log (2 n (n + 1)) + x` at some round `n` is at most `#Q (x / 2) ^ 2 exp (2 - x)`. -/
theorem measureReal_exists_mem_exists_unionBoundThreshold_lt_expFamilyEvidence_le [Countable α]
    {ν₀ : Kernel α ℝ} [IsMarkovKernel ν₀] (Q : Finset (α × α)) (hQ : ∀ p ∈ Q, p.1 ≠ p.2)
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (ν₀ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit ν₀) P) (hx : 2 ≤ x) :
    P.real {ω | ∃ p ∈ Q, ∃ n, unionBoundThreshold 2 x n <
        expFamilyEvidence ρ T {p.1, p.2} n (history O A R n ω) μ} ≤
      #Q * ((x / 2) ^ 2 * exp (2 - x)) := by
  have hx0 : 0 ≤ x := zero_le_two.trans hx
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity)
    ((measure_exists_mem_exists_unionBoundThreshold_lt_expFamilyEvidence_le Q hQ hμ hν hseq
      hx).trans_eq ?_)
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

variable [Fintype α]

/-- **Error probability of the pairwise GLRT for best arm identification**
[GK16, Proposition 12], for every sampling rule. The alternatives to the arm `i` are covered by the
half-spaces `{θ' | mean θ' i ≤ mean θ' b}`, `b ≠ i`; on the piece of `b`, the statistic is the
evidence of the arms `i, b` and the threshold is `2 log (2 n (n + 1)) + x`. Let `a` be a best arm
of the model `θ`, and let the rewards of each arm `b` of `θ` be dominated on `Set.univ`, in moment
generating function, by the member of mean `mean θ b` of the exponential family `(ρ b, T b)`.
Then for a level `x ≥ 2`, the GLRT with these pieces stops with an arm that is not a best arm of
`θ` with probability at most `(K - 1) (x / 2) ^ 2 exp (2 - x)`, where `K` is the number of arms:
only the `K - 1` pairs of the best arm with another arm matter. -/
theorem measureReal_histOutputMeasure_coverGlrt_baiTask_le
    (rec : (n : ℕ) → Hist Unit α ℝ n → α) (hrec : ∀ n, Measurable (rec n))
    (hstop : ∀ n, MeasurableSet {h | ∀ b : {b // b ≠ rec n h}, unionBoundThreshold 2 x n <
      ⨅ θ' ∈ {θ' | mean θ' (rec n h) ≤ mean θ' b}, expFamilyEvidence ρ T {rec n h, b.1} n h
        (mean θ')})
    {θ : Θ} {a : α} (ha : a ∈ (baiTask ν mean).correct θ)
    (hμ : ∀ b, mean θ b ∈ (ρ b).expFamilyMeans (T b))
    (hν : ∀ b, MGFDominatedOn id (ν θ b) (T b)
      ((ρ b).expFamily (T b) ((ρ b).natParam (T b) (mean θ b))) Set.univ) (hx : 2 ≤ x) :
    (histOutputMeasure (coverGlrt alg (fun i (b : {b // b ≠ i}) ↦ {θ' | mean θ' i ≤ mean θ' b})
        (fun i b n h θ' ↦ expFamilyEvidence ρ T {i, b.1} n h (mean θ'))
        (fun _ _ n _ ↦ unionBoundThreshold 2 x n) rec hrec hstop)
        (Environment.bandit (ν θ))).real
      {p | p.1 ∈ (coverGlrt alg (fun i (b : {b // b ≠ i}) ↦ {θ' | mean θ' i ≤ mean θ' b})
        (fun i b n h θ' ↦ expFamilyEvidence ρ T {i, b.1} n h (mean θ'))
        (fun _ _ n _ ↦ unionBoundThreshold 2 x n) rec hrec hstop).stopSet ∧
        p.2 ∉ (baiTask ν mean).correct θ} ≤
      (Fintype.card α - 1 : ℕ) * ((x / 2) ^ 2 * exp (2 - x)) := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (ν θ))
  have ha' : ∀ b ≠ a, mean θ b < mean θ a := by simpa using ha
  refine (measureReal_histOutputMeasure_coverGlrt_le alg _ _ _ rec hrec hstop hseq θ
    (Set.toFinite _).measurableSet).trans ((measureReal_mono fun ω hω ↦ ?sub).trans
    ((measureReal_exists_mem_exists_unionBoundThreshold_lt_expFamilyEvidence_le
      ((univ.erase a) ×ˢ {a}) (fun p hp ↦ ?hQ) hμ hν hseq hx).trans_eq ?card))
  -- a wrong recommendation `b` is not `a`, and the piece of the pair `b, a` contains `θ`
  case sub =>
    obtain ⟨n, hn, hdev⟩ := hω
    set b := rec n (history IT.obs IT.action IT.feedback n ω)
    have hb : b ≠ a := fun h ↦ hn (h ▸ ha)
    exact ⟨(b, a), by simp [hb], n, hdev ⟨a, hb.symm⟩ (ha' _ hb).le⟩
  case hQ =>
    simp only [mem_product, mem_erase, mem_singleton] at hp
    exact hp.2 ▸ hp.1.1
  case card =>
    rw [card_product, card_erase_of_mem (mem_univ a), card_singleton, mul_one, card_univ]

/-- **The pairwise GLRT for best arm identification is `δ`-PAC** [GK16, Proposition 12], for every
sampling rule. Let every bandit of a set `S` of models have a best arm, and let the rewards of each
of its arms `b` be dominated on `Set.univ`, in moment generating function, by the member of mean
`mean θ b` of the exponential family `(ρ b, T b)`. For `δ ∈ (0, 1]`, the GLRT whose pieces for the
arm `i` are the half-spaces `{θ' | mean θ' i ≤ mean θ' b}`, `b ≠ i`, with the evidence of the arms
`i, b` and the thresholds `2 log (2 n (n + 1)) + x_{δ / (K - 1)}`, is `δ`-PAC for best arm
identification on `S`, provided it stops almost surely on every model of `S` with a best arm. The
thresholds grow as `4 log n + log (K / δ)`, against `2 K log n + log (1 / δ)` for the evidence of
all the arms. -/
theorem isDeltaPAC_coverGlrt_baiTask {S : Set Θ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (rec : (n : ℕ) → Hist Unit α ℝ n → α) (hrec : ∀ n, Measurable (rec n))
    (hstop : ∀ n, MeasurableSet {h | ∀ b : {b // b ≠ rec n h},
      unionBoundThreshold 2 (unionBoundLevel 2 (δ / (Fintype.card α - 1 : ℕ))) n <
        ⨅ θ' ∈ {θ' | mean θ' (rec n h) ≤ mean θ' b}, expFamilyEvidence ρ T {rec n h, b.1} n h
          (mean θ')})
    (hμ : ∀ θ ∈ ((baiTask ν mean).restrict S).M, ∀ b, mean θ b ∈ (ρ b).expFamilyMeans (T b))
    (hν : ∀ θ ∈ ((baiTask ν mean).restrict S).M, ∀ b, MGFDominatedOn id (ν θ b) (T b)
      ((ρ b).expFamily (T b) ((ρ b).natParam (T b) (mean θ b))) Set.univ)
    (h_stops : ∀ θ ∈ ((baiTask ν mean).restrict S).M, StopsAS
      (coverGlrt alg (fun i (b : {b // b ≠ i}) ↦ {θ' | mean θ' i ≤ mean θ' b})
        (fun i b n h θ' ↦ expFamilyEvidence ρ T {i, b.1} n h (mean θ'))
        (fun _ _ n _ ↦ unionBoundThreshold 2 (unionBoundLevel 2 (δ / (Fintype.card α - 1 : ℕ))) n)
        rec hrec hstop) (Environment.bandit (ν θ))) :
    ((baiTask ν mean).restrict S).IsDeltaPAC
      (coverGlrt alg (fun i (b : {b // b ≠ i}) ↦ {θ' | mean θ' i ≤ mean θ' b})
        (fun i b n h θ' ↦ expFamilyEvidence ρ T {i, b.1} n h (mean θ'))
        (fun _ _ n _ ↦ unionBoundThreshold 2 (unionBoundLevel 2 (δ / (Fintype.card α - 1 : ℕ))) n)
        rec hrec hstop) δ := by
  refine IdentTask.isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le
    (fun θ _ ↦ (Set.toFinite _).measurableSet) (fun θ hθ ↦ ?_)
    fun θ hθ ↦ by simpa only [IdentTask.ν_restrict, ν_baiTask] using h_stops θ hθ
  have hθM : θ ∈ (baiTask ν mean).M := by
    rw [IdentTask.M_restrict] at hθ
    exact hθ.1
  rw [M_baiTask, Set.mem_ofPred_eq] at hθM
  obtain ⟨a, ha⟩ := hθM
  have h := measureReal_histOutputMeasure_coverGlrt_baiTask_le (alg := alg) (ν := ν) rec hrec
    hstop (a := a) (by rwa [correct_baiTask, Set.mem_ofPred_eq]) (hμ θ hθ)
    (hν θ hθ) (card_le_unionBoundLevel_div _ hδ hδ1)
  simp only [IdentTask.ν_restrict, ν_baiTask, IdentTask.correct_restrict]
  exact h.trans (natCast_mul_div_pow_mul_exp_sub_unionBoundLevel_div_le _ hδ hδ1)

/-- **Error probability of the pairwise GLRT for top-`m` identification**, for every sampling
rule. The alternatives to a set `s` of `m` arms are covered by the half-spaces
`{θ' | mean θ' b ≤ mean θ' c}`, `b ∈ s`, `c ∉ s`; on the piece of `(b, c)`, the statistic is the
evidence of the arms `b, c` and the threshold is `2 log (2 n (n + 1)) + x`. Let the recommendation
rule return sets of `m` arms, let `t` be the set of the `m` arms with the largest means of the model
`θ`, and let the rewards of each arm `b` of `θ` be dominated on `Set.univ`, in moment generating
function, by the member of mean `mean θ b` of the exponential family `(ρ b, T b)`. Then for a level
`x ≥ 2`, the GLRT with these pieces stops with a set that is not `t` with probability at most
`(K - m) m (x / 2) ^ 2 exp (2 - x)`, where `K` is the number of arms: only the pairs of an arm
outside `t` with an arm of `t` matter. -/
theorem measureReal_histOutputMeasure_coverGlrt_topMTask_le {m : ℕ}
    (rec : (n : ℕ) → Hist Unit α ℝ n → Finset α) (hrec : ∀ n, Measurable (rec n))
    (hrec_card : ∀ n h, #(rec n h) = m)
    (hstop : ∀ n, MeasurableSet {h | ∀ p : {p : α × α // p.1 ∈ rec n h ∧ p.2 ∉ rec n h},
      unionBoundThreshold 2 x n < ⨅ θ' ∈ {θ' | mean θ' p.1.1 ≤ mean θ' p.1.2},
        expFamilyEvidence ρ T {p.1.1, p.1.2} n h (mean θ')})
    {θ : Θ} {t : Finset α} (ht : t ∈ (topMTask ν mean m).correct θ)
    (hμ : ∀ b, mean θ b ∈ (ρ b).expFamilyMeans (T b))
    (hν : ∀ b, MGFDominatedOn id (ν θ b) (T b)
      ((ρ b).expFamily (T b) ((ρ b).natParam (T b) (mean θ b))) Set.univ) (hx : 2 ≤ x) :
    (histOutputMeasure (coverGlrt alg
        (fun s (p : {p : α × α // p.1 ∈ s ∧ p.2 ∉ s}) ↦ {θ' | mean θ' p.1.1 ≤ mean θ' p.1.2})
        (fun _ p n h θ' ↦ expFamilyEvidence ρ T {p.1.1, p.1.2} n h (mean θ'))
        (fun _ _ n _ ↦ unionBoundThreshold 2 x n) rec hrec hstop)
        (Environment.bandit (ν θ))).real
      {p | p.1 ∈ (coverGlrt alg
        (fun s (p : {p : α × α // p.1 ∈ s ∧ p.2 ∉ s}) ↦ {θ' | mean θ' p.1.1 ≤ mean θ' p.1.2})
        (fun _ p n h θ' ↦ expFamilyEvidence ρ T {p.1.1, p.1.2} n h (mean θ'))
        (fun _ _ n _ ↦ unionBoundThreshold 2 x n) rec hrec hstop).stopSet ∧
        p.2 ∉ (topMTask ν mean m).correct θ} ≤
      ((Fintype.card α - m) * m : ℕ) * ((x / 2) ^ 2 * exp (2 - x)) := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (ν θ))
  have ht' : #t = m ∧ ∀ a ∈ t, ∀ b ∉ t, mean θ b < mean θ a := by simpa using ht
  refine (measureReal_histOutputMeasure_coverGlrt_le alg _ _ _ rec hrec hstop hseq θ
    (Set.to_countable _).measurableSet).trans ((measureReal_mono fun ω hω ↦ ?sub).trans
    ((measureReal_exists_mem_exists_unionBoundThreshold_lt_expFamilyEvidence_le
      (tᶜ ×ˢ t) (fun p hp ↦ ?hQ) hμ hν hseq hx).trans_eq ?card))
  -- a wrong recommendation `s` of `m` arms has an arm `b ∉ t` and misses an arm `c ∈ t`, and the
  -- piece of the pair `(b, c)` contains `θ`
  case sub =>
    obtain ⟨n, hn, hdev⟩ := hω
    set s := rec n (history IT.obs IT.action IT.feedback n ω)
    have hst : s ≠ t := fun h ↦ hn (h ▸ ht)
    have hcard : #s = #t := (hrec_card _ _).trans ht'.1.symm
    obtain ⟨b, hbs, hbt⟩ := not_subset.1 fun h ↦ hst (eq_of_subset_of_card_le h hcard.ge)
    obtain ⟨c, hct, hcs⟩ := not_subset.1 fun h ↦ hst (eq_of_subset_of_card_le h hcard.le).symm
    exact ⟨(b, c), by simp [hbt, hct], n, hdev ⟨(b, c), hbs, hcs⟩ (ht'.2 c hct b hbt).le⟩
  case hQ =>
    simp only [mem_product, mem_compl] at hp
    exact fun h ↦ hp.1 (h ▸ hp.2)
  case card => rw [card_product, card_compl, ht'.1]

/-- **The pairwise GLRT for top-`m` identification is `δ`-PAC**, for every sampling rule. Let every
bandit of a set `S` of models have a set of `m` arms with the largest means, and let the rewards of
each of its arms `b` be dominated on `Set.univ`, in moment generating function, by the member of
mean `mean θ b` of the exponential family `(ρ b, T b)`. For `δ ∈ (0, 1]` and a recommendation rule
returning sets of `m` arms, the GLRT whose pieces for the set `s` are the half-spaces
`{θ' | mean θ' b ≤ mean θ' c}`, `b ∈ s`, `c ∉ s`, with the evidence of the arms `b, c` and the
thresholds `2 log (2 n (n + 1)) + x_{δ / ((K - m) m)}`, is `δ`-PAC for top-`m` identification on
`S`, provided it stops almost surely on every model of `S` with such a set of arms. -/
theorem isDeltaPAC_coverGlrt_topMTask {m : ℕ} {S : Set Θ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (rec : (n : ℕ) → Hist Unit α ℝ n → Finset α) (hrec : ∀ n, Measurable (rec n))
    (hrec_card : ∀ n h, #(rec n h) = m)
    (hstop : ∀ n, MeasurableSet {h | ∀ p : {p : α × α // p.1 ∈ rec n h ∧ p.2 ∉ rec n h},
      unionBoundThreshold 2 (unionBoundLevel 2 (δ / ((Fintype.card α - m) * m : ℕ))) n <
        ⨅ θ' ∈ {θ' | mean θ' p.1.1 ≤ mean θ' p.1.2},
          expFamilyEvidence ρ T {p.1.1, p.1.2} n h (mean θ')})
    (hμ : ∀ θ ∈ ((topMTask ν mean m).restrict S).M, ∀ b,
      mean θ b ∈ (ρ b).expFamilyMeans (T b))
    (hν : ∀ θ ∈ ((topMTask ν mean m).restrict S).M, ∀ b, MGFDominatedOn id (ν θ b) (T b)
      ((ρ b).expFamily (T b) ((ρ b).natParam (T b) (mean θ b))) Set.univ)
    (h_stops : ∀ θ ∈ ((topMTask ν mean m).restrict S).M, StopsAS (coverGlrt alg
      (fun s (p : {p : α × α // p.1 ∈ s ∧ p.2 ∉ s}) ↦ {θ' | mean θ' p.1.1 ≤ mean θ' p.1.2})
      (fun _ p n h θ' ↦ expFamilyEvidence ρ T {p.1.1, p.1.2} n h (mean θ'))
      (fun _ _ n _ ↦
        unionBoundThreshold 2 (unionBoundLevel 2 (δ / ((Fintype.card α - m) * m : ℕ))) n)
      rec hrec hstop) (Environment.bandit (ν θ))) :
    ((topMTask ν mean m).restrict S).IsDeltaPAC (coverGlrt alg
      (fun s (p : {p : α × α // p.1 ∈ s ∧ p.2 ∉ s}) ↦ {θ' | mean θ' p.1.1 ≤ mean θ' p.1.2})
      (fun _ p n h θ' ↦ expFamilyEvidence ρ T {p.1.1, p.1.2} n h (mean θ'))
      (fun _ _ n _ ↦
        unionBoundThreshold 2 (unionBoundLevel 2 (δ / ((Fintype.card α - m) * m : ℕ))) n)
      rec hrec hstop) δ := by
  refine IdentTask.isDeltaPAC_of_measureReal_mem_stopSet_and_notMem_le
    (fun θ _ ↦ (Set.to_countable _).measurableSet) (fun θ hθ ↦ ?_)
    fun θ hθ ↦ by simpa only [IdentTask.ν_restrict, ν_topMTask] using h_stops θ hθ
  have hθM : θ ∈ (topMTask ν mean m).M := by
    rw [IdentTask.M_restrict] at hθ
    exact hθ.1
  rw [M_topMTask, Set.mem_ofPred_eq] at hθM
  obtain ⟨t, ht⟩ := hθM
  have h := measureReal_histOutputMeasure_coverGlrt_topMTask_le (alg := alg) (ν := ν) rec hrec
    hrec_card hstop (t := t) (by rwa [correct_topMTask, Set.mem_ofPred_eq]) (hμ θ hθ)
    (hν θ hθ) (card_le_unionBoundLevel_div _ hδ hδ1)
  simp only [IdentTask.ν_restrict, ν_topMTask, IdentTask.correct_restrict]
  exact h.trans (natCast_mul_div_pow_mul_exp_sub_unionBoundLevel_div_le _ hδ hδ1)

end Pairwise

end LMLExplore.Identification
