/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Identification.TrackAndStop
public import LMLExplore.SequentialLearning.RateFunctionDeviation

/-!
# `δ`-correct GLR thresholds for arms dominated by exponential families

Let the models of an identification task be vectors of means `μ : α → ℝ` of arms with real
observations, and let the arm `a` be described by the exponential family `(ρ a, T a)` on a
measurable space `𝓧`, with extended divergence `dbar_a(x, μ_a)`
(`MeasureTheory.Measure.expFamilyRate`): the Cramér rate function at `x` of the statistic `T a`
under the member of mean `μ_a`. After `n` rounds with history `h`, pull counts `N_a` and empirical
means `μ̂_a`, the *generalized likelihood ratio evidence* against a vector of means `λ` is
`Z_n(h, λ) = ∑ a, N_a dbar_a(μ̂_a, λ_a)` (`LMLExplore.Identification.expFamilyEvidence`). When the
divergences between the arm laws are those of the families, its value at a vector of means of the
families is the plug-in statistic of the empirical means (`IdentTask.plugInCost`) as long as the
empirical means are means of the families, and it extends that statistic to empirical means on
the boundary of the means, such as the empirical means `0` and `1` of Bernoulli arms, where the
plug-in statistic of the empirical means is not meaningful.

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

## Main definitions

* `LMLExplore.Identification.expFamilyEvidence ρ T n h λ`: the generalized likelihood ratio
  evidence `∑ a, N_a dbar_a(μ̂_a, λ_a)` against the vector of means `λ`.

## Main statements

* `LMLExplore.Identification.IdentTask.plugInCost_empMean'_eq_expFamilyEvidence`: when the
  divergences between the arm laws are those of the families and the empirical means are means of
  the families, the evidence is the plug-in statistic of the empirical means.
* `LMLExplore.Identification.IdentTask.measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le`:
  along a run of any sampling rule on the model `μ`, the evidence against `μ` exceeds the threshold
  `K log (2 n (n + 1)) + x` at some round with probability at most `f(x)`.
* `LMLExplore.Identification.IdentTask.measureReal_histOutputMeasure_glrt_expFamilyEvidence_le`:
  for every task and every sampling rule, the GLRT with the evidence and these thresholds stops with
  an answer that is not correct for `μ` with probability at most `f(x)`.
* `LMLExplore.Identification.IdentTask.isDeltaPAC_glrt_expFamilyEvidence`: with the level `x_δ`,
  the GLRT is `δ`-PAC on the task as soon as it stops almost surely on every admissible model.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Proposition 12.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press (2020),
  Lemma 33.7.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Learning Real

open scoped ENNReal

namespace LMLExplore.Identification

variable {α 𝓧 : Type*} [Fintype α] [DecidableEq α] {m𝓧 : MeasurableSpace 𝓧}
  {ρ : α → Measure 𝓧} {T : α → 𝓧 → ℝ}

/-- The *generalized likelihood ratio evidence* against the vector of means `λ` after `n` rounds
with history `h`, for arms described by the exponential families `(ρ a, T a)`:
`∑ a, N_a dbar_a(μ̂_a, λ_a)`, with the pull counts `N_a` and the empirical means `μ̂_a` of `h` and
the extended divergence `dbar_a` of the family of `a` (`MeasureTheory.Measure.expFamilyRate`). -/
noncomputable def expFamilyEvidence (ρ : α → Measure 𝓧) (T : α → 𝓧 → ℝ) (n : ℕ)
    (h : Hist Unit α ℝ n) (l : α → ℝ) : ℝ≥0∞ :=
  ∑ a, pullCount' n h a * (ρ a).expFamilyRate (T a) (empMean' n h a) (l a)

lemma expFamilyEvidence_def (ρ : α → Measure 𝓧) (T : α → 𝓧 → ℝ) (n : ℕ) (h : Hist Unit α ℝ n)
    (l : α → ℝ) :
    expFamilyEvidence ρ T n h l =
      ∑ a, pullCount' n h a * (ρ a).expFamilyRate (T a) (empMean' n h a) (l a) :=
  (rfl)

/-- The evidence against a vector of means is a measurable function of the history. -/
lemma measurable_expFamilyEvidence {mα : MeasurableSpace α} [MeasurableSingletonClass α] (n : ℕ)
    (l : α → ℝ) : Measurable fun h : Hist Unit α ℝ n ↦ expFamilyEvidence ρ T n h l := by
  simp_rw [expFamilyEvidence_def, Measure.expFamilyRate_def]
  refine Finset.measurable_sum _ fun a _ ↦ Measurable.mul ?_ ?_
  · exact measurable_from_nat.comp (measurable_pullCount' n a)
  · exact (lowerSemicontinuous_rateFunction _ _).measurable.comp (measurable_empMean' n a)

namespace IdentTask

variable {ℐ : Type*} {mα : MeasurableSpace α} {task : IdentTask α (α → ℝ) ℐ ℝ}

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
    task.plugInCost empMean' n h l = expFamilyEvidence ρ T n h l := by
  rw [plugInCost_def, cost_def, expFamilyEvidence_def]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hν _ _ hemp hl a, ENNReal.ofReal_natCast,
    Measure.expFamilyRate_eq_ofReal_expFamilyDiv (hemp a) (hl a)]

variable [MeasurableSingletonClass α] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P] {alg : Algorithm Unit α ℝ} {O : ℕ → Ω → Unit} {A : ℕ → Ω → α}
  {R : ℕ → Ω → ℝ} {μ : α → ℝ} {x δ : ℝ}

/-- **Deviation of the generalized likelihood ratio evidence for arms dominated by exponential
families**, along a run of any sampling rule. If the rewards of each arm `a` of the model `μ` are
dominated on `Set.univ`, in moment generating function, by the member of mean `μ a` of the
exponential family `(ρ a, T a)`, then for a level `x ≥ K`, the probability that at some round `n`
the evidence against the true model `μ` exceeds the threshold `K log (2 n (n + 1)) + x` is at most
`(x / K) ^ K exp (K - x)`. -/
theorem measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le
    (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hseq : IsAlgEnvSeq O A R alg (Environment.bandit (task.ν μ)) P)
    (hx : Fintype.card α ≤ x) :
    P {ω | ∃ n, unionBoundThreshold (Fintype.card α) x n <
        expFamilyEvidence ρ T n (history O A R n ω) μ} ≤
      ENNReal.ofReal ((x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x)) := by
  refine le_trans (measure_mono fun ω hω ↦ ?_)
    (measure_exists_card_mul_log_add_le_sum_pullCount_mul_expFamilyRate_le hseq hμ hν hx)
  obtain ⟨n, hn⟩ := hω
  rw [unionBoundThreshold_def] at hn
  refine ⟨n, hn.le.trans_eq ?_⟩
  simp only [expFamilyEvidence_def, pullCount_eq_pullCount' (O := O) (R' := R),
    empMean_eq_empMean' (O := O)]

variable {mℐ : MeasurableSpace ℐ} (rec : (n : ℕ) → Hist Unit α ℝ n → ℐ)
  (hrec : ∀ n, Measurable (rec n))

/-- **Error probability of the GLRT for arms dominated by exponential families**
([GK16, Proposition 12], [LS, Lemma 33.7]), for every task and every sampling rule. If the rewards
of each arm `a` of an admissible model `μ` are dominated on `Set.univ`, in moment generating
function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for a level
`x ≥ K`, the GLRT with the generalized likelihood ratio evidence and the thresholds
`K log (2 n (n + 1)) + x` stops with an answer that is not correct for `μ` with probability at most
`(x / K) ^ K exp (K - x)`. -/
theorem measureReal_histOutputMeasure_glrt_expFamilyEvidence_le
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α) x n <
      task.glr (expFamilyEvidence ρ T) n h (rec n h)})
    (hμM : μ ∈ task.M) (hμ : ∀ a, μ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ a, MGFDominatedOn id (task.ν μ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (μ a))) Set.univ)
    (hc : MeasurableSet (task.correct μ)) (hx : Fintype.card α ≤ x) :
    (histOutputMeasure
        (task.glrt (expFamilyEvidence ρ T) alg
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n) rec hrec hstop)
          (Environment.bandit (task.ν μ))).real
        {p | p.1 ∈ (task.glrt (expFamilyEvidence ρ T) alg
          (fun n _ ↦ unionBoundThreshold (Fintype.card α) x n) rec hrec hstop).stopSet ∧
          p.2 ∉ task.correct μ} ≤
      (x / Fintype.card α) ^ Fintype.card α * exp (Fintype.card α - x) := by
  have hseq := IT.isAlgEnvSeq_trajMeasure alg (Environment.bandit (task.ν μ))
  refine (task.measureReal_histOutputMeasure_glrt_le (expFamilyEvidence ρ T) alg _ rec hrec hstop
    hseq hμM hc).trans ?_
  rw [measureReal_def]
  have hx0 : 0 ≤ x := (Nat.cast_nonneg _).trans hx
  exact ENNReal.toReal_le_of_le_ofReal (by positivity)
    (measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le hμ hν hseq hx)

/-- **The GLRT for arms dominated by exponential families is `δ`-PAC**
([GK16, Proposition 12], [LS, Lemma 33.7]), for every task and every sampling rule. If on every
admissible model `μ` the rewards of each arm `a` are dominated on `Set.univ`, in moment generating
function, by the member of mean `μ a` of the exponential family `(ρ a, T a)`, then for
`δ ∈ (0, 1]`, the GLRT with the generalized likelihood ratio evidence and the thresholds
`K log (2 n (n + 1)) + x_δ` is `δ`-PAC on the task, provided it stops almost surely on every
admissible model. -/
theorem isDeltaPAC_glrt_expFamilyEvidence (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstop : ∀ n, MeasurableSet {h | unionBoundThreshold (Fintype.card α)
      (unionBoundLevel (Fintype.card α) δ) n < task.glr (expFamilyEvidence ρ T) n h (rec n h)})
    (hμ : ∀ θ ∈ task.M, ∀ a, θ a ∈ (ρ a).expFamilyMeans (T a))
    (hν : ∀ θ ∈ task.M, ∀ a, MGFDominatedOn id (task.ν θ a) (T a)
      ((ρ a).expFamily (T a) ((ρ a).natParam (T a) (θ a))) Set.univ)
    (hc : ∀ θ ∈ task.M, MeasurableSet (task.correct θ))
    (h_stops : ∀ θ ∈ task.M, StopsAS (task.glrt (expFamilyEvidence ρ T) alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) (Environment.bandit (task.ν θ))) :
    task.IsDeltaPAC (task.glrt (expFamilyEvidence ρ T) alg
      (fun n _ ↦ unionBoundThreshold (Fintype.card α) (unionBoundLevel (Fintype.card α) δ) n) rec
      hrec hstop) δ := by
  refine task.isDeltaPAC_glrt (expFamilyEvidence ρ T) alg _ rec hrec hstop hc (fun θ hθ ↦ ?_)
    h_stops
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal hδ.le
    ((measure_exists_unionBoundThreshold_lt_expFamilyEvidence_le (hμ θ hθ) (hν θ hθ)
      (IT.isAlgEnvSeq_trajMeasure alg _) (card_le_unionBoundLevel hδ hδ1)).trans ?_)
  exact ENNReal.ofReal_le_ofReal (div_pow_mul_exp_sub_unionBoundLevel_le hδ hδ1)

end IdentTask

end LMLExplore.Identification
