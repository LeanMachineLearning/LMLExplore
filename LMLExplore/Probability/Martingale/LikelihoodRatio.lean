/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.TestSupermartingale.Predictor
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Martingale.Basic
import LMLExplore.MeasureTheory.Measure.Singletons

/-!
# Likelihood ratios of sequential predictors

Let `ξ 0, ξ 1, …` be random variables on a finite type `α`, each independent of the past and with
law `ν`. A *sequential predictor* assigns to every time `t` a vector `q t ω : α → ℝ` that depends
only on the past, here: `ω ↦ q t ω a` is measurable for the σ-algebra `ℱ t` of a filtration with
respect to which `ξ t` is `ℱ (t + 1)`-measurable and independent of `ℱ t`. Its *likelihood ratio*
against `ν` after `n` observations is
`L_n = ∏_{t < n} q t (ξ t) / ν{ξ t}` (`LMLExplore.predictorLikelihoodRatio`).

If every `q t ω` is a sub-probability vector, `L` is a nonnegative supermartingale with `L_0 = 1`,
and if moreover every `q t ω` is a probability vector and `ν` charges every point, `L` is a
martingale, with mean `1`. Ville's inequality then bounds the probability that `L` ever reaches
`1 / δ` by `δ`. Choosing a universal predictor, whose likelihood is close to the maximum likelihood
of the observations, turns this into time-uniform concentration of the empirical distribution of
the `ξ t`, as for Laplace's rule of succession in `InformationTheory/LaplaceMixture.lean`.

A mixture of fixed alternatives over a prior is the predictor of its posterior predictive laws;
`SequentialLearning/LikelihoodRatio.lean` treats such mixtures, along a bandit run, through the
exponentials of sums of log-likelihood ratios instead. A predictor needs no prior, and no integral
over the alternatives.

## Main statements

* `LMLExplore.supermartingale_predictorLikelihoodRatio`: the likelihood ratio of a
  sub-probability predictor is a supermartingale.
* `LMLExplore.martingale_predictorLikelihoodRatio`: the likelihood ratio of a probability
  predictor against a law that charges every point is a martingale.
* `LMLExplore.integral_predictorLikelihoodRatio`: it has mean `1`.

## Implementation notes

The (super)martingale property is the case of a finite alphabet and of the constant conditional
laws `ν` of the general statement for sequential predictors on any observation space against any
conditional law of the observations,
`ProbabilityTheory.isTestSupermartingale_prod_of_hasCondLaw` and
`ProbabilityTheory.isTestMartingale_prod_of_hasCondLaw` in
`EValues/TestSupermartingale/Predictor.lean`: the density of the prediction `q t ω` with
respect to `ν` is `a ↦ q t ω a / ν{a}`, and an observation independent of the past with law `ν`
has the conditional law `ν` given the past (`ProbabilityTheory.hasCondLaw_of_indep`). The
statements are adapted from `InformationTheory/KLTimeUniform.lean` of the formalization
RemyDegenne/Essakine2026Tight (commit 38bbd16f, directory `ForLMLExplore/`).

## References

* [JKMDLV20] A. Jonsson, E. Kaufmann, P. Ménard, O. D. Domingues, E. Leurent and M. Valko,
  *Planning in Markov decision processes with gap-dependent sample complexity*, NeurIPS 2020,
  Proposition 1 and its proof.
-/

public section

open MeasureTheory ProbabilityTheory Finset

namespace LMLExplore

variable {α Ω : Type*} [MeasurableSpace α] {mΩ : MeasurableSpace Ω}

/-- The **likelihood ratio of a sequential predictor** `q` against a measure `ν`, along the
observations `ξ 0, ξ 1, …`: after `n` observations, `∏_{t < n} q t (ξ t) / ν{ξ t}`. -/
noncomputable def predictorLikelihoodRatio (ν : Measure α) (q : ℕ → Ω → α → ℝ)
    (ξ : ℕ → Ω → α) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ t ∈ range n, q t ω (ξ t ω) / ν.real {ξ t ω}

variable {ν : Measure α} {q : ℕ → Ω → α → ℝ} {ξ : ℕ → Ω → α}

lemma predictorLikelihoodRatio_def (n : ℕ) (ω : Ω) :
    predictorLikelihoodRatio ν q ξ n ω = ∏ t ∈ range n, q t ω (ξ t ω) / ν.real {ξ t ω} :=
  (rfl)

@[simp]
lemma predictorLikelihoodRatio_zero (ω : Ω) : predictorLikelihoodRatio ν q ξ 0 ω = 1 := by
  simp [predictorLikelihoodRatio_def]

lemma predictorLikelihoodRatio_succ (n : ℕ) (ω : Ω) :
    predictorLikelihoodRatio ν q ξ (n + 1) ω =
      predictorLikelihoodRatio ν q ξ n ω * (q n ω (ξ n ω) / ν.real {ξ n ω}) := by
  simp_rw [predictorLikelihoodRatio_def, prod_range_succ]

lemma predictorLikelihoodRatio_nonneg (hq0 : ∀ t ω a, 0 ≤ q t ω a) (n : ℕ) (ω : Ω) :
    0 ≤ predictorLikelihoodRatio ν q ξ n ω :=
  prod_nonneg fun _ _ ↦ div_nonneg (hq0 _ _ _) measureReal_nonneg

section Filtration

variable [Fintype α] [MeasurableSingletonClass α] {ℱ : Filtration ℕ mΩ}

omit [Fintype α] in
/-- The likelihood ratio after `n` observations is `ℱ n`-measurable. -/
lemma measurable_predictorLikelihoodRatio [Finite α] (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a)) (n : ℕ) :
    Measurable[ℱ n] (predictorLikelihoodRatio ν q ξ n) := by
  classical
  have := Fintype.ofFinite α
  have h_factor : ∀ t < n, Measurable[ℱ n] (fun ω ↦ q t ω (ξ t ω) / ν.real {ξ t ω}) := by
    intro t ht
    have hξt : Measurable[ℱ n] (ξ t) := (hξ t).mono (ℱ.mono ht) le_rfl
    have h_eq : (fun ω ↦ q t ω (ξ t ω) / ν.real {ξ t ω}) =
        fun ω ↦ ∑ a, if ξ t ω = a then q t ω a / ν.real {a} else 0 := by
      ext ω
      simp
    rw [h_eq]
    exact Finset.measurable_sum _ fun a _ ↦ Measurable.ite (hξt (measurableSet_singleton a))
      (((hq t a).mono (ℱ.mono ht.le) le_rfl).div_const _) measurable_const
  rw [show predictorLikelihoodRatio ν q ξ n =
    fun ω ↦ ∏ t ∈ range n, q t ω (ξ t ω) / ν.real {ξ t ω} from
      funext (predictorLikelihoodRatio_def n)]
  exact Finset.measurable_prod _ fun t ht ↦ h_factor t (mem_range.1 ht)

omit [MeasurableSingletonClass α] in
/-- A sub-probability predictor has coordinates at most `1`, so that every factor
`q t ω a / ν{a}` of its likelihood ratio is at most `∑ b, ν{b}⁻¹`. -/
private lemma div_measureReal_le_sum_inv (hq0 : ∀ t ω a, 0 ≤ q t ω a)
    (hq1 : ∀ t ω, ∑ a, q t ω a ≤ 1) (t : ℕ) (ω : Ω) (a : α) :
    q t ω a / ν.real {a} ≤ ∑ b, (ν.real {b})⁻¹ := by
  rw [div_eq_mul_inv]
  calc q t ω a * (ν.real {a})⁻¹ ≤ 1 * (ν.real {a})⁻¹ := by
        gcongr
        exact (single_le_sum (fun b _ ↦ hq0 t ω b) (mem_univ _)).trans (hq1 t ω)
    _ ≤ ∑ b, (ν.real {b})⁻¹ := by
        rw [one_mul]
        exact single_le_sum (f := fun b ↦ (ν.real {b})⁻¹)
          (fun _ _ ↦ inv_nonneg.2 measureReal_nonneg) (mem_univ _)

omit [MeasurableSingletonClass α] in
/-- The likelihood ratio of a sub-probability predictor after `n` observations is at most
`(∑ a, ν{a}⁻¹) ^ n`. -/
private lemma predictorLikelihoodRatio_le (hq0 : ∀ t ω a, 0 ≤ q t ω a)
    (hq1 : ∀ t ω, ∑ a, q t ω a ≤ 1) (n : ℕ) (ω : Ω) :
    predictorLikelihoodRatio ν q ξ n ω ≤ (∑ a, (ν.real {a})⁻¹) ^ n := by
  rw [predictorLikelihoodRatio_def]
  exact (prod_le_prod₀ (g := fun _ ↦ ∑ a, (ν.real {a})⁻¹)
    (fun t _ ↦ div_nonneg (hq0 _ _ _) measureReal_nonneg)
    fun t _ ↦ div_measureReal_le_sum_inv hq0 hq1 t ω (ξ t ω)).trans_eq (by simp)

/-- The likelihood ratio of a sub-probability predictor is integrable. -/
lemma integrable_predictorLikelihoodRatio {μ : Measure Ω} [IsFiniteMeasure μ]
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t)) (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a))
    (hq0 : ∀ t ω a, 0 ≤ q t ω a) (hq1 : ∀ t ω, ∑ a, q t ω a ≤ 1) (n : ℕ) :
    Integrable (predictorLikelihoodRatio ν q ξ n) μ :=
  Integrable.of_mem_Icc 0 _
    ((measurable_predictorLikelihoodRatio hξ hq n).mono (ℱ.le n) le_rfl).aemeasurable
    (ae_of_all _ fun ω ↦
      ⟨predictorLikelihoodRatio_nonneg hq0 n ω, predictorLikelihoodRatio_le hq0 hq1 n ω⟩)

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Fintype α] in
/-- The densities `q t ω a / ν{a}` of the predictions with respect to `ν`, in `ℝ≥0∞`, are
measurable for `ℱ t` and `α` jointly. -/
private lemma measurable_uncurry_ofReal_div [Countable α]
    (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a)) (t : ℕ) :
    Measurable[(ℱ t).prod inferInstance]
      (Function.uncurry fun ω a ↦ ENNReal.ofReal (q t ω a / ν.real {a})) :=
  measurable_from_prod_countable_left (m := ℱ t) fun a ↦
    ((hq t a).div_const (ν.real {a})).ennreal_ofReal

omit [Fintype α] [MeasurableSingletonClass α] in
/-- The likelihood ratio is the real value of the product of the densities
`ofReal (q t ω (ξ t ω) / ν{ξ t ω})`. -/
private lemma toReal_prod_ofReal_div (hq0 : ∀ t ω a, 0 ≤ q t ω a) :
    (fun n ω ↦ (∏ t ∈ range n, ENNReal.ofReal (q t ω (ξ t ω) / ν.real {ξ t ω})).toReal) =
      predictorLikelihoodRatio ν q ξ := by
  ext n ω
  have h0 : ∀ t ∈ range n, 0 ≤ q t ω (ξ t ω) / ν.real {ξ t ω} := fun t _ ↦
    div_nonneg (hq0 _ _ _) measureReal_nonneg
  rw [predictorLikelihoodRatio_def, ← ENNReal.ofReal_prod_of_nonneg h0,
    ENNReal.toReal_ofReal (prod_nonneg h0)]

/-- **The likelihood ratio of a sub-probability predictor is a supermartingale.** Let `ξ t` be
`ℱ (t + 1)`-measurable, independent of `ℱ t` and of law `ν`, and let the predictor `q t` be
`ℱ t`-measurable with `q t ω` nonnegative of total mass at most `1`. Then
`L_n = ∏_{t < n} q t (ξ t) / ν{ξ t}` is a supermartingale for `ℱ`.

This is the case of a finite alphabet, and of the constant conditional laws `ν`, of
`ProbabilityTheory.isTestSupermartingale_prod_of_hasCondLaw`, with the densities `q t ω a / ν{a}`
of the predictions with respect to `ν`. -/
theorem supermartingale_predictorLikelihoodRatio (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (ξ t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (ξ t) ν μ) (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a))
    (hq0 : ∀ t ω a, 0 ≤ q t ω a) (hq1 : ∀ t ω, ∑ a, q t ω a ≤ 1) :
    Supermartingale (predictorLikelihoodRatio ν q ξ) ℱ μ := by
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have hT := isTestSupermartingale_prod_of_hasCondLaw hξ
    (fun t ↦ hasCondLaw_of_indep (ℱ.le t) (hind t) (hlaw t))
    (measurable_uncurry_ofReal_div hq) fun t ↦ ae_of_all μ fun ω ↦
      (lintegral_ofReal_div_measureReal_le (hq0 t ω)).trans (ENNReal.ofReal_le_one.2 (hq1 t ω))
  rw [← toReal_prod_ofReal_div hq0]
  exact hT.supermartingale_toReal (Set.mem_singleton μ)

/-- **The likelihood ratio of a probability predictor is a martingale.** Let `ξ t` be
`ℱ (t + 1)`-measurable, independent of `ℱ t` and of a law `ν` that charges every point, and let
the predictor `q t` be `ℱ t`-measurable with `q t ω` a probability vector. Then
`L_n = ∏_{t < n} q t (ξ t) / ν{ξ t}` is a martingale for `ℱ`.

This is the case of a finite alphabet, and of the constant conditional laws `ν`, of
`ProbabilityTheory.isTestMartingale_prod_of_hasCondLaw`. -/
theorem martingale_predictorLikelihoodRatio (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (ξ t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (ξ t) ν μ) (hν : ∀ a, ν {a} ≠ 0)
    (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a)) (hq0 : ∀ t ω a, 0 ≤ q t ω a)
    (hq1 : ∀ t ω, ∑ a, q t ω a = 1) :
    Martingale (predictorLikelihoodRatio ν q ξ) ℱ μ := by
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have hT := isTestMartingale_prod_of_hasCondLaw hξ
    (fun t ↦ hasCondLaw_of_indep (ℱ.le t) (hind t) (hlaw t))
    (measurable_uncurry_ofReal_div hq) fun t ↦ ae_of_all μ fun ω ↦ by
      rw [lintegral_ofReal_div_measureReal_eq hν (hq0 t ω), hq1 t ω, ENNReal.ofReal_one]
  rw [← toReal_prod_ofReal_div hq0]
  exact hT.martingale_toReal (Set.mem_singleton μ)

/-- **The likelihood ratio of a probability predictor has mean one**, under the hypotheses of
`LMLExplore.martingale_predictorLikelihoodRatio`. -/
theorem integral_predictorLikelihoodRatio (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (ξ t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (ξ t) ν μ) (hν : ∀ a, ν {a} ≠ 0)
    (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a)) (hq0 : ∀ t ω a, 0 ≤ q t ω a)
    (hq1 : ∀ t ω, ∑ a, q t ω a = 1) (n : ℕ) :
    ∫ ω, predictorLikelihoodRatio ν q ξ n ω ∂μ = 1 := by
  have h := (martingale_predictorLikelihoodRatio hξ hind hlaw hν hq hq0 hq1).setIntegral_eq
    (Nat.zero_le n) MeasurableSet.univ
  simpa using h.symm

end Filtration

end LMLExplore
