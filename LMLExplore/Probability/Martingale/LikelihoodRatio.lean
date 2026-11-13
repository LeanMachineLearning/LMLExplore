/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Martingale.Basic

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

The supermartingale property is adapted, and generalised from Laplace's rule of succession to
every predictor, from `InformationTheory/KLTimeUniform.lean` of the formalization
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

/-- The one-step identity behind the (super)martingale property: for `s ∈ ℱ n`,
`∫_s L_{n + 1} = ∫_s L_n ∑ a, ν{a} q n a / ν{a}`, since `ξ n` is independent of `ℱ n` with law
`ν`. -/
private lemma setIntegral_predictorLikelihoodRatio_succ (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (ξ t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (ξ t) ν μ) (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a))
    (hq0 : ∀ t ω a, 0 ≤ q t ω a) (hq1 : ∀ t ω, ∑ a, q t ω a ≤ 1) (n : ℕ) {s : Set Ω}
    (hs : MeasurableSet[ℱ n] s) :
    ∫ ω in s, predictorLikelihoodRatio ν q ξ (n + 1) ω ∂μ =
      ∫ ω in s, predictorLikelihoodRatio ν q ξ n ω *
        ∑ a, ν.real {a} * (q n ω a / ν.real {a}) ∂μ := by
  classical
  set L := predictorLikelihoodRatio ν q ξ with hL
  set C : ℝ := ∑ a, (ν.real {a})⁻¹
  have hC0 : 0 ≤ C := sum_nonneg fun a _ ↦ inv_nonneg.2 measureReal_nonneg
  have hξm : Measurable (ξ n) := (hξ n).mono (ℱ.le _) le_rfl
  have hsm : MeasurableSet s := ℱ.le n s hs
  -- `F a = 1_s L_n q n a / ν{a}`, measurable for `ℱ n`, and `G a = 1_{ξ n = a}`
  set F : α → Ω → ℝ := fun a ↦ s.indicator fun ω ↦ L n ω * (q n ω a / ν.real {a}) with hF
  set G : α → Ω → ℝ := fun a ↦ (ξ n ⁻¹' {a}).indicator 1 with hG
  have hFmeas : ∀ a, Measurable[ℱ n] (F a) := fun a ↦
    ((measurable_predictorLikelihoodRatio hξ hq n).mul ((hq n a).div_const _)).indicator hs
  have hGmeas : ∀ a, Measurable[MeasurableSpace.comap (ξ n) inferInstance] (G a) := fun a ↦
    measurable_const.indicator (comap_measurable (ξ n) (measurableSet_singleton a))
  have hFm : ∀ a, Measurable (F a) := fun a ↦ (hFmeas a).mono (ℱ.le n) le_rfl
  have hGm : ∀ a, Measurable (G a) := fun a ↦
    measurable_const.indicator (hξm (measurableSet_singleton a))
  have hFint : ∀ a, Integrable (F a) μ := fun a ↦ by
    refine Integrable.of_mem_Icc 0 (C ^ n * C) (hFm a).aemeasurable (ae_of_all _ fun ω ↦ ?_)
    have h0 : 0 ≤ q n ω a / ν.real {a} := div_nonneg (hq0 n ω a) measureReal_nonneg
    simp only [hF, Set.indicator_apply]
    split_ifs
    · exact ⟨mul_nonneg (predictorLikelihoodRatio_nonneg hq0 n ω) h0,
        mul_le_mul (predictorLikelihoodRatio_le hq0 hq1 n ω)
          (div_measureReal_le_sum_inv hq0 hq1 n ω a) h0 (pow_nonneg hC0 n)⟩
    · exact ⟨le_rfl, mul_nonneg (pow_nonneg hC0 n) hC0⟩
  -- `1_s L_{n + 1} = ∑ a, F a G a`, by the value of `ξ n`
  have h_decomp : s.indicator (L (n + 1)) = fun ω ↦ ∑ a, F a ω * G a ω := by
    ext ω
    by_cases hω : ω ∈ s
    · simp only [hF, hG, Set.indicator_apply, hω, ite_true, Set.mem_preimage,
        Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ,
        hL, predictorLikelihoodRatio_succ]
    · simp [hF, Set.indicator_of_notMem hω]
  -- independence of `ξ n` from `ℱ n`
  have h_indep : ∀ a, ∫ ω, F a ω * G a ω ∂μ = ∫ ω, F a ω * ν.real {a} ∂μ := fun a ↦ by
    have hFG : IndepFun (F a) (G a) μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (hind n).symm
        (hFmeas a).comap_le) (hGmeas a).comap_le
    rw [hFG.integral_fun_mul_eq_mul_integral (hFm a).aestronglyMeasurable
      (hGm a).aestronglyMeasurable, hG, integral_indicator_one (hξm (measurableSet_singleton a)),
      ← map_measureReal_apply hξm (measurableSet_singleton a), (hlaw n).map_eq,
      integral_mul_const]
  have hFG_int : ∀ a, Integrable (fun ω ↦ F a ω * G a ω) μ := fun a ↦
    (hFint a).mul_of_top_left (memLp_top_of_bound (hGm a).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ by simp only [hG, Set.indicator]; split_ifs <;> simp))
  calc ∫ ω in s, L (n + 1) ω ∂μ = ∫ ω, ∑ a, F a ω * G a ω ∂μ := by
        rw [← integral_indicator hsm, h_decomp]
    _ = ∫ ω, ∑ a, F a ω * ν.real {a} ∂μ := by
        rw [integral_finsetSum _ fun a _ ↦ hFG_int a,
          integral_finsetSum _ fun a _ ↦ (hFint a).mul_const _]
        exact sum_congr rfl fun a _ ↦ h_indep a
    _ = ∫ ω in s, L n ω * ∑ a, ν.real {a} * (q n ω a / ν.real {a}) ∂μ := by
        rw [← integral_indicator hsm]
        refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
        by_cases hω : ω ∈ s
        · simp only [hF, Set.indicator_of_mem hω, mul_sum]
          exact sum_congr rfl fun a _ ↦ by ring
        · simp [hF, Set.indicator_of_notMem hω]

/-- **The likelihood ratio of a sub-probability predictor is a supermartingale.** Let `ξ t` be
`ℱ (t + 1)`-measurable, independent of `ℱ t` and of law `ν`, and let the predictor `q t` be
`ℱ t`-measurable with `q t ω` nonnegative of total mass at most `1`. Then
`L_n = ∏_{t < n} q t (ξ t) / ν{ξ t}` is a supermartingale for `ℱ`. -/
theorem supermartingale_predictorLikelihoodRatio (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (ξ t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (ξ t) ν μ) (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a))
    (hq0 : ∀ t ω a, 0 ≤ q t ω a) (hq1 : ∀ t ω, ∑ a, q t ω a ≤ 1) :
    Supermartingale (predictorLikelihoodRatio ν q ξ) ℱ μ := by
  refine supermartingale_of_setIntegral_succ_le
    (fun n ↦ (measurable_predictorLikelihoodRatio hξ hq n).stronglyMeasurable)
    (integrable_predictorLikelihoodRatio hξ hq hq0 hq1) fun n s hs ↦ ?_
  rw [setIntegral_predictorLikelihoodRatio_succ hξ hind hlaw hq hq0 hq1 n hs]
  -- `∑ a, ν{a} q n a / ν{a} ≤ ∑ a, q n a ≤ 1`
  refine integral_mono_of_nonneg (ae_of_all _ fun ω ↦ mul_nonneg
    (predictorLikelihoodRatio_nonneg hq0 n ω) (sum_nonneg fun a _ ↦ mul_nonneg measureReal_nonneg
      (div_nonneg (hq0 n ω a) measureReal_nonneg)))
    (integrable_predictorLikelihoodRatio hξ hq hq0 hq1 n).integrableOn (ae_of_all _ fun ω ↦ ?_)
  refine mul_le_of_le_one_right (predictorLikelihoodRatio_nonneg hq0 n ω)
    ((sum_le_sum fun a _ ↦ ?_).trans (hq1 n ω))
  rcases eq_or_ne (ν.real {a}) 0 with h0 | h0
  · rw [h0, zero_mul]
    exact hq0 n ω a
  · rw [mul_div_cancel₀ _ h0]

/-- **The likelihood ratio of a probability predictor is a martingale.** Let `ξ t` be
`ℱ (t + 1)`-measurable, independent of `ℱ t` and of a law `ν` that charges every point, and let
the predictor `q t` be `ℱ t`-measurable with `q t ω` a probability vector. Then
`L_n = ∏_{t < n} q t (ξ t) / ν{ξ t}` is a martingale for `ℱ`. -/
theorem martingale_predictorLikelihoodRatio (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hind : ∀ t, Indep (MeasurableSpace.comap (ξ t) inferInstance) (ℱ t) μ)
    (hlaw : ∀ t, HasLaw (ξ t) ν μ) (hν : ∀ a, ν {a} ≠ 0)
    (hq : ∀ t a, Measurable[ℱ t] (fun ω ↦ q t ω a)) (hq0 : ∀ t ω a, 0 ≤ q t ω a)
    (hq1 : ∀ t ω, ∑ a, q t ω a = 1) :
    Martingale (predictorLikelihoodRatio ν q ξ) ℱ μ := by
  have hq1' : ∀ t ω, ∑ a, q t ω a ≤ 1 := fun t ω ↦ (hq1 t ω).le
  have := (hlaw 0).isProbabilityMeasure_iff.1 inferInstance
  have hν' : ∀ a, ν.real {a} ≠ 0 := fun a ↦ (measureReal_ne_zero_iff (measure_ne_top _ _)).2 (hν a)
  refine martingale_of_setIntegral_eq_succ
    (fun n ↦ (measurable_predictorLikelihoodRatio hξ hq n).stronglyMeasurable)
    (integrable_predictorLikelihoodRatio hξ hq hq0 hq1') fun n s hs ↦ ?_
  rw [setIntegral_predictorLikelihoodRatio_succ hξ hind hlaw hq hq0 hq1' n hs]
  -- `∑ a, ν{a} q n a / ν{a} = ∑ a, q n a = 1`
  refine setIntegral_congr_fun (ℱ.le n s hs) fun ω _ ↦ ?_
  simp_rw [mul_div_cancel₀ _ (hν' _), hq1, mul_one]

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
