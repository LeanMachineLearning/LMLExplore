/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.EffectiveSet.Basic
public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import LMLExplore.EValues.KLInf
public import LMLExplore.EValues.Null.Basic
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import Mathlib.Probability.Process.HittingTime
import LMLExplore.EValues.BipolarRate.StoppingTime
import LMLExplore.EValues.EffectiveSet.CountableMixture
import LMLExplore.EValues.TestBet
import LMLExplore.EValues.TestSupermartingale.ConvexHull
import LMLExplore.MeasureTheory.Integral.Lebesgue.Countable
import TauCeti.Data.EReal.Operations

/-!
# Tests between two nulls

Let `H₀` and `H₁` be two nulls on `𝓧`, the members of `H₁` probability measures that charge
every point of `𝓧`. The observations are the coordinates of `ℕ → 𝓧`, with the filtration
`Filtration.piLT` of the past observations. Let `M` be an e-process for the i.i.d. null of `H₀`,
`M'` a test supermartingale for the i.i.d. null of `H₁`, and `α, β` levels with `α + β ≤ 1`. The
test stops at the first time `min τ τ'`, with `τ` the first time that `α⁻¹ ≤ M` (rejecting `H₀`)
and `τ'` the first time that `β⁻¹ ≤ M'` (rejecting `H₁`). On a countable alphabet, it makes at
least `kl(1 - α, β) / a₁(Q, H₁)` observations in expectation under the i.i.d. law of every
`Q ∈ H₀`, where `kl` is the relative entropy of Bernoulli laws and `a₁(Q, H₁) = maxEPower Q H₁`
the largest expected logarithm of an e-variable of one observation for `H₁`
[EVR26, Note 32, Statement 1]. The bound is in `ℝ≥0∞`: if `a₁(Q, H₁) = 0` and `α + β < 1`, the
expected number of observations is infinite. And if `Q ∈ H₀` is also in the effective null of
`H₁`, for instance if its masses are pointwise limits of those of mixtures of members of `H₁`,
the test stops with probability at most `α + β` under the i.i.d. law of `Q`.

**The proof.** Since the members of `H₁` charge every point, `M'` is a test supermartingale for
the i.i.d. law of every probability measure of the effective null of `H₁`
(`ProbabilityTheory.isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull`), in particular
of every countable mixture `R` of members of `H₁`. Let `A` be the event `τ' ≤ τ`, known
at the stopping time `min τ τ'`. Under the i.i.d. law of `Q`, the complement of `A` has
probability at most `α`, since the first test rejects there; under the i.i.d. law of `R`, the test
stops on `A` with probability at most `β`, since the second test rejects there. The bet on `A`
(`ProbabilityTheory.testBet`), which pays `(1 - α) / β` on `A` and `α / (1 - β)` off `A`, is then
an e-variable at the stopping time for the simple null `{R}`, with expected logarithm at least
`kl(1 - α, β)` under the i.i.d. law of `Q`. Wald's inequality at the bipolar rate of `{R}`, which
is `KL(Q ‖ R)` (`ProbabilityTheory.eintegral_log_le_lintegral_mul_bipolarRate`), gives
`kl(1 - α, β) ≤ 𝔼[min τ τ'] KL(Q ‖ R)`. On a countable alphabet, the infimum of `KL(Q ‖ R)` over
the countable mixtures `R` of members of `H₁` is `a₁(Q, H₁)`
(`ProbabilityTheory.maxEPower_eq_iInf_klIntegral_sigmaConvexHull`). At the levels `α = 0` and
`β = 0` the bet is replaced by `𝟙_A / β` and by `∞ 𝟙_A + 1`.

## Main statements

* `ProbabilityTheory.klBer_div_maxEPower_le_lintegral_min_hittingAfter`
  [EVR26, Note 32, Statement 1]: the test between two nulls makes at least
  `kl(1 - α, β) / a₁(Q, H₁)` observations in expectation under the i.i.d. law of `Q ∈ H₀`.
* `ProbabilityTheory.measure_min_hittingAfter_lt_top_le_of_mem_effectiveSet`,
  `ProbabilityTheory.measure_min_hittingAfter_lt_top_le_of_tendsto`
  [EVR26, Note 32, Statement 1]: it stops with probability at most `α + β` under the i.i.d. law
  of a law of `H₀` in the effective null of `H₁`, in particular of a law of `H₀` whose masses are
  limits of those of mixtures of members of `H₁`.

## Implementation notes

The statements and proofs are adapted from `EValuesResearch/Results/ConvexPiecesTests.lean`
(commit `83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore: `M` is an e-process rather than a test supermartingale, the levels are in `ℝ≥0∞`, the
bound on the probability of stopping is stated for the effective null, and the bet on the event is
`ProbabilityTheory.testBet`.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Filter Set LMLExplore
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSingletonClass 𝓧]
  {H₀ H₁ : Set (Measure 𝓧)} {M M' : ℕ → (ℕ → 𝓧) → ℝ≥0∞}

/-- The countable mixtures of probability measures are probability measures. -/
private lemma isProbabilityMeasure_of_mem_sigmaConvexHull {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {S : Set (Measure Ω)} (hS : ∀ P ∈ S, IsProbabilityMeasure P) {R : Measure Ω}
    (hR : R ∈ sigmaConvexHull S) : IsProbabilityMeasure R := by
  obtain ⟨w, Qs, hw, hQs, rfl⟩ := mem_sigmaConvexHull_iff.1 hR
  constructor
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp [fun i ↦ (hS _ (hQs i)).measure_univ, hw]

/-- The test of a test supermartingale for the i.i.d. null of laws that charge every point has
level `β` under the i.i.d. law of every probability measure of the effective null. -/
private lemma isLevelStoppingTime_hittingAfter_infinitePi_of_mem_effectiveSet
    (hH₁ : ∀ P ∈ H₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ H₁, ∀ x, P {x} ≠ 0)
    (hM' : IsTestSupermartingale M' Filtration.piLT (iidNull H₁)) {R : Measure 𝓧}
    [IsProbabilityMeasure R] (hR : R ∈ effectiveSet H₁) (β : ℝ≥0∞) :
    IsLevelStoppingTime (hittingAfter M' (Ici β⁻¹) 0) Filtration.piLT
      {Measure.infinitePi fun _ : ℕ ↦ R} β :=
  have hR' : R ∈ effectiveSet H₁ ∩ {P | IsProbabilityMeasure P} := ⟨hR, inferInstance⟩
  (((isTestSupermartingale_sequentialNull_effectiveSet_of_iidNull hH₁ hpos hM').anti_set
    (singleton_subset_iff.2 (infinitePi_mem_sequentialNull fun _ ↦ .of_forall fun _ ↦
      hR'))).isEProcess (by rintro _ rfl; infer_instance)).isLevelStoppingTime_hittingAfter β

/-- **A test between two nulls makes at least `kl(1 - α, β) / a₁` observations**
[EVR26, Note 32, Statement 1]. On a countable alphabet, let `H₁` be a set of probability measures
that charge every point, `H₀` a set of measures, `M` an e-process for the i.i.d. null of `H₀`,
`M'` a test supermartingale for the i.i.d. null of `H₁`, and `α + β ≤ 1`. The test that stops the
first time `α⁻¹ ≤ M` (rejecting `H₀`) or `β⁻¹ ≤ M'` (rejecting `H₁`) makes, under the i.i.d. law
of a probability measure `Q ∈ H₀`, at least `kl(1 - α, β) / a₁(Q, H₁)` observations in
expectation, where `kl` is the relative entropy of Bernoulli laws and
`a₁(Q, H₁) = maxEPower Q H₁` is the largest expected logarithm of an e-variable of one
observation for `H₁`. The left side is in `ℝ≥0∞`: if
`a₁(Q, H₁) = 0` and `α + β < 1`, the expected number of observations is infinite. -/
theorem klBer_div_maxEPower_le_lintegral_min_hittingAfter [Countable 𝓧]
    (hH₁ : ∀ P ∈ H₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ H₁, ∀ x, P {x} ≠ 0)
    (hM : IsEProcess M Filtration.piLT (iidNull H₀))
    (hM' : IsTestSupermartingale M' Filtration.piLT (iidNull H₁)) {α β : ℝ≥0∞}
    (hαβ : α + β ≤ 1) {Q : Measure 𝓧} [IsProbabilityMeasure Q] (hQ : Q ∈ H₀) :
    klBer (1 - α.toReal) β.toReal / (maxEPower Q H₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (min (hittingAfter M (Ici α⁻¹) 0 ω)
        (hittingAfter M' (Ici β⁻¹) 0 ω)) ∂Measure.infinitePi (fun _ : ℕ ↦ Q) := by
  classical
  set Q₀ := Measure.infinitePi (fun _ : ℕ ↦ Q)
  set τ := hittingAfter M (Ici α⁻¹) 0
  set τ' := hittingAfter M' (Ici β⁻¹) 0
  have hτ : IsStoppingTime Filtration.piLT τ :=
    hM.adapted.isStoppingTime_hittingAfter measurableSet_Ici
  have hτ' : IsStoppingTime Filtration.piLT τ' :=
    hM'.adapted.isStoppingTime_hittingAfter measurableSet_Ici
  have hT := hτ.min hτ'
  set m := ∫⁻ ω, ENat.toENNReal (min (τ ω) (τ' ω)) ∂Q₀
  rcases eq_or_ne m ⊤ with hm | hm
  · rw [hm]
    exact le_top
  rcases H₁.eq_empty_or_nonempty with rfl | hne
  · have : NeZero Q := ⟨IsProbabilityMeasure.ne_zero Q⟩
    rw [maxEPower_empty, EReal.toENNReal_top, ENNReal.div_top]
    exact zero_le
  -- the levels as real numbers
  have hα1 : α ≤ 1 := le_self_add.trans hαβ
  have hβ1 : β ≤ 1 := le_add_self.trans hαβ
  set a := α.toReal
  set b := β.toReal
  have hαa : α = ENNReal.ofReal a :=
    (ENNReal.ofReal_toReal (hα1.trans_lt ENNReal.one_lt_top).ne).symm
  have hβb : β = ENNReal.ofReal b :=
    (ENNReal.ofReal_toReal (hβ1.trans_lt ENNReal.one_lt_top).ne).symm
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hab : a + b ≤ 1 := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hαβ
    rwa [ENNReal.toReal_add (hα1.trans_lt ENNReal.one_lt_top).ne
      (hβ1.trans_lt ENNReal.one_lt_top).ne, ENNReal.toReal_one] at h
  -- a test with a finite expected number of observations stops almost surely
  have hTQ : ∀ᵐ ω ∂Q₀, min (τ ω) (τ' ω) ≠ ⊤ := by
    filter_upwards [ae_lt_top (measurable_from_top.comp hT.measurable_enat) hm] with ω hω h
    exact (show ENat.toENNReal (min (τ ω) (τ' ω)) < ⊤ from hω).ne (ENat.toENNReal_eq_top.2 h)
  -- the event that the second test rejects first, known at the stopping time
  set A := {ω | τ' ω ≤ τ ω}
  have hAT : MeasurableSet[hT.measurableSpace] A :=
    (IsStoppingTime.measurableSet_min_iff hτ hτ' A).2
      ⟨IsStoppingTime.measurableSet_stopping_time_le hτ' hτ,
        IsStoppingTime.measurableSet_le_stopping_time hτ' hτ⟩
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hAT
  set s := {ω | min (τ ω) (τ' ω) ≠ ⊤}
  -- under the i.i.d. law of `Q ∈ H₀`, the first test rejects with probability at most `α`
  have hAc : Q₀ Aᶜ ≤ ENNReal.ofReal a := by
    rw [← hαa]
    refine (measure_mono fun ω hω ↦ ?_).trans
      ((hM.isLevelStoppingTime_hittingAfter α).measure_lt_top_le Q₀ (infinitePi_mem_iidNull hQ))
    exact lt_of_lt_of_le (not_le.1 (show ¬ τ' ω ≤ τ ω from hω)) le_top
  have hQA : ENNReal.ofReal (1 - a) ≤ Q₀ A := by
    calc ENNReal.ofReal (1 - a) = 1 - ENNReal.ofReal a := by
          rw [ENNReal.ofReal_sub _ ha0, ENNReal.ofReal_one]
      _ ≤ 1 - Q₀ Aᶜ := tsub_le_tsub_left hAc 1
      _ = Q₀ A := by
        rw [prob_compl_eq_one_sub hAm, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  -- Wald's inequality for the simple null `{R}`, for a countable mixture `R` of `H₁`
  have hW : ∀ R ∈ sigmaConvexHull H₁, ∀ Y : (ℕ → 𝓧) → ℝ≥0∞, Measurable[hT.measurableSpace] Y →
      ∫⁻ ω in s, Y ω ∂(Measure.infinitePi fun _ : ℕ ↦ R) ≤ 1 →
      ∫ᵉ ω, ENNReal.log (Y ω) ∂Q₀ ≤ ((m * klDiv Q R : ℝ≥0∞) : EReal) := by
    intro R hR Y hY hYR
    have := isProbabilityMeasure_of_mem_sigmaConvexHull hH₁ hR
    have h := eintegral_log_le_lintegral_mul_bipolarRate Q (S₁ := {R})
      (by rintro _ rfl; infer_instance) (singleton_nonempty R) hT hY
      (by rintro _ rfl; exact hYR) hTQ
    rwa [bipolarRate_singleton, ← EReal.coe_ennreal_mul] at h
  -- the main bound, for each countable mixture `R` of `H₁`
  have hmain : ∀ R ∈ sigmaConvexHull H₁, klBer (1 - a) b ≤ m * klDiv Q R := by
    intro R hR
    have := isProbabilityMeasure_of_mem_sigmaConvexHull hH₁ hR
    set R₀ := Measure.infinitePi fun _ : ℕ ↦ R
    -- under the i.i.d. law of `R`, the test stops on `A` with probability at most `β`
    have hRA : R₀ (A ∩ s) ≤ ENNReal.ofReal b := by
      rw [← hβb]
      refine (measure_mono fun ω hω ↦ ?_).trans
        ((isLevelStoppingTime_hittingAfter_infinitePi_of_mem_effectiveSet hH₁ hpos hM'
          (isSigmaConvex_effectiveSet.sigmaConvexHull_subset subset_effectiveSet hR)
          β).measure_lt_top_le R₀ rfl)
      have h2 : min (τ ω) (τ' ω) ≠ ⊤ := hω.2
      rw [min_eq_right (show τ' ω ≤ τ ω from hω.1)] at h2
      exact lt_top_iff_ne_top.2 h2
    have hRs : R₀.restrict s univ ≤ 1 := by
      rw [Measure.restrict_apply_univ]
      exact prob_le_one
    have hind1 (ω : ℕ → 𝓧) : A.indicator (1 : (ℕ → 𝓧) → ℝ≥0∞) ω ≤ 1 := by
      by_cases hω : ω ∈ A <;> simp [hω]
    have hindT : Measurable[hT.measurableSpace] (A.indicator (1 : (ℕ → 𝓧) → ℝ≥0∞)) :=
      measurable_const.indicator hAT
    have hRind : ∫⁻ ω, A.indicator 1 ω ∂R₀.restrict s ≤ ENNReal.ofReal b := by
      rw [lintegral_indicator_one hAm, Measure.restrict_apply hAm]
      exact hRA
    rcases eq_or_ne (klBer (1 - a) b) 0 with h0 | h0
    · rw [h0]
      exact zero_le
    have hba : b < 1 - a := lt_of_le_of_ne (by linarith) fun h ↦ h0 (h ▸ klBer_self _)
    rcases hb0.eq_or_lt with hb | hb
    · -- `β = 0`: the bet `∞` on `A` and `1` off `A`, so that `m * KL(Q ‖ R) = ∞`
      suffices h : m * klDiv Q R = ⊤ by
        rw [h]
        exact le_top
      have hQA0 : Q₀ A ≠ 0 := ((ENNReal.ofReal_pos.2 (by linarith)).trans_le hQA).ne'
      have hK := hW R hR (fun ω ↦ A.indicator (fun _ ↦ ∞) ω + 1)
        ((measurable_const.indicator hAT).add measurable_const) (by
          rw [lintegral_add_left (measurable_const.indicator hAm), lintegral_indicator_const hAm,
            Measure.restrict_apply hAm, show R₀ (A ∩ s) = 0 from
              nonpos_iff_eq_zero.1 (hRA.trans_eq (by rw [← hb, ENNReal.ofReal_zero])),
            mul_zero, zero_add, lintegral_one]
          exact hRs)
      have hlog (ω : ℕ → 𝓧) : ENNReal.log (A.indicator (fun _ ↦ ∞) ω + 1) =
          ((A.indicator (fun _ ↦ ∞) ω : ℝ≥0∞) : EReal) := by
        by_cases hω : ω ∈ A <;> simp [hω]
      rw [eintegral_congr hlog, eintegral_coe_ennreal, lintegral_indicator_const hAm,
        ENNReal.top_mul hQA0, EReal.coe_ennreal_top, top_le_iff,
        EReal.coe_ennreal_eq_top_iff] at hK
      exact hK
    rcases ha0.eq_or_lt with ha | ha
    · -- `α = 0`: the bet `1/β` on `A`, which holds almost surely under the i.i.d. law of `Q`
      have hAc0 : Q₀ Aᶜ = 0 :=
        nonpos_iff_eq_zero.1 (hAc.trans_eq (by rw [← ha, ENNReal.ofReal_zero]))
      have hK := hW R hR (testBet b 1 (A.indicator 1)) (Measurable.testBet hindT)
        (lintegral_testBet_le_one (measurable_one.indicator hAm) hind1 ⟨hb, by linarith⟩
          (by linarith) le_rfl hRs hRind)
      have hae : ∀ᵐ ω ∂Q₀, ENNReal.log (testBet b 1 (A.indicator 1) ω) =
          ((-Real.log b : ℝ) : EReal) := by
        filter_upwards [show ∀ᵐ ω ∂Q₀, ω ∈ A from ae_iff.2 hAc0] with ω hω
        rw [testBet_indicator_of_mem hω, ENNReal.log_ofReal_of_pos (by positivity), div_eq_inv_mul,
          mul_one, Real.log_inv]
      rw [eintegral_congr_ae hae, eintegral_const, measure_univ, EReal.coe_ennreal_one,
        mul_one] at hK
      -- `kl(1, β) = log (1/β)`
      have hkl : klBer 1 b = ENNReal.ofReal (-Real.log b) := by
        have h := klBer_zero_left (q := 1 - b) (by linarith)
        rwa [← klBer_one_sub_one_sub, sub_zero, sub_sub_cancel] at h
      rw [← ha, sub_zero, hkl, ← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_ennreal_ofReal,
        max_eq_left (neg_nonneg.2 (Real.log_nonpos hb0 (by linarith)))]
      exact hK
    · -- the general case: the bet on `A` of the test of level `β` with power `1 - α`
      have h1 := klBer_le_eintegral_log_testBet (Q := Q₀) (measurable_one.indicator hAm) hind1 hb
        hba.le (by linarith) (by rwa [lintegral_indicator_one hAm])
      have h2 := hW R hR (testBet b (1 - a) (A.indicator 1)) (Measurable.testBet hindT)
        (lintegral_testBet_le_one (measurable_one.indicator hAm) hind1 ⟨hb, by linarith⟩ hba.le
          (by linarith) hRs hRind)
      exact EReal.coe_ennreal_le_coe_ennreal_iff.1 (h1.trans h2)
  -- the largest e-power is the infimum over the countable mixtures of the relative entropy
  have hdual : (maxEPower Q H₁).toENNReal = ⨅ R ∈ sigmaConvexHull H₁, klDiv Q R := by
    rw [maxEPower_eq_iInf_klIntegral_sigmaConvexHull (μ := Measure.count)
      (fun P _ s hs ↦ by rw [Measure.count_eq_zero_iff] at hs; simp [hs])
      (fun P hP ↦ (hH₁ P hP).measure_univ.le)]
    have hR : ∀ R ∈ sigmaConvexHull H₁, klIntegral Q R = (klDiv Q R : EReal) := fun R hR ↦ by
      have := isProbabilityMeasure_of_mem_sigmaConvexHull hH₁ hR
      exact klIntegral_eq_klDiv (by simp)
    rw [iInf_congr fun R ↦ iInf_congr fun hR' ↦ hR R hR']
    simp_rw [← EReal.coe_ennreal_iInf]
    rw [EReal.toENNReal_coe]
  rw [hdual]
  rcases eq_or_ne m 0 with hm0 | hm0
  · obtain ⟨P, hP⟩ := hne
    have h := hmain P (subset_sigmaConvexHull hP)
    rw [hm0, zero_mul, nonpos_iff_eq_zero] at h
    rw [h, ENNReal.zero_div]
    exact zero_le
  have hk : klBer (1 - a) b / m ≤ ⨅ R ∈ sigmaConvexHull H₁, klDiv Q R :=
    le_iInf₂ fun R hR ↦ ENNReal.div_le_of_le_mul' (hmain R hR)
  exact ENNReal.div_le_of_le_mul (((ENNReal.div_le_iff hm0 hm).1 hk).trans_eq (mul_comm _ _))

/-- **A test between two nulls does not stop at a law of the effective null of the second**
[EVR26, Note 32, Statement 1]. Let `H₁` be a set of probability measures that charge every point,
`M` an e-process for the i.i.d. null of a set `H₀` and `M'` a test supermartingale for the i.i.d.
null of `H₁`. Under the i.i.d. law of a probability measure `Q ∈ H₀` of the effective null of
`H₁`, the test that stops the first time `α⁻¹ ≤ M` or `β⁻¹ ≤ M'` stops with probability at most
`α + β`. -/
theorem measure_min_hittingAfter_lt_top_le_of_mem_effectiveSet
    (hH₁ : ∀ P ∈ H₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ H₁, ∀ x, P {x} ≠ 0)
    (hM : IsEProcess M Filtration.piLT (iidNull H₀))
    (hM' : IsTestSupermartingale M' Filtration.piLT (iidNull H₁)) (α β : ℝ≥0∞)
    {Q : Measure 𝓧} [IsProbabilityMeasure Q] (hQ₀ : Q ∈ H₀) (hQ₁ : Q ∈ effectiveSet H₁) :
    Measure.infinitePi (fun _ : ℕ ↦ Q)
      {ω | min (hittingAfter M (Ici α⁻¹) 0 ω) (hittingAfter M' (Ici β⁻¹) 0 ω) < ⊤} ≤ α + β :=
  (((hM.isLevelStoppingTime_hittingAfter α).anti_set
    (singleton_subset_iff.2 (infinitePi_mem_iidNull hQ₀))).min
    (isLevelStoppingTime_hittingAfter_infinitePi_of_mem_effectiveSet hH₁ hpos hM' hQ₁
      β)).measure_lt_top_le _ rfl

/-- **A test between two nulls does not stop at a limit of mixtures of the second**
[EVR26, Note 32, Statement 1]. Under the hypotheses of
`measure_min_hittingAfter_lt_top_le_of_mem_effectiveSet`, on a countable alphabet, if the masses
of `Q ∈ H₀` are the limits, along a filter, of those of mixtures of members of `H₁`, the test that
stops the first time `α⁻¹ ≤ M` or `β⁻¹ ≤ M'` stops with probability at most `α + β` under the
i.i.d. law of `Q`: it never stops with probability at least `1 - α - β`. -/
theorem measure_min_hittingAfter_lt_top_le_of_tendsto [Countable 𝓧]
    (hH₁ : ∀ P ∈ H₁, IsProbabilityMeasure P) (hpos : ∀ P ∈ H₁, ∀ x, P {x} ≠ 0)
    (hM : IsEProcess M Filtration.piLT (iidNull H₀))
    (hM' : IsTestSupermartingale M' Filtration.piLT (iidNull H₁)) (α β : ℝ≥0∞)
    {Q : Measure 𝓧} [IsProbabilityMeasure Q] (hQ : Q ∈ H₀)
    {ι : Type*} {l : Filter ι} [l.NeBot] {R : ι → Measure 𝓧}
    (hR : ∀ᶠ i in l, R i ∈ convexHull ℝ≥0∞ H₁)
    (hQR : ∀ x, Tendsto (fun i ↦ R i {x}) l (𝓝 (Q {x}))) :
    Measure.infinitePi (fun _ : ℕ ↦ Q)
      {ω | min (hittingAfter M (Ici α⁻¹) 0 ω) (hittingAfter M' (Ici β⁻¹) 0 ω) < ⊤} ≤ α + β := by
  -- `Q` is in the effective null of `H₁`, by Fatou's lemma for sums
  refine measure_min_hittingAfter_lt_top_le_of_mem_effectiveSet hH₁ hpos hM hM' α β hQ
    (mem_effectiveSet_of_measure_le_liminf (hR.mono fun i hi ↦ convexHull_subset_effectiveSet hi)
      fun s hs ↦ ?_)
  simpa [lintegral_indicator_one hs] using
    lintegral_le_liminf_of_tendsto_measure_singleton hQR (s.indicator 1)

end ProbabilityTheory
