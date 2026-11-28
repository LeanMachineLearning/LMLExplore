/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
import LMLExplore.EValues.EVariable
import LMLExplore.MeasureTheory.Integral.BoundedMeasurable
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# The game between bets and a null hypothesis

Let `Q` be a probability measure on a measurable space `Ω` (the alternative) and `T` a null
hypothesis, a set of measures on `Ω`. In the game between a statistician and nature, the
statistician chooses a bounded measurable function `g`, that is the bet `exp g`, and nature a
member `P` of the null; the bet pays `betPayoff Q P g = ∫ g ∂Q - log ∫ exp g ∂P`, the expected
logarithm under `Q` of the bet divided by its mean under `P` [EVR26].

* The max–min value `⨆ g, ⨅ P ∈ T, betPayoff Q P g` is the largest e-power `maxEPower Q T`. A
  bet whose payoff is above `c` against every member of the null, divided by
  `exp (∫ g ∂Q - c)`, is an e-variable with expected logarithm `c` under `Q`; conversely, the
  expected logarithm of an e-variable is approached by the means of bounded functions `g` with
  `exp g` an e-variable (`ProbabilityTheory.IsEVar.exists_bounded_lt_integral_of_lt_eintegral_log`),
  whose payoffs against the null are at least `∫ g ∂Q`.
* The min–max value `⨅ P ∈ T, ⨆ g, betPayoff Q P g` is the smallest relative entropy
  `klInf Q T`, by the Donsker–Varadhan formula
  `TauCeti.klDiv_eq_iSup_integral_sub_log_integral_exp` for each member of the null.

For `n` observations, `T = sampleNull S₁ n` and `Q = Q₁ ^ n`, the values are
`maxLogGrowth Q₁ S₁ n` and `n * klInf Q₁ S₁`: the bipolar rate `bipolarRate Q₁ S₁` is the limit
of the max–min values divided by `n`, while the min–max values divided by `n` are all
`klInf Q₁ S₁`. Neither the supremum nor the infimum is attained in general.

## Main definitions

* `ProbabilityTheory.betPayoff Q P g`: the payoff `∫ g ∂Q - log ∫ exp g ∂P` of the bet `exp g`
  against `P`; it is at least `∫ g ∂Q` when `exp g` has mean at most one under `P`
  (`ProbabilityTheory.integral_le_betPayoff`).

## Main statements

* `ProbabilityTheory.iSup_iInf_betPayoff_eq_maxEPower`: the max–min value is the largest
  e-power, for a null of measures of mass at most one.
* `ProbabilityTheory.iInf_iSup_betPayoff_eq_klInf`: the min–max value is the smallest relative
  entropy, for a null of probability measures.
* `ProbabilityTheory.iSup_iInf_betPayoff_sampleNull_eq_maxLogGrowth`,
  `ProbabilityTheory.tendsto_iSup_iInf_betPayoff_sampleNull_div_bipolarRate`: with `n`
  observations the max–min value is `maxLogGrowth Q₁ S₁ n`, and divided by `n` it tends to the
  bipolar rate.
* `ProbabilityTheory.iInf_iSup_betPayoff_sampleNull_eq_mul_klInf`: with `n ≠ 0` observations the
  min–max value is `n * klInf Q₁ S₁`.

## Implementation notes

The payoff is real-valued, with Mathlib's `Real.log`, and the values of the game are taken in
`EReal`. The statements and proofs are adapted from `EValuesResearch/Results/RateGame.lean`
(commit `83205cb`) in the paper project `RemyDegenne/evalues_research`, rewritten on the API of
LMLExplore, where they are stated for the `n`-sample nulls; here they are stated for every null,
and the `n`-sample nulls are instances.

## References

* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
-/

public section

open MeasureTheory InformationTheory Filter
open scoped ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The payoff of the bet `exp g` against the law `P` under the alternative `Q`:
`∫ g ∂Q - log ∫ exp g ∂P`, the expected logarithm under `Q` of the bet divided by its mean
under `P`. -/
noncomputable def betPayoff (Q P : Measure Ω) (g : Ω → ℝ) : ℝ :=
  ∫ x, g x ∂Q - Real.log (∫ x, Real.exp (g x) ∂P)

/-- The payoff of the bet `exp g`, unfolded. -/
lemma betPayoff_def (Q P : Measure Ω) (g : Ω → ℝ) :
    betPayoff Q P g = ∫ x, g x ∂Q - Real.log (∫ x, Real.exp (g x) ∂P) :=
  (rfl)

/-- A bet `exp g` with mean at most one under `P` pays at least the mean `∫ g ∂Q` against `P`:
the logarithm of its mean under `P` is nonpositive. -/
lemma integral_le_betPayoff (Q : Measure Ω) {P : Measure Ω} {g : Ω → ℝ} (hg : AEMeasurable g P)
    (hgP : ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂P ≤ 1) :
    ∫ x, g x ∂Q ≤ betPayoff Q P g := by
  have hle : ∫ x, Real.exp (g x) ∂P ≤ 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun x ↦ (Real.exp_pos _).le)
      (Real.measurable_exp.comp_aemeasurable hg).aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hgP).trans_eq ENNReal.toReal_one
  have hlog : Real.log (∫ x, Real.exp (g x) ∂P) ≤ 0 :=
    Real.log_nonpos (integral_nonneg fun x ↦ (Real.exp_pos _).le) hle
  rw [betPayoff_def]
  linarith

/-! ### The values of the game -/

/-- **The max–min value of the game is the largest e-power** [EVR26]. For a probability measure
`Q` and a null `T` of measures of mass at most one, the supremum over the bounded measurable
functions `g` of the infimum over the null of the payoff of the bet `exp g` is `maxEPower Q T`. -/
theorem iSup_iInf_betPayoff_eq_maxEPower (Q : Measure Ω) [IsProbabilityMeasure Q]
    (T : Set (Measure Ω)) (hT : ∀ P ∈ T, P Set.univ ≤ 1) :
    ⨆ (g : Ω → ℝ) (_ : Measurable g) (_ : ∃ C, ∀ x, |g x| ≤ C),
      ⨅ P ∈ T, (betPayoff Q P g : EReal) = maxEPower Q T := by
  refine le_antisymm (iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun ⟨C, hC⟩ ↦ ?_) ?_
  · -- a bounded bet whose payoff is above `c`, normalized, is an e-variable
    refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
    induction c using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hc not_top_lt
    | coe c =>
      have hgQ : Integrable g Q := LMLExplore.integrable_of_abs_le hg hC Q
      set a := ∫ x, g x ∂Q with ha
      set X : Ω → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (g x - a + c)) with hX_def
      have heq (x : Ω) : Real.exp (g x - a + c) = Real.exp (g x) * Real.exp (c - a) := by
        rw [← Real.exp_add]; ring_nf
      have hX : IsEVar X T := by
        refine ⟨by fun_prop, fun P hP ↦ ?_⟩
        have : IsFiniteMeasure P := ⟨(hT P hP).trans_lt ENNReal.one_lt_top⟩
        have hexp : Integrable (fun x ↦ Real.exp (g x)) P :=
          LMLExplore.integrable_exp_of_abs_le hg hC P
        rw [← ofReal_integral_eq_lintegral_ofReal (by simp_rw [heq]; exact hexp.mul_const _)
          (.of_forall fun x ↦ (Real.exp_pos _).le), ENNReal.ofReal_le_one]
        simp_rw [heq]
        rw [integral_mul_const]
        rcases (integral_nonneg fun x ↦ (Real.exp_pos (g x)).le : 0 ≤ ∫ x, Real.exp (g x) ∂P)
          |>.eq_or_lt with h0 | hpos
        · rw [← h0, zero_mul]
          exact zero_le_one
        -- the payoff against `P` is above `c`
        have hcP : (c : EReal) < betPayoff Q P g := hc.trans_le (iInf₂_le P hP)
        rw [EReal.coe_lt_coe_iff, betPayoff_def] at hcP
        have hlt : ∫ x, Real.exp (g x) ∂P < Real.exp (a - c) :=
          (Real.log_lt_iff_lt_exp hpos).1 (by linarith)
        calc (∫ x, Real.exp (g x) ∂P) * Real.exp (c - a)
        _ ≤ Real.exp (a - c) * Real.exp (c - a) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
      calc (c : EReal) = ∫ᵉ x, ((g x - a + c : ℝ) : EReal) ∂Q := by
            have h1 : Integrable (fun x ↦ g x - a) Q := hgQ.sub (integrable_const a)
            rw [eintegral_eq_integral (f := fun x ↦ g x - a + c) (h1.add (integrable_const c)),
              integral_add (f := fun x ↦ g x - a) (g := fun _ ↦ c) h1 (integrable_const c),
              integral_sub (f := g) (g := fun _ ↦ a) hgQ (integrable_const a)]
            simp [← ha]
      _ = ∫ᵉ x, ENNReal.log (X x) ∂Q := by
            refine eintegral_congr_ae (.of_forall fun x ↦ ?_)
            simp [hX_def, ENNReal.log_ofReal_of_pos (Real.exp_pos _)]
      _ ≤ maxEPower Q T := hX.eintegral_log_le_maxEPower Q
  · -- the expected logarithm of an e-variable is approached by bounded bets
    refine le_of_forall_lt_imp_le_of_dense fun c hc ↦ ?_
    induction c using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd hc not_top_lt
    | coe c =>
      obtain ⟨E, hE, hcE⟩ := lt_maxEPower_iff.1 hc
      obtain ⟨N, f, hfm, hfN, hfP, hcf⟩ :=
        hE.exists_bounded_lt_integral_of_lt_eintegral_log Q hT hcE
      refine le_iSup_of_le f (le_iSup_of_le hfm (le_iSup_of_le ⟨N, hfN⟩
        (le_iInf₂ fun P hP ↦ ?_)))
      -- `exp f` has mean at most one under `P`, so the payoff is at least `∫ f ∂Q`
      exact EReal.coe_le_coe_iff.2 (hcf.le.trans (integral_le_betPayoff Q hfm.aemeasurable
        (hfP P hP)))

/-- **The min–max value of the game is the smallest relative entropy** [EVR26]. For a probability
measure `Q` and a null `T` of probability measures, the infimum over the null of the supremum over
the bounded measurable functions `g` of the payoff of the bet `exp g` is `klInf Q T`: for each
member `P`, the supremum is `klDiv Q P` by the Donsker–Varadhan formula. -/
theorem iInf_iSup_betPayoff_eq_klInf (Q : Measure Ω) [IsProbabilityMeasure Q]
    (T : Set (Measure Ω)) (hT : ∀ P ∈ T, IsProbabilityMeasure P) :
    ⨅ P ∈ T, ⨆ (g : Ω → ℝ) (_ : Measurable g) (_ : ∃ C, ∀ x, |g x| ≤ C),
      (betPayoff Q P g : EReal) = klInf Q T := by
  -- for one member of the null, the Donsker–Varadhan formula
  have key (P : Measure Ω) (hP : P ∈ T) :
      (⨆ (g : Ω → ℝ) (_ : Measurable g) (_ : ∃ C, ∀ x, |g x| ≤ C),
        (betPayoff Q P g : EReal)) = (klDiv Q P : EReal) := by
    have := hT P hP
    rw [TauCeti.klDiv_eq_iSup_integral_sub_log_integral_exp]
    set X := ⨆ (g : Ω → ℝ) (_ : Measurable g) (_ : ∃ C, ∀ x, |g x| ≤ C),
      (betPayoff Q P g : EReal)
    -- the bet `1` pays `0`
    have hX0 : 0 ≤ X := by
      refine le_iSup_of_le (fun _ ↦ 0) (le_iSup_of_le measurable_const
        (le_iSup_of_le ⟨0, fun _ ↦ by simp⟩ ?_))
      simp [betPayoff_def]
    refine le_antisymm (iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hC ↦ ?_) ?_
    · refine le_trans ?_ (EReal.coe_ennreal_le_coe_ennreal_iff.2
        (le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hC le_rfl))))
      rw [EReal.coe_ennreal_ofReal, betPayoff_def]
      exact EReal.coe_le_coe_iff.2 (le_max_left _ _)
    · rw [← EReal.coe_toENNReal hX0, EReal.coe_ennreal_le_coe_ennreal_iff]
      refine iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hC ↦ ?_
      rw [← EReal.coe_ennreal_le_coe_ennreal_iff, EReal.coe_toENNReal hX0,
        EReal.coe_ennreal_ofReal]
      have hle : (betPayoff Q P g : EReal) ≤ X :=
        le_iSup_of_le g (le_iSup_of_le hg (le_iSup_of_le hC le_rfl))
      rw [betPayoff_def] at hle
      rcases le_total (∫ x, g x ∂Q - Real.log (∫ x, Real.exp (g x) ∂P)) 0 with h | h
      · rw [max_eq_right h]
        simpa using hX0
      · rw [max_eq_left h]
        exact hle
  rw [biInf_congr key, klInf_eq_iInf_klDiv fun P hP ↦ by simp [(hT P hP).measure_univ]]

/-! ### Blocks of `n` observations -/

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}

/-- **The max–min value with `n` observations is `maxLogGrowth Q₁ S₁ n`** [EVR26]: the case
`T = sampleNull S₁ n`, `Q = Q₁ ^ n` of `iSup_iInf_betPayoff_eq_maxEPower`. -/
theorem iSup_iInf_betPayoff_sampleNull_eq_maxLogGrowth (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (S₁ : Set (Measure 𝓧)) (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (n : ℕ) :
    ⨆ (g : (Fin n → 𝓧) → ℝ) (_ : Measurable g) (_ : ∃ C, ∀ x, |g x| ≤ C),
      ⨅ μ ∈ sampleNull S₁ n, (betPayoff (Measure.pi fun _ : Fin n ↦ Q₁) μ g : EReal) =
        maxLogGrowth Q₁ S₁ n := by
  rw [maxLogGrowth_def]
  exact iSup_iInf_betPayoff_eq_maxEPower _ _ (measure_univ_le_one_of_mem_sampleNull hS₁ n)

/-- **The bipolar rate is the limit of the max–min values per observation** [EVR26]: the max–min
values of the games with `n` observations, divided by `n`, tend to `bipolarRate Q₁ S₁`. -/
theorem tendsto_iSup_iInf_betPayoff_sampleNull_div_bipolarRate (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (S₁ : Set (Measure 𝓧)) (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) :
    Tendsto (fun n : ℕ ↦ (⨆ (g : (Fin n → 𝓧) → ℝ) (_ : Measurable g) (_ : ∃ C, ∀ x, |g x| ≤ C),
      ⨅ μ ∈ sampleNull S₁ n, (betPayoff (Measure.pi fun _ : Fin n ↦ Q₁) μ g : EReal)) / n)
      atTop (𝓝 (bipolarRate Q₁ S₁)) :=
  (tendsto_maxLogGrowth_div_bipolarRate Q₁ hS₁).congr fun n ↦ by
    rw [iSup_iInf_betPayoff_sampleNull_eq_maxLogGrowth Q₁ S₁ hS₁ n]

/-- **The min–max value with `n` observations is `n * klInf Q₁ S₁`** [EVR26]: the case
`T = sampleNull S₁ n`, `Q = Q₁ ^ n` of `iInf_iSup_betPayoff_eq_klInf`, with the tensorization
`klInf_pi_sampleNull`. Divided by `n`, the min–max values are all `klInf Q₁ S₁`. -/
theorem iInf_iSup_betPayoff_sampleNull_eq_mul_klInf (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (S₁ : Set (Measure 𝓧)) (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) {n : ℕ} (hn : n ≠ 0) :
    ⨅ μ ∈ sampleNull S₁ n, ⨆ (g : (Fin n → 𝓧) → ℝ) (_ : Measurable g) (_ : ∃ C, ∀ x, |g x| ≤ C),
      (betPayoff (Measure.pi fun _ : Fin n ↦ Q₁) μ g : EReal) = n * klInf Q₁ S₁ := by
  rw [iInf_iSup_betPayoff_eq_klInf _ _ (isProbabilityMeasure_of_mem_sampleNull hS₁ n),
    klInf_pi_sampleNull Q₁ hS₁ hn]

end ProbabilityTheory
