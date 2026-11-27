/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.EValues.BipolarRate.Basic
public import LMLExplore.EValues.EProcess.LevelStoppingTime
public import LMLExplore.EValues.Null.Basic
public import Mathlib.Probability.ProductMeasure
import LMLExplore.Analysis.SpecialFunctions.Log.ENNRealLog
import LMLExplore.EValues.BipolarRate.StoppingTime
import LMLExplore.EValues.EProcess.ProductNumeraire
import LMLExplore.Probability.Independence.Wald
import LMLExplore.Probability.Process.LevelCrossing
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Probability.Independence.InfinitePi

/-!
# The expected number of observations of the test of the product of the numeraires

Let `S₁` be a set of measures of mass at most `1` on `𝓧` (the null) and `Q₁` a probability measure
on `𝓧` (the alternative). The observations are the coordinates of `ℕ → 𝓧`, with the i.i.d. law
`Q = Measure.infinitePi fun _ ↦ Q₁`. The numeraire `X* = numeraire Q₁ S₁` is the log-optimal
e-variable for `S₁` under `Q₁`, with expected logarithm `D = maxEPower Q₁ S₁`, and the product
`∏ k < n, X* (ω k)` of the numeraires is a test supermartingale for the sequential null of the
constant one-step null `S₁`
(`ProbabilityTheory.isTestSupermartingale_prod_numeraire_sequentialNull`).
Thresholding it at `α⁻¹` is a sequential test of level `α`
(`ProbabilityTheory.IsEProcess.isLevelStoppingTime_hittingAfter`).

This file computes its expected number of observations: if `D > 0`, the first time `τ α` at
which the product reaches `α⁻¹` satisfies `𝔼_Q[τ α] / log (1/α) → 1 / D` as `α → 0`, with
`1 / ∞ = 0` [ARR26, Theorem 4.1]. The numeraires of the observations are i.i.d. factors whose
logarithm has the mean `D`, and the limit is that of the expected time for a product of i.i.d.
factors to reach a level
(`ProbabilityTheory.iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log`), which comes
from the elementary renewal theorem for first passage times. No moment of `log X*` is assumed.

For a null `S₁` of probability measures, every sequential test of level `α` for the i.i.d. laws
of the members of `S₁` makes at least `log (1/α) / d` observations in expectation, with
`d = bipolarRate Q₁ S₁` (`ProbabilityTheory.toENNReal_log_inv_div_bipolarRate_le_lintegral`), and
`D ≤ d ≤ KL_inf(Q₁, S₁)`. When the rate `D` of the numeraires is the bipolar rate `d`, for
instance when `D = KL_inf(Q₁, S₁)`, as for a simple null, the test of the product of the
numeraires attains the lower bound to first order.

Without any hypothesis on the bipolar rate, the rate `D` still bounds the expected number of
observations of the sequential tests of level `α` for the larger independent null
`indepNull S₁`, the laws of independent observations with laws in `S₁`: they make at least
`log (1/α) / D` observations in expectation. The ratio of the e-process `α⁻¹ 𝟙{τ ≤ n}` to the
product of the numeraires has mean at most `1` at every bounded stopping time
(`ProbabilityTheory.lintegral_div_prod_le_one`), so `𝔼[𝟙{τ < ∞} α⁻¹ / ∏ j < τ, X* (ω j)] ≤ 1`;
pathwise,
`log (1/α) + ∑ j < τ, log⁻ X* (ω j) + 1 ≤ ∑ j < τ, log⁺ X* (ω j) + α⁻¹ / ∏ j < τ, X* (ω j)`,
which is `t + 1 ≤ exp t`, and Wald's identity in `ℝ≥0∞`
(`ProbabilityTheory.iIndepFun.lintegral_tsum_indicator_lt_eq_mul`) integrates the sums, whose
means are `𝔼[τ]` times those of `log⁺ X*` and `log⁻ X*`, of difference `D`
[EVR26, Note 32, Statement 1].

## Main statements

* `ProbabilityTheory.tendsto_lintegral_hittingAfter_prod_numeraire_div_log`: for `D > 0`,
  `𝔼_Q[τ α] / log (1/α) → 1 / D` as `α → 0`.
* `ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral`: if the bipolar rate is at
  most `D`, for instance if `KL_inf(Q₁, S₁) ≤ D`, every sequential test of level `α` makes at
  least `log (1/α) / D` observations in expectation.
* `ProbabilityTheory.IsLevelStoppingTime.lintegral_tsum_indicator_inv_div_prod_le_one`: a
  sequential test `τ` of level `α` for the independent null `indepNull S₁` has
  `𝔼[𝟙{τ < ∞} α⁻¹ / ∏ i < τ, X* (ω i)] ≤ 1`.
* `ProbabilityTheory.toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull`: with no
  hypothesis on the bipolar rate, every sequential test of level `α` for the independent null
  makes at least `log (1/α) / D` observations in expectation [EVR26, Note 32, Statement 1].

## Implementation notes

`toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull` is adapted from
`EValuesResearch/Results/ConvexPieces.lean` (commit `83205cb`) in the paper project
`RemyDegenne/evalues_research`, rewritten on the API of LMLExplore.

## References

* [ARR26] S. Agrawal, A. Ram and A. Ramdas, *On stopping times of power-one sequential tests:
  tight lower and upper bounds*, arXiv:2504.19952v2, Theorem 4.1.
* [EVR26] *Answers to open questions in e-values and anytime-valid inference*, notes 01 to 34 and
  the Lean library `EValuesResearch` of github.com/RemyDegenne/evalues_research, 2026; written and
  refereed by AI agents.
* [Gut09] A. Gut, *Stopped Random Walks: Limit Theorems and Applications*, 2nd edition, Springer,
  2009, Chapter 3.
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {S₁ : Set (Measure 𝓧)}

/-- **The expected number of observations of the test of the product of the numeraires**
[ARR26, Theorem 4.1]. Let `S₁` be a null of measures of mass at most `1`, `Q₁` a probability
measure, and `D = maxEPower Q₁ S₁ > 0` the expected logarithm of the numeraire
`X* = numeraire Q₁ S₁`. Under the i.i.d. law of `Q₁`, the first time `τ α` at which the product
`∏ k < n, X* (ω k)` reaches `α⁻¹` satisfies `𝔼[τ α] / log (1/α) → 1 / D` as `α → 0`. The rate
`D` may be `⊤`, where the limit is `0`. -/
theorem tendsto_lintegral_hittingAfter_prod_numeraire_div_log (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) (hpos : 0 < maxEPower Q₁ S₁) :
    Tendsto (fun α ↦ (∫⁻ ω, ENat.toENNReal (hittingAfter
        (fun n ω ↦ ∏ k ∈ Finset.range n, numeraire Q₁ S₁ (ω k)) (Set.Ici α⁻¹) 0 ω)
        ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁)) / (ENNReal.log α⁻¹).toENNReal) (𝓝[>] 0)
      (𝓝 (maxEPower Q₁ S₁).toENNReal⁻¹) := by
  have hXm := measurable_numeraire Q₁ S₁
  -- the expected logarithm of the numeraire of the first coordinate is the largest e-power
  have hD : ∫ᵉ ω, ENNReal.log (numeraire Q₁ S₁ (ω 0)) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) =
      maxEPower Q₁ S₁ := by
    rw [← eintegral_map hXm.ennreal_log (measurable_pi_apply 0),
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q₁) 0).map_eq,
      maxEPower_eq_eintegral_numeraire hS₁]
  -- the numeraires of the coordinates are i.i.d. under the i.i.d. law of `Q₁`
  have h := iIndepFun.tendsto_lintegral_hittingAfter_prod_div_log
    (X := fun k (ω : ℕ → 𝓧) ↦ numeraire Q₁ S₁ (ω k)) (iIndepFun_infinitePi fun _ ↦ hXm)
    (fun j ↦ hXm.comp (measurable_pi_apply j))
    (fun j ↦ (Measure.identDistrib_eval_infinitePi Q₁ j 0).comp hXm) (hD ▸ hpos)
  rwa [hD] at h

/-- **The lower bound on expected stopping times at the rate of the numeraire.** If the bipolar
rate of `Q₁` against a null `S₁` of probability measures is at most the expected logarithm
`D = maxEPower Q₁ S₁` of the numeraire, every sequential test of level `α` for the i.i.d. laws of
the members of `S₁` makes at least `log (1/α) / D` observations in expectation under the i.i.d.
law of `Q₁`. The hypothesis holds when `KL_inf(Q₁, S₁) ≤ D`, as for a simple null, since the
bipolar rate is at most `KL_inf(Q₁, S₁)` (`bipolarRate_le_klInf`). Then `D` is the bipolar rate,
and with `tendsto_lintegral_hittingAfter_prod_numeraire_div_log` the test of the product of the
numeraires attains this bound to first order as `α → 0`. -/
theorem toENNReal_log_inv_div_maxEPower_le_lintegral (Q₁ : Measure 𝓧) [IsProbabilityMeasure Q₁]
    (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (h : bipolarRate Q₁ S₁ ≤ maxEPower Q₁ S₁)
    {τ : (ℕ → 𝓧) → WithTop ℕ} {α : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ Filtration.piLT (iidNull S₁) α) :
    (ENNReal.log α⁻¹).toENNReal / (maxEPower Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  -- `D ≤ d ≤ D`
  have hd : bipolarRate Q₁ S₁ = maxEPower Q₁ S₁ :=
    le_antisymm h (maxLogGrowth_one Q₁ S₁ ▸ maxLogGrowth_one_le_bipolarRate Q₁ S₁)
  exact hd ▸ toENNReal_log_inv_div_bipolarRate_le_lintegral Q₁ hS₁ hτ

/-! ### The sequential tests of the independent null -/

/-- The negative part of the logarithm of a numeraire has mean at most `1`: it is at most
`1 / X - 1 ≤ 1 / X`, and `1 / X` has mean at most `1` since the constant `1` is an e-variable. -/
private lemma lintegral_toENNReal_neg_log_le_one_of_isNumeraire {Q₁ : Measure 𝓧}
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, P Set.univ ≤ 1) {X : 𝓧 → ℝ≥0∞}
    (hX : IsNumeraire X S₁ Q₁) :
    ∫⁻ x, (-ENNReal.log (X x)).toENNReal ∂Q₁ ≤ 1 := by
  refine (lintegral_mono fun x ↦ ?_).trans (hX.lintegral_div_le_one (isEVar_fun_one hS₁))
  rw [← ENNReal.log_inv, one_div]
  refine (EReal.toENNReal_le_toENNReal (ENNReal.log_le_sub_one _)).trans ?_
  rw [← EReal.coe_ennreal_one, EReal.coe_ennreal_sub_toENNReal]
  exact tsub_le_self

/-- **A sequential test against the product of the numeraires.** Let `S₁` be a nonempty set of
probability measures, `Q₁` a probability measure and `X` a numeraire of `S₁` under `Q₁`. A
sequential test `τ` of level `α` for the independent null `indepNull S₁`, in the filtration
`Filtration.piLT` of the past observations, has `𝔼[𝟙{τ < ∞} α⁻¹ / ∏ i < τ, X (ω i)] ≤ 1` under
the i.i.d. law of `Q₁`, written as a sum over the values `k` of `τ`: the ratio of the e-process
`α⁻¹ 𝟙{τ ≤ n}` to the product of the numeraires has mean at most `1` at every bounded stopping
time (`ProbabilityTheory.lintegral_div_prod_le_one`). -/
theorem IsLevelStoppingTime.lintegral_tsum_indicator_inv_div_prod_le_one (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P) (hS_ne : S₁.Nonempty)
    {X : 𝓧 → ℝ≥0∞} (hX : IsNumeraire X S₁ Q₁) {τ : (ℕ → 𝓧) → WithTop ℕ} {α : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ Filtration.piLT (indepNull S₁) α) :
    ∫⁻ ω, ∑' k : ℕ, {ω | τ ω = k}.indicator (fun ω ↦ α⁻¹ / ∏ i ∈ Finset.range k, X (ω i)) ω
      ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) ≤ 1 := by
  have hτs := hτ.isStoppingTime
  have hf_meas (k : ℕ) : Measurable ({ω | τ ω = k}.indicator
      fun ω ↦ α⁻¹ / ∏ i ∈ Finset.range k, X (ω i)) :=
    (measurable_const.div (Finset.measurable_prod _ fun i _ ↦
      hX.measurable.comp (measurable_pi_apply i))).indicator
      (Filtration.le _ k _ (by simpa using hτs.measurableSet_eq k))
  rw [lintegral_tsum fun k ↦ (hf_meas k).aemeasurable, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N ↦ ?_
  rw [← lintegral_finsetSum _ fun k _ ↦ hf_meas k]
  -- the sum up to `N` is the ratio at the bounded stopping time `min τ N`
  refine (lintegral_mono fun ω ↦ ?_).trans (lintegral_div_prod_le_one (S₁ := fun _ ↦ S₁)
    (Q₁ := fun _ ↦ Q₁) (X := fun _ ↦ X) (fun _ ↦ hS₁) (fun _ ↦ hS_ne) (fun _ ↦ hX)
    (fun _ hP ↦ infinitePi_mem_indepNull hP) hτ.isEProcess_inv_mul_indicator
    (hτs.min_const N) fun ω ↦ ((min_le_right _ _).trans_lt (WithTop.coe_lt_top N)).ne)
  by_cases hk : ∃ k < N, τ ω = k
  · obtain ⟨k, hkN, hτk⟩ := hk
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hkN) fun j _ hjk ↦ by
      simp [hτk, Ne.symm hjk]]
    have hkN' : min (k : WithTop ℕ) (WithTop.some N) = WithTop.some k := by
      rw [Nat.cast_withTop]; exact min_eq_left (WithTop.coe_le_coe.2 hkN.le)
    simp only [stoppedValue, Set.indicator_of_mem (show ω ∈ {ω | τ ω = k} from hτk), hτk]
    rw [hkN']
    simp [hτk]
  · push Not at hk
    rw [Finset.sum_eq_zero fun j hj ↦ by simp [hk j (Finset.mem_range.1 hj)]]
    exact zero_le

/-- At level `0`, the bound of `IsLevelStoppingTime.lintegral_tsum_indicator_inv_div_prod_le_one`
forbids an almost surely finite stopping time when the factors are almost surely finite: the sum
is then almost surely `⊤`. -/
private lemma ne_zero_of_lintegral_tsum_indicator_inv_div_prod_le_one {μ : Measure (ℕ → 𝓧)}
    [IsProbabilityMeasure μ] {τ : (ℕ → 𝓧) → WithTop ℕ} {X : 𝓧 → ℝ≥0∞} {α : ℝ≥0∞}
    (h : ∫⁻ ω, ∑' k : ℕ, {ω | τ ω = k}.indicator
      (fun ω ↦ α⁻¹ / ∏ i ∈ Finset.range k, X (ω i)) ω ∂μ ≤ 1)
    (hτ : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) (hX : ∀ᵐ ω ∂μ, ∀ i, X (ω i) ≠ ⊤) : α ≠ 0 := by
  rintro rfl
  have htop : ∀ᵐ ω ∂μ, ∑' k : ℕ, {ω | τ ω = k}.indicator
      (fun ω ↦ 0⁻¹ / ∏ i ∈ Finset.range k, X (ω i)) ω = ⊤ := by
    filter_upwards [hτ, hX] with ω hτω hXω
    obtain ⟨k, hk2⟩ := ENat.ne_top_iff_exists.mp hτω
    have hk : τ ω = (k : WithTop ℕ) := hk2.symm
    rw [tsum_eq_single k fun j hj ↦ by simp [hk, Ne.symm hj]]
    simp only [Set.indicator_of_mem (show ω ∈ {ω | τ ω = k} from hk), ENNReal.inv_zero]
    exact ENNReal.top_div_of_ne_top (ENNReal.prod_ne_top fun i _ ↦ hXω i)
  rw [lintegral_congr_ae htop, lintegral_const, measure_univ, mul_one] at h
  exact absurd h (by simp)

/-- **Sequential tests of the independent null need `log (1/α) / a₁` observations.** Let `S₁` be
a set of probability measures and `Q₁` a probability measure on `𝓧`. Every sequential test `τ` of
level `α` for the independent null `indepNull S₁`, in the filtration `Filtration.piLT` of the past
observations, makes at least `log (1/α) / a₁` observations in expectation under the i.i.d. law of
`Q₁`, where `a₁ = maxEPower Q₁ S₁` is the largest expected logarithm under `Q₁` of an e-variable
for `S₁`. The left side is in `ℝ≥0∞`, with `log (1/α)` replaced by `0` for `α ≥ 1`; if `a₁ = 0`
and `α < 1`, the expected number of observations is infinite.

Pathwise, for the numeraire `X* = numeraire Q₁ S₁`,
`log (1/α) + ∑ j < τ, log⁻ X* (ω j) + 1 ≤ ∑ j < τ, log⁺ X* (ω j) + α⁻¹ / ∏ j < τ, X* (ω j)`
(`ENNReal.ofReal_add_sum_add_one_le_sum_add_div_prod`); the last term has mean at most `1`
(`IsLevelStoppingTime.lintegral_tsum_indicator_inv_div_prod_le_one`), and Wald's identity in
`ℝ≥0∞` (`ProbabilityTheory.iIndepFun.lintegral_tsum_indicator_lt_eq_mul`) integrates the sums,
whose means are `𝔼[τ]` times those of `log⁺ X*` and `log⁻ X*`, of difference `a₁`. -/
theorem toENNReal_log_inv_div_maxEPower_le_lintegral_of_indepNull (Q₁ : Measure 𝓧)
    [IsProbabilityMeasure Q₁] (hS₁ : ∀ P ∈ S₁, IsProbabilityMeasure P)
    {τ : (ℕ → 𝓧) → WithTop ℕ} {α : ℝ≥0∞}
    (hτ : IsLevelStoppingTime τ Filtration.piLT (indepNull S₁) α) :
    (ENNReal.log α⁻¹).toENNReal / (maxEPower Q₁ S₁).toENNReal ≤
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂Measure.infinitePi (fun _ : ℕ ↦ Q₁) := by
  set Q := Measure.infinitePi (fun _ : ℕ ↦ Q₁)
  set T := ∫⁻ ω, ENat.toENNReal (τ ω) ∂Q with hT_def
  -- the trivial cases
  rcases eq_or_ne T ⊤ with hT | hT
  · rw [hT]; exact le_top
  rcases le_or_gt 1 α with hα1 | hα1
  · have : (ENNReal.log α⁻¹).toENNReal = 0 :=
      EReal.toENNReal_eq_zero_iff.2 (ENNReal.log_le_zero_iff.2 (ENNReal.inv_le_one.2 hα1))
    rw [this, ENNReal.zero_div]; exact zero_le
  rcases eq_or_ne (maxEPower Q₁ S₁) ⊤ with ha | ha
  · rw [ha, EReal.toENNReal_top, ENNReal.div_top]; exact zero_le
  -- the null is nonempty; the numeraire `X` of `S₁` against `Q₁`
  have hS_ne : S₁.Nonempty := by
    rw [← Set.ne_empty_iff_nonempty]; rintro rfl; exact ha maxEPower_empty
  have hS₁le : ∀ P ∈ S₁, P Set.univ ≤ 1 := fun P hP ↦ (hS₁ P hP).measure_univ.le
  set X := numeraire Q₁ S₁
  have hX : IsNumeraire X S₁ Q₁ := isNumeraire_numeraire Q₁ hS₁le
  have hXm : Measurable X := hX.measurable
  -- the positive and negative parts of the expected logarithm of the numeraire
  set gp : 𝓧 → ℝ≥0∞ := fun x ↦ (ENNReal.log (X x)).toENNReal
  set gm : 𝓧 → ℝ≥0∞ := fun x ↦ (-ENNReal.log (X x)).toENNReal
  have hgp : Measurable gp := hXm.ennreal_log.ereal_toENNReal
  have hgm : Measurable gm := hXm.ennreal_log.neg.ereal_toENNReal
  have hmm_top : ∫⁻ x, gm x ∂Q₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (lintegral_toENNReal_neg_log_le_one_of_isNumeraire hS₁le hX)
  -- `a₁` is the extended integral of `log X`, the difference of these two integrals
  have ha_eq : maxEPower Q₁ S₁ = ((∫⁻ x, gp x ∂Q₁ : ℝ≥0∞) : EReal) - ∫⁻ x, gm x ∂Q₁ := by
    rw [maxEPower_eq_eintegral_numeraire hS₁le, eintegral]
  have hmp_top : ∫⁻ x, gp x ∂Q₁ ≠ ⊤ := by
    rintro h
    rw [ha_eq, h, ← EReal.coe_ennreal_toReal hmm_top] at ha
    exact ha (EReal.top_sub_coe _)
  have hXtop : ∀ᵐ x ∂Q₁, X x ≠ ⊤ := by
    filter_upwards [ae_lt_top' hgp.aemeasurable hmp_top] with x hx h
    simp [gp, h] at hx
  -- the key bound: `∫ 𝟙{τ < ∞} α⁻¹ / ∏ i < τ, X (ω i) ≤ 1`
  set f : ℕ → (ℕ → 𝓧) → ℝ≥0∞ := fun k ↦
    {ω | τ ω = k}.indicator fun ω ↦ α⁻¹ / ∏ i ∈ Finset.range k, X (ω i) with hf
  have hkey : ∫⁻ ω, ∑' k, f k ω ∂Q ≤ 1 :=
    hτ.lintegral_tsum_indicator_inv_div_prod_le_one Q₁ hS₁ hS_ne hX
  -- almost surely, the test stops and the numeraires of the observations are positive and finite
  have hτs := hτ.isStoppingTime
  have hτm : Measurable fun ω ↦ ENat.toENNReal (τ ω) :=
    (measurable_of_countable _).comp hτs.measurable'
  have hτ_ae : ∀ᵐ ω ∂Q, τ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top hτm hT] with ω hω h
    exact hω.ne (by rw [h]; exact ENat.toENNReal_top)
  have hX0 : ∀ᵐ ω ∂Q, ∀ i, X (ω i) ≠ 0 :=
    Measure.ae_forall_apply_infinitePi _ fun _ ↦ hX.ae_ne_zero hS₁le
  have hXt : ∀ᵐ ω ∂Q, ∀ i, X (ω i) ≠ ⊤ :=
    Measure.ae_forall_apply_infinitePi _ fun _ ↦ hXtop
  -- the level is positive, and `log (1/α)` is a nonnegative real number
  have hα0 : α ≠ 0 := ne_zero_of_lintegral_tsum_indicator_inv_div_prod_le_one hkey hτ_ae hXt
  set c := Real.log (α⁻¹).toReal with hc_def
  have hαinv0 : α⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (hα1.trans ENNReal.one_lt_top).ne
  have hαinvt : α⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hα0
  have hc0 : 0 ≤ c := Real.log_nonneg (by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hαinvt (ENNReal.one_le_inv.2 hα1.le))
  have hexp : ENNReal.ofReal (Real.exp c) = α⁻¹ := by
    rw [hc_def, Real.exp_log (ENNReal.toReal_pos hαinv0 hαinvt), ENNReal.ofReal_toReal hαinvt]
  have hlogc : (ENNReal.log α⁻¹).toENNReal = ENNReal.ofReal c := by
    rw [ENNReal.log_pos_real hαinv0 hαinvt, EReal.real_coe_toENNReal]
  -- Wald's identity for the coordinates
  have hind : iIndepFun (fun j (ω : ℕ → 𝓧) ↦ ω j) Q :=
    iIndepFun_infinitePi (P := fun _ ↦ Q₁) (X := fun _ ↦ id) fun _ ↦ measurable_id
  have hτ' : IsStoppingTime (Filtration.naturalLT (fun j (ω : ℕ → 𝓧) ↦ ω j)
      measurable_pi_apply) τ := by
    rw [← Filtration.piLT_eq_naturalLT]; exact hτs
  have hWald {g : 𝓧 → ℝ≥0∞} (hg : Measurable g) :
      ∫⁻ ω, ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (ω j)) ω ∂Q =
        (∫⁻ x, g x ∂Q₁) * T :=
    hind.lintegral_tsum_indicator_lt_eq_mul measurable_pi_apply hτ' hg fun j ↦
      (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ Q₁) j).lintegral_comp hg
  have hsum_meas {g : 𝓧 → ℝ≥0∞} (hg : Measurable g) :
      Measurable fun ω ↦ ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (ω j)) ω :=
    Measurable.tsum fun j ↦ (hg.comp (measurable_pi_apply j)).indicator
      (hτs.measurable' measurableSet_Ioi)
  -- the pathwise bound `log (1/α) + ∑ j < τ, log⁻ X + 1 ≤ ∑ j < τ, log⁺ X + α⁻¹ / ∏ j < τ, X`
  have hpt : ∀ᵐ ω ∂Q, ENNReal.ofReal c +
      ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ gm (ω j)) ω + 1 ≤
      ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ gp (ω j)) ω + ∑' k, f k ω := by
    filter_upwards [hτ_ae, hX0] with ω hτω hXω
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hτω
    have hsum (g : 𝓧 → ℝ≥0∞) :
        ∑' j : ℕ, {ω | (j : ℕ∞) < τ ω}.indicator (fun ω ↦ g (ω j)) ω =
          ∑ j ∈ Finset.range k, g (ω j) := by
      rw [tsum_eq_sum (s := Finset.range k) fun j hj ↦ ?_]
      · refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [Set.indicator_of_mem]
        simp [← hk, Finset.mem_range.1 hj]
      · rw [Set.indicator_of_notMem]
        simpa [← hk] using hj
    have hf_sum : ∑' j, f j ω = α⁻¹ / ∏ i ∈ Finset.range k, X (ω i) := by
      have hk1 : τ ω = (k : WithTop ℕ) := hk.symm
      rw [tsum_eq_single k fun j hj ↦ by simp [f, hk1, Ne.symm hj]]
      simp [f, hk1]
    rw [hsum, hsum, hf_sum, ← hexp]
    exact ENNReal.ofReal_add_sum_add_one_le_sum_add_div_prod (fun j _ ↦ hXω j) hc0
  -- integrate, with Wald's identity and the key bound
  have hint := lintegral_mono_ae hpt
  rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
    lintegral_const, measure_univ, mul_one, hWald hgm, lintegral_const, measure_univ, mul_one,
    lintegral_add_left (hsum_meas hgp), hWald hgp] at hint
  have h1 : ENNReal.ofReal c + (∫⁻ x, gm x ∂Q₁) * T ≤ (∫⁻ x, gp x ∂Q₁) * T :=
    (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).1 (hint.trans (by gcongr))
  have h2 : ENNReal.ofReal c ≤ (∫⁻ x, gp x ∂Q₁ - ∫⁻ x, gm x ∂Q₁) * T := by
    rw [ENNReal.sub_mul fun _ _ ↦ hT]
    exact ENNReal.le_sub_of_add_le_left (ENNReal.mul_ne_top hmm_top hT) (by rwa [add_comm])
  rw [hlogc, ha_eq, EReal.coe_ennreal_sub_toENNReal]
  exact ENNReal.div_le_of_le_mul (by rwa [mul_comm])

end ProbabilityTheory
