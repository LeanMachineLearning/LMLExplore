/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.MeasureTheory.Measure.Weighted
public import LMLExplore.OnlineLearning.KrichevskyTrofimov
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ConditionalProbability
import LMLExplore.Analysis.Normed.Group.Basic
import LMLExplore.InformationTheory.KullbackLeibler.Cond
import LMLExplore.InformationTheory.KullbackLeibler.Finite
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# Learning with expert advice through coin betting

The reduction of [Ora, §13.6] turns any coin-betting algorithm into an algorithm for prediction
with expert advice. The experts form a measurable space `Θ` with a prior probability measure `μ`,
and the losses `g t : Θ → ℝ` of the rounds are measurable with values in `[-L, L]`. Each expert
`θ` has its own bettor, from the initial wealth `1`, which bets `x t θ` at round `t`.

* The prediction `bettingMixture μ (x t)` of round `t` [Ora, (13.4)] is the prior weighted by the
  positive parts `max (x t θ) 0` of the bets and normalized, or the prior itself when no bet is
  positive. Its loss is the mean `∫ g t ∂(bettingMixture μ (x t))` of the losses of the experts.
* The bettor of the expert `θ` then receives the coin `bettingCoin μ L (g t) (x t) θ`
  [Ora, (13.5)]: `(m - g t θ) / (2 L)` if its bet is positive and `max (m - g t θ) 0 / (2 L)`
  otherwise, where `m` is the loss of the prediction. The coins lie in `[-1, 1]`.

The coins are chosen so that the bettors win nothing on average: the gain `∫ c x dμ` of each round
is nonpositive (`integral_bettingCoin_mul_nonpos`), so the mean wealth of the bettors after `n`
rounds is at most `1` (`integral_wealth_bettingCoin_le_one`). The coins also dominate the
instantaneous regret: `m - g t θ ≤ 2 L c t θ`. If every bettor guarantees the wealth
`exp (f (∑ t < n, c t θ))`, the Donsker–Varadhan inequality (Tau Ceti's
`TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`) bounds the mean under every probability
measure `Q` of `f (∑ t < n, c t θ)` by the relative entropy `KL(Q, μ)`. This gives **the regret
bound for experts** [Ora, Theorem 13.14] (`regret_bettingMixture_le`): for every concave
nondecreasing `h` with `y ≤ h (f y)`,
`∑ t < n, (∫ g t ∂(bettingMixture μ (x t)) - ∫ g t ∂Q) ≤ 2 L h (KL(Q, μ))`.

[Ora] asks `h` to be concave on `ℝ`, which its own Krichevsky–Trofimov instance violates. Here `h`
is concave, continuous and nondecreasing on a half-line `[a, ∞)` containing the values of `f`.
Concavity on `[0, ∞)` alone does not make the argument work: for `μ = Q` uniform on two experts
and `h = max · 0`, the values `-M` and `log 2 - δ` of `f` at the sums `0` and `log 2 - δ` of the
coins satisfy `y ≤ h (f y)` and keep the mean of `exp ∘ f` below `1` for `M` large, but the mean
`(log 2 - δ) / 2` of the sums exceeds `h 0 = 0`.

## Main definitions

* `LMLExplore.OnlineLearning.bettingMixture μ x`: the prediction of the reduction from the bets
  `x` of the experts [Ora, (13.4)].
* `LMLExplore.OnlineLearning.bettingCoin μ L g x`: the coins of the experts for the losses `g` and
  the bets `x` [Ora, (13.5)].
* `LMLExplore.OnlineLearning.OnlineLearner.bettingExperts μ L B`: the reduction as an online
  learner, from a bettor `B` [Ora, Algorithm 13.4 for the Krichevsky–Trofimov bettor].

## Main statements

* `integral_bettingCoin_mul_nonpos`, `integral_wealth_bettingCoin_le_one`: the bettors win nothing
  on average.
* `regret_bettingMixture_le`: the regret bound for experts [Ora, Theorem 13.14], for every
  probability measure `Q` with `KL(Q, μ) < ∞`, and `regret_bettingMixture_le_of_toReal_klDiv_le`
  with any upper bound of the relative entropy.
* `regret_bettingMixture_weightedMeasure_le`: the case of finitely many experts, with the relative
  entropy `∑ i, u i log (u i / w i)` of probability vectors.
* `sum_integral_bettingMixture_le_of_forall_mem`: the **quantile bound** [Ora, Remark 13.13]: if
  every expert of a measurable set `A` of experts has cumulative loss at most `G`, then the
  cumulative loss of the predictions is at most `G + 2 L h (log (1 / μ A))`.
* `OnlineLearner.hasRegretBound_bettingExperts`: the regret guarantee of the learner, from the
  wealth guarantee of the bettor.
* `OnlineLearner.hasRegretBound_bettingExperts_krichevskyTrofimov`: with Krichevsky–Trofimov
  bettors, the regret is at most `2 L √(2 n (KL(Q, μ) + log n / 2 + 1))` [Ora, §13.6].

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Chapter 13.
* F. Orabona and D. Pál, *Coin betting and parameter-free online learning*, NeurIPS 2016.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Finset Real Set
open scoped ENNReal

namespace LMLExplore.OnlineLearning

variable {Θ : Type*} [MeasurableSpace Θ] {μ : Measure Θ}

section Mixture

/-- The **prediction of the experts-through-betting reduction** [Ora, (13.4)] from the bets `x θ`
of the experts: the prior `μ` weighted by the positive parts `max (x θ) 0` of the bets and
normalized, or the prior itself when the positive parts have integral `0`. -/
noncomputable def bettingMixture (μ : Measure Θ) (x : Θ → ℝ) : Measure Θ :=
  if ∫ θ, max (x θ) 0 ∂μ = 0 then μ
  else μ.withDensity fun θ ↦ ENNReal.ofReal (max (x θ) 0 / ∫ θ, max (x θ) 0 ∂μ)

lemma bettingMixture_def (μ : Measure Θ) (x : Θ → ℝ) :
    bettingMixture μ x = if ∫ θ, max (x θ) 0 ∂μ = 0 then μ
      else μ.withDensity fun θ ↦ ENNReal.ofReal (max (x θ) 0 / ∫ θ, max (x θ) 0 ∂μ) := (rfl)

lemma bettingMixture_of_integral_eq_zero {x : Θ → ℝ} (h : ∫ θ, max (x θ) 0 ∂μ = 0) :
    bettingMixture μ x = μ := by
  simp [bettingMixture_def, h]

lemma bettingMixture_of_integral_ne_zero {x : Θ → ℝ} (h : ∫ θ, max (x θ) 0 ∂μ ≠ 0) :
    bettingMixture μ x =
      μ.withDensity fun θ ↦ ENNReal.ofReal (max (x θ) 0 / ∫ θ, max (x θ) 0 ∂μ) := by
  simp [bettingMixture_def, h]

/-- The prediction of the reduction is a probability measure. -/
instance isProbabilityMeasure_bettingMixture [IsProbabilityMeasure μ] (x : Θ → ℝ) :
    IsProbabilityMeasure (bettingMixture μ x) := by
  by_cases h : ∫ θ, max (x θ) 0 ∂μ = 0
  · rw [bettingMixture_of_integral_eq_zero h]
    infer_instance
  rw [bettingMixture_of_integral_ne_zero h]
  have hZ : 0 < ∫ θ, max (x θ) 0 ∂μ :=
    (integral_nonneg fun θ ↦ le_max_right (x θ) 0).lt_of_ne' h
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal ((Integrable.of_integral_ne_zero h).div_const _)
      (Filter.Eventually.of_forall fun θ ↦ div_nonneg (le_max_right (x θ) 0) hZ.le),
    integral_div, div_self h, ENNReal.ofReal_one]

/-- **The loss of the prediction**: `(∫ max x 0 dμ) * ∫ g d(bettingMixture μ x)` is the integral
`∫ max x 0 * g dμ` of the losses weighted by the positive parts of the bets, for bets with
integrable positive parts and every function `g`. -/
lemma integral_mul_integral_bettingMixture {x : Θ → ℝ}
    (hx : Integrable (fun θ ↦ max (x θ) 0) μ) (g : Θ → ℝ) :
    (∫ θ, max (x θ) 0 ∂μ) * ∫ θ, g θ ∂bettingMixture μ x = ∫ θ, max (x θ) 0 * g θ ∂μ := by
  by_cases h : ∫ θ, max (x θ) 0 ∂μ = 0
  · rw [h, zero_mul]
    have h0 : (fun θ ↦ max (x θ) 0) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun θ ↦ le_max_right (x θ) 0) hx).1 h
    rw [integral_congr_ae (g := fun _ ↦ (0 : ℝ)) (h0.mono fun θ hθ ↦ by simp [hθ]),
      integral_zero]
  have hZ : 0 < ∫ θ, max (x θ) 0 ∂μ :=
    (integral_nonneg fun θ ↦ le_max_right (x θ) 0).lt_of_ne' h
  rw [bettingMixture_of_integral_ne_zero h, integral_withDensity_eq_integral_toReal_smul₀
    (hx.aemeasurable.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall fun θ ↦ ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ ↦ ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (le_max_right (x θ) 0) hZ.le)]
  field_simp

end Mixture

section Coin

variable {L : ℝ} {g x : Θ → ℝ}

/-- The **coins of the experts** in the experts-through-betting reduction [Ora, (13.5)], for the
losses `g` and the bets `x` of a round: with `m = ∫ g d(bettingMixture μ x)` the loss of the
prediction, the coin of the expert `θ` is `(m - g θ) / (2 L)` if its bet is positive, and
`max (m - g θ) 0 / (2 L)` otherwise. -/
noncomputable def bettingCoin (μ : Measure Θ) (L : ℝ) (g x : Θ → ℝ) (θ : Θ) : ℝ :=
  if 0 < x θ then (∫ θ', g θ' ∂bettingMixture μ x - g θ) / (2 * L)
  else max (∫ θ', g θ' ∂bettingMixture μ x - g θ) 0 / (2 * L)

lemma bettingCoin_def (μ : Measure Θ) (L : ℝ) (g x : Θ → ℝ) (θ : Θ) :
    bettingCoin μ L g x θ = if 0 < x θ then (∫ θ', g θ' ∂bettingMixture μ x - g θ) / (2 * L)
      else max (∫ θ', g θ' ∂bettingMixture μ x - g θ) 0 / (2 * L) := (rfl)

/-- The coins dominate the instantaneous regret against each expert:
`∫ g d(bettingMixture μ x) - g θ ≤ 2 L * bettingCoin μ L g x θ`. -/
lemma sub_le_two_mul_bettingCoin (hL : 0 < L) (θ : Θ) :
    ∫ θ', g θ' ∂bettingMixture μ x - g θ ≤ 2 * L * bettingCoin μ L g x θ := by
  rw [bettingCoin_def]
  split_ifs
  · rw [mul_div_cancel₀ _ (by positivity)]
  · rw [mul_div_cancel₀ _ (by positivity)]
    exact le_max_left _ _

/-- The gain of the bettor of an expert is at most its share of the instantaneous regret:
`bettingCoin μ L g x θ * x θ ≤ max (x θ) 0 * ((m - g θ) / (2 L))`. -/
lemma bettingCoin_mul_le (hL : 0 < L) (θ : Θ) :
    bettingCoin μ L g x θ * x θ ≤
      max (x θ) 0 * ((∫ θ', g θ' ∂bettingMixture μ x - g θ) / (2 * L)) := by
  rw [bettingCoin_def]
  split_ifs with hx
  · rw [max_eq_left hx.le, mul_comm]
  · rw [max_eq_right (not_lt.1 hx), zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 hx)

/-- For measurable losses and bets, the coins are measurable. -/
lemma measurable_bettingCoin (hg : Measurable g) (hx : Measurable x) :
    Measurable (bettingCoin μ L g x) := by
  simp_rw [funext (bettingCoin_def μ L g x)]
  exact Measurable.ite (measurableSet_lt measurable_const hx)
    ((measurable_const.sub hg).div_const _)
    (((measurable_const.sub hg).max measurable_const).div_const _)

variable [IsProbabilityMeasure μ]

/-- For losses in `[-L, L]`, the coins lie in `[-1, 1]`. -/
lemma abs_bettingCoin_le_one (hL : 0 < L) (hg : ∀ θ, |g θ| ≤ L) (θ : Θ) :
    |bettingCoin μ L g x θ| ≤ 1 := by
  have hm : |∫ θ', g θ' ∂bettingMixture μ x| ≤ L := by
    simpa using norm_integral_le_of_norm_le_const (μ := bettingMixture μ x)
      (Filter.Eventually.of_forall fun θ' ↦ (Real.norm_eq_abs (g θ')).trans_le (hg θ'))
  have hd : |∫ θ', g θ' ∂bettingMixture μ x - g θ| ≤ 2 * L :=
    (abs_sub _ _).trans (by linarith [hg θ])
  rw [bettingCoin_def]
  split_ifs
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * L), div_le_one (by positivity)]
    exact hd
  · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * L), div_le_one (by positivity),
      abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans hd) (by positivity)


/-- **The bettors win nothing on average** [Ora, proof of Theorem 13.14]: for losses in `[-L, L]`
and integrable bets, the mean gain `∫ bettingCoin μ L g x θ * x θ dμ` of a round is nonpositive.
The bettors with positive bets gain `0` on average by the choice of the prediction, and the others
gain a nonpositive amount at each expert. -/
theorem integral_bettingCoin_mul_nonpos (hL : 0 < L) (hg : Measurable g) (hgL : ∀ θ, |g θ| ≤ L)
    (hxm : Measurable x) (hx : Integrable x μ) :
    ∫ θ, bettingCoin μ L g x θ * x θ ∂μ ≤ 0 := by
  set m := ∫ θ', g θ' ∂bettingMixture μ x
  have hgb : ∀ᵐ θ ∂μ, ‖g θ‖ ≤ L := Filter.Eventually.of_forall fun θ ↦ hgL θ
  have hcx : Integrable (fun θ ↦ bettingCoin μ L g x θ * x θ) μ :=
    hx.bdd_mul (measurable_bettingCoin hg hxm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ ↦ abs_bettingCoin_le_one hL hgL θ)
  have hpos : Integrable (fun θ ↦ max (x θ) 0 * ((m - g θ) / (2 * L))) μ :=
    hx.pos_part.mul_bdd (((measurable_const.sub hg).div_const _).aestronglyMeasurable)
      (c := 2 * L / (2 * L)) (Filter.Eventually.of_forall fun θ ↦ by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * L)]
        refine div_le_div_of_nonneg_right ((abs_sub _ _).trans ?_) (by positivity)
        have hm : |m| ≤ L := by
          simpa using norm_integral_le_of_norm_le_const (μ := bettingMixture μ x)
            (Filter.Eventually.of_forall fun θ' ↦ (Real.norm_eq_abs (g θ')).trans_le (hgL θ'))
        linarith [hgL θ])
  have hzero : ∫ θ, max (x θ) 0 * ((m - g θ) / (2 * L)) ∂μ = 0 := by
    have e : (fun θ ↦ max (x θ) 0 * ((m - g θ) / (2 * L))) =
        fun θ ↦ (max (x θ) 0 * m - max (x θ) 0 * g θ) / (2 * L) := by
      ext θ
      ring
    have hm : (∫ θ, max (x θ) 0 ∂μ) * m = ∫ θ, max (x θ) 0 * g θ ∂μ :=
      integral_mul_integral_bettingMixture hx.pos_part g
    rw [e, integral_div, integral_sub (hx.pos_part.mul_const m)
      (hx.pos_part.mul_bdd hg.aestronglyMeasurable hgb), integral_mul_const, hm, sub_self,
      zero_div]
  exact (integral_mono hcx hpos fun θ ↦ bettingCoin_mul_le hL θ).trans_eq hzero

end Coin

section Regret

variable [IsProbabilityMeasure μ] {L : ℝ} {n : ℕ} {g x : ℕ → Θ → ℝ}

/-- The wealth after `n` rounds of the bettors of the experts, from the initial wealth `1`, is
integrable for integrable bets and losses in `[-L, L]`. -/
lemma integrable_wealth_bettingCoin (hL : 0 < L) (hg : ∀ t < n, Measurable (g t))
    (hgL : ∀ t < n, ∀ θ, |g t θ| ≤ L) (hxm : ∀ t < n, Measurable (x t))
    (hx : ∀ t < n, Integrable (x t) μ) :
    Integrable (fun θ ↦ wealth 1 (fun t ↦ bettingCoin μ L (g t) (x t) θ) (fun t ↦ x t θ) n) μ := by
  simp_rw [wealth_def]
  refine (integrable_const 1).add (integrable_finsetSum _ fun t ht ↦ ?_)
  have ht := mem_range.1 ht
  exact (hx t ht).bdd_mul (measurable_bettingCoin (hg t ht) (hxm t ht)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ ↦ abs_bettingCoin_le_one hL (hgL t ht) θ)

/-- **The mean wealth of the bettors is at most `1`** [Ora, (13.7)]: in the experts-through-betting
reduction with losses in `[-L, L]` and integrable bets, the mean under the prior of the wealth
after `n` rounds of the bettors of the experts, each from the initial wealth `1`, is at most `1`. -/
theorem integral_wealth_bettingCoin_le_one (hL : 0 < L) (hg : ∀ t < n, Measurable (g t))
    (hgL : ∀ t < n, ∀ θ, |g t θ| ≤ L) (hxm : ∀ t < n, Measurable (x t))
    (hx : ∀ t < n, Integrable (x t) μ) :
    ∫ θ, wealth 1 (fun t ↦ bettingCoin μ L (g t) (x t) θ) (fun t ↦ x t θ) n ∂μ ≤ 1 := by
  have hi (t : ℕ) (ht : t < n) : Integrable (fun θ ↦ bettingCoin μ L (g t) (x t) θ * x t θ) μ :=
    (hx t ht).bdd_mul (measurable_bettingCoin (hg t ht) (hxm t ht)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ ↦ abs_bettingCoin_le_one hL (hgL t ht) θ)
  simp_rw [wealth_def]
  rw [integral_add (integrable_const 1) (integrable_finsetSum _ fun t ht ↦ hi t (mem_range.1 ht)),
    integral_finsetSum _ fun t ht ↦ hi t (mem_range.1 ht)]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, add_le_iff_nonpos_right]
  exact sum_nonpos fun t ht ↦ integral_bettingCoin_mul_nonpos hL (hg t (mem_range.1 ht))
    (hgL t (mem_range.1 ht)) (hxm t (mem_range.1 ht)) (hx t (mem_range.1 ht))

/-- The regret of the predictions against a probability measure `Q` on the experts is at most
`2 L` times the mean under `Q` of the sum of the coins. -/
lemma regret_bettingMixture_le_two_mul_integral (hL : 0 < L) (hg : ∀ t < n, Measurable (g t))
    (hgL : ∀ t < n, ∀ θ, |g t θ| ≤ L) (hxm : ∀ t < n, Measurable (x t)) (Q : Measure Θ)
    [IsProbabilityMeasure Q] :
    regret (fun t p ↦ ∫ θ, g t θ ∂p) (fun t ↦ bettingMixture μ (x t)) Q n ≤
      2 * L * ∫ θ, ∑ t ∈ range n, bettingCoin μ L (g t) (x t) θ ∂Q := by
  have hci (t : ℕ) (ht : t < n) : Integrable (bettingCoin μ L (g t) (x t)) Q :=
    Integrable.of_bound (measurable_bettingCoin (hg t ht) (hxm t ht)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun θ ↦ abs_bettingCoin_le_one hL (hgL t ht) θ)
  rw [integral_finsetSum _ fun t ht ↦ hci t (mem_range.1 ht), mul_sum, regret_def]
  refine sum_le_sum fun t ht ↦ ?_
  have ht := mem_range.1 ht
  have hgi : Integrable (g t) Q := Integrable.of_bound (hg t ht).aestronglyMeasurable L
    (Filter.Eventually.of_forall fun θ ↦ hgL t ht θ)
  have e : ∫ θ, g t θ ∂bettingMixture μ (x t) - ∫ θ, g t θ ∂Q =
      ∫ θ, (∫ θ', g t θ' ∂bettingMixture μ (x t) - g t θ) ∂Q := by
    rw [integral_sub (integrable_const _) hgi]
    simp
  rw [e, ← integral_const_mul]
  exact integral_mono ((integrable_const _).sub hgi) ((hci t ht).const_mul _)
    fun θ ↦ sub_le_two_mul_bettingCoin hL θ

omit [IsProbabilityMeasure μ] in
/-- The step of Jensen's inequality in the regret bound for experts: for a measurable `S` with
`|S| ≤ n`, and `f` and `h` as in `regret_bettingMixture_le`, the mean of `S` under a probability
measure `Q` is at most `h` of the mean of the truncation `min (f ∘ S) (f n)`, a bounded
function with values in `[a, f n]` on which Jensen's inequality applies. -/
private lemma integral_le_map_integral_min {a : ℝ} {f h : ℝ → ℝ} {S : Θ → ℝ}
    (hSm : Measurable S) (hS : ∀ θ, |S θ| ≤ n) (hf : Measurable f)
    (hfa : ∀ y : ℝ, |y| ≤ n → a ≤ f y) (hfh : ∀ y : ℝ, |y| ≤ n → y ≤ h (f y))
    (hh : ConcaveOn ℝ (Ici a) h) (hhc : ContinuousOn h (Ici a)) (hhm : MonotoneOn h (Ici a))
    (Q : Measure Θ) [IsProbabilityMeasure Q] :
    ∫ θ, S θ ∂Q ≤ h (∫ θ, min (f (S θ)) (f n) ∂Q) := by
  have hn : |(n : ℝ)| ≤ n := by rw [Nat.abs_cast]
  set Z : Θ → ℝ := fun θ ↦ min (f (S θ)) (f n)
  have hZm : Measurable Z := (hf.comp hSm).min measurable_const
  have hZa (θ : Θ) : a ≤ Z θ := le_min (hfa _ (hS θ)) (hfa _ hn)
  have hZi : Integrable Z Q := Integrable.of_bound hZm.aestronglyMeasurable _
    (Filter.Eventually.of_forall fun θ ↦ abs_le_max_abs_abs (hZa θ) (min_le_right _ _))
  have hSZ (θ : Θ) : S θ ≤ h (Z θ) := by
    rcases le_total (f (S θ)) (f n) with hle | hle
    · rw [show Z θ = f (S θ) from min_eq_left hle]
      exact hfh _ (hS θ)
    · rw [show Z θ = f n from min_eq_right hle]
      exact (le_abs_self _).trans ((hS θ).trans (hfh _ hn))
  have hhZm : Measurable fun θ ↦ h (Z θ) := by
    have hcont : Continuous fun z ↦ h (max a z) :=
      hhc.comp_continuous (continuous_const.max continuous_id) fun z ↦ le_max_left a z
    convert hcont.measurable.comp hZm using 1
    funext θ
    simp [max_eq_right (hZa θ)]
  have hhZi : Integrable (h ∘ Z) Q :=
    Integrable.of_bound hhZm.aestronglyMeasurable (max |h a| |h (f n)|)
      (Filter.Eventually.of_forall fun θ ↦ abs_le_max_abs_abs
        (hhm (mem_Ici.2 le_rfl) (mem_Ici.2 (hZa θ)) (hZa θ))
        (hhm (mem_Ici.2 (hZa θ)) (mem_Ici.2 (hfa _ hn)) (min_le_right _ _)))
  exact (integral_mono (Integrable.of_bound hSm.aestronglyMeasurable n
    (Filter.Eventually.of_forall hS)) hhZi hSZ).trans
    (hh.le_map_integral hhc isClosed_Ici (Filter.Eventually.of_forall hZa) hZi hhZi)

/-- **The regret bound for experts** [Ora, Theorem 13.14], with an upper bound `K` of the relative
entropy. Let the bets `x t θ` of the experts be measurable and integrable, and the losses `g t` be
measurable with values in `[-L, L]`. Assume that each bettor, from the initial wealth `1`, has the
wealth `exp (f (∑ t < n, c t θ))` after `n` rounds on its coins `c t θ = bettingCoin …`, and let `h`
be concave, continuous and nondecreasing on `[a, ∞)` with `a ≤ f y` and `y ≤ h (f y)` for
`|y| ≤ n`. Then for every probability measure `Q` with `KL(Q, μ) ≤ K < ∞`, the regret of the
predictions against `Q` is at most `2 L h K`. -/
theorem regret_bettingMixture_le_of_toReal_klDiv_le {a K : ℝ} {f h : ℝ → ℝ} (hL : 0 < L)
    (hg : ∀ t < n, Measurable (g t)) (hgL : ∀ t < n, ∀ θ, |g t θ| ≤ L)
    (hxm : ∀ t < n, Measurable (x t)) (hx : ∀ t < n, Integrable (x t) μ)
    (hW : ∀ θ, exp (f (∑ t ∈ range n, bettingCoin μ L (g t) (x t) θ)) ≤
      wealth 1 (fun t ↦ bettingCoin μ L (g t) (x t) θ) (fun t ↦ x t θ) n)
    (hf : Measurable f) (hfa : ∀ y : ℝ, |y| ≤ n → a ≤ f y) (hfh : ∀ y : ℝ, |y| ≤ n → y ≤ h (f y))
    (hh : ConcaveOn ℝ (Ici a) h) (hhc : ContinuousOn h (Ici a)) (hhm : MonotoneOn h (Ici a))
    (Q : Measure Θ) [IsProbabilityMeasure Q] (hQ : klDiv Q μ ≠ ∞) (hK : (klDiv Q μ).toReal ≤ K) :
    regret (fun t p ↦ ∫ θ, g t θ ∂p) (fun t ↦ bettingMixture μ (x t)) Q n ≤ 2 * L * h K := by
  set S : Θ → ℝ := fun θ ↦ ∑ t ∈ range n, bettingCoin μ L (g t) (x t) θ
  have hSm : Measurable S := Finset.measurable_sum _ fun t ht ↦
    measurable_bettingCoin (hg t (mem_range.1 ht)) (hxm t (mem_range.1 ht))
  have hS (θ : Θ) : |S θ| ≤ n := by
    simpa using norm_sum_le_card_mul (range n) (L := 1) fun t ht ↦
      (Real.norm_eq_abs _).trans_le (abs_bettingCoin_le_one hL (hgL t (mem_range.1 ht)) θ)
  have hn : |(n : ℝ)| ≤ n := by rw [Nat.abs_cast]
  -- the truncation `Z` of `f ∘ S` at `f n` is bounded and measurable
  set Z : Θ → ℝ := fun θ ↦ min (f (S θ)) (f n)
  have hZm : Measurable Z := (hf.comp hSm).min measurable_const
  have hZa (θ : Θ) : a ≤ Z θ := le_min (hfa _ (hS θ)) (hfa _ hn)
  have hZi : Integrable Z Q := Integrable.of_bound hZm.aestronglyMeasurable _
    (Filter.Eventually.of_forall fun θ ↦ abs_le_max_abs_abs (hZa θ) (min_le_right _ _))
  -- the mean wealth bound and the Donsker–Varadhan inequality give `∫ Z dQ ≤ K`
  have hexpi : Integrable (fun θ ↦ exp (Z θ)) μ :=
    Integrable.of_bound (Real.measurable_exp.comp hZm).aestronglyMeasurable (exp (f n))
      (Filter.Eventually.of_forall fun θ ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.2 (min_le_right _ _))
  have hexp : ∫ θ, exp (Z θ) ∂μ ≤ 1 :=
    (integral_mono hexpi (integrable_wealth_bettingCoin hL hg hgL hxm hx) fun θ ↦
      (exp_le_exp.2 (min_le_left _ _)).trans (hW θ)).trans
      (integral_wealth_bettingCoin_le_one hL hg hgL hxm hx)
  have hlog : log (∫ θ, exp (Z θ) ∂μ) ≤ 0 :=
    log_nonpos (integral_nonneg fun θ ↦ (exp_pos _).le) hexp
  have hDV := (ENNReal.ofReal_le_iff_le_toReal hQ).1
    (TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv hZi hexpi)
  have hZK : ∫ θ, Z θ ∂Q ≤ K := by linarith
  have haZ : a ≤ ∫ θ, Z θ ∂Q := by
    simpa using integral_mono (integrable_const a) hZi hZa
  -- Jensen's inequality for `h` and its monotonicity conclude
  calc regret (fun t p ↦ ∫ θ, g t θ ∂p) (fun t ↦ bettingMixture μ (x t)) Q n
      ≤ 2 * L * ∫ θ, S θ ∂Q := regret_bettingMixture_le_two_mul_integral hL hg hgL hxm Q
    _ ≤ 2 * L * h (∫ θ, Z θ ∂Q) := mul_le_mul_of_nonneg_left
        (integral_le_map_integral_min hSm hS hf hfa hfh hh hhc hhm Q) (by positivity)
    _ ≤ 2 * L * h K := mul_le_mul_of_nonneg_left
        (hhm (mem_Ici.2 haZ) (mem_Ici.2 (haZ.trans hZK)) hZK) (by positivity)

/-- **The regret bound for experts** [Ora, Theorem 13.14]. Let the bets `x t θ` of the experts be
measurable and integrable, and the losses `g t` be measurable with values in `[-L, L]`. Assume
that each bettor, from the initial wealth `1`, has the wealth `exp (f (∑ t < n, c t θ))` after `n`
rounds on its coins `c t θ = bettingCoin …`, and let `h` be concave, continuous and nondecreasing
on `[a, ∞)` with `a ≤ f y` and `y ≤ h (f y)` for `|y| ≤ n`. Then for every probability measure
`Q` with `KL(Q, μ) < ∞`,
`∑ t < n, (∫ g t ∂(bettingMixture μ (x t)) - ∫ g t ∂Q) ≤ 2 L h (KL(Q, μ))`.

[Ora] asks `h` to be concave on `ℝ`; concavity on `[0, ∞)` alone would not suffice (see the
module docstring). -/
theorem regret_bettingMixture_le {a : ℝ} {f h : ℝ → ℝ} (hL : 0 < L)
    (hg : ∀ t < n, Measurable (g t)) (hgL : ∀ t < n, ∀ θ, |g t θ| ≤ L)
    (hxm : ∀ t < n, Measurable (x t)) (hx : ∀ t < n, Integrable (x t) μ)
    (hW : ∀ θ, exp (f (∑ t ∈ range n, bettingCoin μ L (g t) (x t) θ)) ≤
      wealth 1 (fun t ↦ bettingCoin μ L (g t) (x t) θ) (fun t ↦ x t θ) n)
    (hf : Measurable f) (hfa : ∀ y : ℝ, |y| ≤ n → a ≤ f y) (hfh : ∀ y : ℝ, |y| ≤ n → y ≤ h (f y))
    (hh : ConcaveOn ℝ (Ici a) h) (hhc : ContinuousOn h (Ici a)) (hhm : MonotoneOn h (Ici a))
    (Q : Measure Θ) [IsProbabilityMeasure Q] (hQ : klDiv Q μ ≠ ∞) :
    regret (fun t p ↦ ∫ θ, g t θ ∂p) (fun t ↦ bettingMixture μ (x t)) Q n ≤
      2 * L * h (klDiv Q μ).toReal :=
  regret_bettingMixture_le_of_toReal_klDiv_le hL hg hgL hxm hx hW hf hfa hfh hh hhc hhm Q hQ le_rfl

/-- **The quantile bound** [Ora, Remark 13.13]. Under the hypotheses of `regret_bettingMixture_le`,
if every expert of a measurable set `A` of positive prior mass has cumulative loss at most `G`
after `n` rounds, then the cumulative loss of the predictions is at most
`G + 2 L h (log (1 / μ A))`. For `μ` uniform on `k` experts and `A` the `⌈ε k⌉` best ones, this
bounds the regret against the `⌈ε k⌉`-th best expert by `2 L h (log (1 / ε))`. The proof applies
the regret bound to the prior conditioned on `A`, whose relative entropy to the prior is at most
`log (1 / μ A)` (`InformationTheory.klDiv_cond_le`). -/
theorem sum_integral_bettingMixture_le_of_forall_mem {a G : ℝ} {f h : ℝ → ℝ} (hL : 0 < L)
    (hg : ∀ t < n, Measurable (g t)) (hgL : ∀ t < n, ∀ θ, |g t θ| ≤ L)
    (hxm : ∀ t < n, Measurable (x t)) (hx : ∀ t < n, Integrable (x t) μ)
    (hW : ∀ θ, exp (f (∑ t ∈ range n, bettingCoin μ L (g t) (x t) θ)) ≤
      wealth 1 (fun t ↦ bettingCoin μ L (g t) (x t) θ) (fun t ↦ x t θ) n)
    (hf : Measurable f) (hfa : ∀ y : ℝ, |y| ≤ n → a ≤ f y) (hfh : ∀ y : ℝ, |y| ≤ n → y ≤ h (f y))
    (hh : ConcaveOn ℝ (Ici a) h) (hhc : ContinuousOn h (Ici a)) (hhm : MonotoneOn h (Ici a))
    {A : Set Θ} (hA : MeasurableSet A) (hμA : μ A ≠ 0)
    (hG : ∀ θ ∈ A, ∑ t ∈ range n, g t θ ≤ G) :
    ∑ t ∈ range n, ∫ θ, g t θ ∂bettingMixture μ (x t) ≤ G + 2 * L * h (log (μ.real A)⁻¹) := by
  have := cond_isProbabilityMeasure hμA
  have hμA' : 0 < μ.real A := ENNReal.toReal_pos hμA (measure_ne_top μ A)
  -- the relative entropy of the conditioned prior
  have hKL := klDiv_cond_le hμA
  rw [ENNReal.log_pos_real (ENNReal.inv_ne_zero.2 (measure_ne_top μ A)) (ENNReal.inv_ne_top.2 hμA),
    ENNReal.toReal_inv] at hKL
  have hne : klDiv (μ[|A]) μ ≠ ∞ := by
    intro htop
    rw [htop] at hKL
    exact absurd hKL (by simp)
  have hle : (klDiv (μ[|A]) μ).toReal ≤ log (μ.real A)⁻¹ := by
    rw [← EReal.coe_le_coe_iff, EReal.coe_ennreal_toReal hne]
    simpa [measureReal_def] using hKL
  have hreg := regret_bettingMixture_le_of_toReal_klDiv_le hL hg hgL hxm hx hW hf hfa hfh hh hhc
    hhm (μ[|A]) hne hle
  have hgi (t : ℕ) (ht : t < n) : Integrable (g t) (μ[|A]) :=
    Integrable.of_bound (hg t ht).aestronglyMeasurable L
      (Filter.Eventually.of_forall fun θ ↦ hgL t ht θ)
  have hsum : ∑ t ∈ range n, ∫ θ, g t θ ∂(μ[|A]) ≤ G := by
    rw [← integral_finsetSum _ fun t ht ↦ hgi t (mem_range.1 ht)]
    calc ∫ θ, ∑ t ∈ range n, g t θ ∂(μ[|A]) ≤ ∫ _, G ∂(μ[|A]) :=
          integral_mono_ae (integrable_finsetSum _ fun t ht ↦ hgi t (mem_range.1 ht))
            (integrable_const G) ((ae_cond_mem hA).mono fun θ hθ ↦ hG θ hθ)
      _ = G := by simp
  rw [regret_def, sum_sub_distrib] at hreg
  linarith

end Regret

section Finite

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] {L : ℝ} {n : ℕ}
  {g x : ℕ → α → ℝ}

/-- **The regret bound for finitely many experts** [Ora, Theorem 13.14]: the case of a finite
type `α` of experts, with the prior `weightedMeasure w` of a probability vector `w`. Under the
hypotheses of `regret_bettingMixture_le`, which hold automatically for the measurability and the
integrability, the regret against every probability vector `u` whose support is contained in that
of `w` is at most `2 L h (∑ i, u i log (u i / w i))`. -/
theorem regret_bettingMixture_weightedMeasure_le {a : ℝ} {f h : ℝ → ℝ} {w u : α → ℝ}
    (hL : 0 < L) (hw : w ∈ simplex α) (hu : u ∈ simplex α) (huw : ∀ i, 0 < u i → 0 < w i)
    (hgL : ∀ t < n, ∀ i, |g t i| ≤ L)
    (hW : ∀ i, exp (f (∑ t ∈ range n, bettingCoin (weightedMeasure w) L (g t) (x t) i)) ≤
      wealth 1 (fun t ↦ bettingCoin (weightedMeasure w) L (g t) (x t) i) (fun t ↦ x t i) n)
    (hf : Measurable f) (hfa : ∀ y : ℝ, |y| ≤ n → a ≤ f y) (hfh : ∀ y : ℝ, |y| ≤ n → y ≤ h (f y))
    (hh : ConcaveOn ℝ (Ici a) h) (hhc : ContinuousOn h (Ici a)) (hhm : MonotoneOn h (Ici a)) :
    ∑ t ∈ range n, (∫ i, g t i ∂bettingMixture (weightedMeasure w) (x t) - ∑ i, u i * g t i) ≤
      2 * L * h (∑ i, u i * log (u i / w i)) := by
  have := isProbabilityMeasure_weightedMeasure hw
  have := isProbabilityMeasure_weightedMeasure hu
  have hac := weightedMeasure_absolutelyContinuous huw
  have hne : klDiv (weightedMeasure u) (weightedMeasure w) ≠ ∞ :=
    klDiv_ne_top_iff.2 ⟨hac, Integrable.of_finite⟩
  have hKL : (klDiv (weightedMeasure u) (weightedMeasure w)).toReal =
      ∑ i, u i * log (u i / w i) := by
    rw [toReal_klDiv_eq_sum_mul_log_div hac, probReal_univ, probReal_univ, add_sub_cancel_right]
    simp_rw [measureReal_weightedMeasure_singleton_of_mem_simplex hu,
      measureReal_weightedMeasure_singleton_of_mem_simplex hw]
  have hreg := regret_bettingMixture_le hL (fun t _ ↦ measurable_of_finite _) hgL
    (fun t _ ↦ measurable_of_finite _) (fun t _ ↦ Integrable.of_finite) hW hf hfa hfh hh hhc hhm
    (weightedMeasure u) hne
  rw [hKL, regret_def] at hreg
  simpa [integral_weightedMeasure_eq_sum (mem_simplex_iff.1 hu).1] using hreg

end Finite


section Learner

namespace OnlineLearner

variable {C : Type*}

/-- **The experts-through-betting learner** [Ora, §13.6] with the prior `μ`, for losses in
`[-L, L]`, from a bettor `B`: each expert `θ` has a copy of `B`, fed the coins
`bettingCoin μ L (g t) (x t) θ` of its own bets, and the learner predicts the mixture
`bettingMixture μ (x t)` of the experts weighted by the positive parts of their bets. With the
Krichevsky–Trofimov bettor, it is [Ora, Algorithm 13.4]. -/
noncomputable def bettingExperts (μ : Measure Θ) (L : ℝ) (B : OnlineLearner C ℝ ℝ) :
    OnlineLearner C (Θ → ℝ) (Measure Θ) :=
  (pi fun _ : Θ ↦ B).reduce (bettingMixture μ) fun x g ↦ bettingCoin μ L g x

/-- **The plays of the experts-through-betting learner**: they are the mixtures
`bettingMixture μ (x t)` of bets `x t θ` that are the bets of `B` on the coins of the expert `θ`.
-/
theorem exists_run_bettingExperts (μ : Measure Θ) (L : ℝ) (B : OnlineLearner C ℝ ℝ)
    (d : ℕ → C) (g : ℕ → Θ → ℝ) : ∃ x : ℕ → Θ → ℝ,
      (∀ t, (bettingExperts μ L B).run d g t = bettingMixture μ (x t)) ∧
      ∀ t θ, x t θ = B.run d (fun s ↦ bettingCoin μ L (g s) (x s) θ) t := by
  set A := pi fun _ : Θ ↦ B
  set z := A.closedLoopFeedback d fun s y ↦ bettingCoin μ L (g s) y
  refine ⟨A.run d z, fun t ↦ ?_, fun t θ ↦ ?_⟩
  · rw [bettingExperts, run_reduce]
  · rw [run_pi]
    congr 1
    funext s
    exact congrFun (A.closedLoopFeedback_eq d _ s) θ

variable [IsProbabilityMeasure μ] {L : ℝ} {B : OnlineLearner C ℝ ℝ}

/-- **The regret guarantee of the experts-through-betting learner** [Ora, Theorem 13.14]. Let the
bettor `B` be measurable in the coins, with bets bounded at each round for coins in `[-1, 1]`, and
guarantee after `n` rounds, from the initial wealth `1`, the wealth `exp (f n (∑ t < n, c t))` on
every sequence of coins in `[-1, 1]`. Let `h n` be concave, continuous and nondecreasing on
`[a n, ∞)` with `a n ≤ f n y` and `y ≤ h n (f n y)` for `|y| ≤ n`. Then for measurable losses in
`[-L, L]`, the regret of `bettingExperts μ L B` against every probability measure `Q` with
`KL(Q, μ) < ∞` is at most `2 L h n (KL(Q, μ))`. -/
theorem hasRegretBound_bettingExperts (hL : 0 < L) {a : ℕ → ℝ} {f h : ℕ → ℝ → ℝ}
    (hBm : ∀ d t, Measurable fun c : ℕ → ℝ ↦ B.run d c t)
    (hBb : ∀ d t, ∃ K, ∀ c : ℕ → ℝ, (∀ s < t, |c s| ≤ 1) → |B.run d c t| ≤ K)
    (hB : ∀ d (c : ℕ → ℝ) n, (∀ t < n, |c t| ≤ 1) →
      exp (f n (∑ t ∈ range n, c t)) ≤ wealth 1 c (B.run d c) n)
    (hf : ∀ n, Measurable (f n)) (hfa : ∀ (n : ℕ) (y : ℝ), |y| ≤ n → a n ≤ f n y)
    (hfh : ∀ (n : ℕ) (y : ℝ), |y| ≤ n → y ≤ h n (f n y)) (hh : ∀ n, ConcaveOn ℝ (Ici (a n)) (h n))
    (hhc : ∀ n, ContinuousOn (h n) (Ici (a n))) (hhm : ∀ n, MonotoneOn (h n) (Ici (a n))) :
    (bettingExperts μ L B).HasRegretBound (fun g p ↦ ∫ θ, g θ ∂p)
      (fun _ g ↦ Measurable g ∧ ∀ θ, |g θ| ≤ L) {Q | IsProbabilityMeasure Q ∧ klDiv Q μ ≠ ∞}
      fun n _ _ Q ↦ 2 * L * h n (klDiv Q μ).toReal := by
  refine hasRegretBound_iff.2 fun d g n hg Q ⟨hQ, hQμ⟩ ↦ ?_
  obtain ⟨x, hrun, hx⟩ := exists_run_bettingExperts μ L B d g
  have hc (t : ℕ) (ht : t < n) (θ : Θ) : |bettingCoin μ L (g t) (x t) θ| ≤ 1 :=
    abs_bettingCoin_le_one hL (hg t ht).2 θ
  -- the bets are measurable, by strong induction on the rounds
  have hxm (t : ℕ) (ht : t < n) : Measurable (x t) := by
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      have e : x t = fun θ ↦ B.run d (fun s ↦ if s < t then bettingCoin μ L (g s) (x s) θ
          else 0) t := funext fun θ ↦ by
        rw [hx t θ]
        exact B.run_congr (fun _ _ ↦ rfl) fun s hs ↦ by simp [hs]
      rw [e]
      refine (hBm d t).comp (Measurable.of_eval fun s ↦ ?_)
      by_cases hs : s < t
      · simp only [hs, ↓reduceIte]
        exact measurable_bettingCoin (hg s (hs.trans ht)).1 (ih s hs (hs.trans ht))
      · simp only [hs, ↓reduceIte]
        exact measurable_const
  have hxi (t : ℕ) (ht : t < n) : Integrable (x t) μ := by
    obtain ⟨K, hK⟩ := hBb d t
    exact Integrable.of_bound (hxm t ht).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun θ ↦ by
        rw [Real.norm_eq_abs, hx t θ]
        exact hK _ fun s hs ↦ hc s (hs.trans ht) θ)
  have hW (θ : Θ) : exp (f n (∑ t ∈ range n, bettingCoin μ L (g t) (x t) θ)) ≤
      wealth 1 (fun t ↦ bettingCoin μ L (g t) (x t) θ) (fun t ↦ x t θ) n := by
    have e : (fun t ↦ x t θ) = B.run d fun s ↦ bettingCoin μ L (g s) (x s) θ :=
      funext fun t ↦ hx t θ
    rw [e]
    exact hB d _ n fun t ht ↦ hc t ht θ
  have e : (bettingExperts μ L B).run d g = fun t ↦ bettingMixture μ (x t) := funext hrun
  rw [e]
  exact regret_bettingMixture_le hL (fun t ht ↦ (hg t ht).1) (fun t ht ↦ (hg t ht).2) hxm hxi hW
    (hf n) (hfa n) (hfh n) (hh n) (hhc n) (hhm n) Q hQμ

end OnlineLearner

end Learner

section KrichevskyTrofimov

namespace OnlineLearner

variable {C : Type*} [IsProbabilityMeasure μ] {L : ℝ}

/-- **Experts through Krichevsky–Trofimov bettors** [Ora, §13.6, Algorithm 13.4]: for measurable
losses in `[-L, L]`, the regret after `n` rounds of `bettingExperts μ L (krichevskyTrofimov 1)`
against every probability measure `Q` with `KL(Q, μ) < ∞` is at most
`2 L √(2 n (KL(Q, μ) + log n / 2 + 1))`, that is `L √(8 n (KL(Q, μ) + log n / 2 + 1))`. The
logarithm of the horizon comes from the factor `1 / √n` of the wealth of the Krichevsky–Trofimov
bettor (`mul_exp_sq_div_sub_le_wealth`), with `f y = y ^ 2 / (2 n) - log n / 2 - 1` and
`h z = √(2 n (z + log n / 2 + 1))`. -/
theorem hasRegretBound_bettingExperts_krichevskyTrofimov (hL : 0 < L) :
    (bettingExperts (C := C) μ L (krichevskyTrofimov 1)).HasRegretBound (fun g p ↦ ∫ θ, g θ ∂p)
      (fun _ g ↦ Measurable g ∧ ∀ θ, |g θ| ≤ L) {Q | IsProbabilityMeasure Q ∧ klDiv Q μ ≠ ∞}
      fun n _ _ Q ↦ 2 * L * √(2 * n * ((klDiv Q μ).toReal + log n / 2 + 1)) := by
  refine hasRegretBound_bettingExperts (a := fun n ↦ -(log n / 2 + 1))
    (f := fun n y ↦ y ^ 2 / (2 * n) - log n / 2 - 1)
    (h := fun n z ↦ √(2 * n * (z + log n / 2 + 1))) hL
    (measurable_run_krichevskyTrofimov 1)
    (fun d t ↦ ⟨1 * 2 ^ t, fun c hc ↦ abs_run_krichevskyTrofimov_le zero_le_one d hc⟩)
    (fun d c n hc ↦ ?_) (fun n ↦ by fun_prop) (fun n y _ ↦ ?_) (fun n y hy ↦ ?_) (fun n ↦ ?_)
    (fun n ↦ by fun_prop) (fun n z _ w _ hzw ↦ ?_)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [exp_le_one_iff]
    · simpa using mul_exp_sq_div_sub_le_wealth zero_le_one hn hc
        fun t _ ↦ run_krichevskyTrofimov 1 d c t
  · simp only [neg_add_rev]
    linarith [div_nonneg (sq_nonneg y) (by positivity : (0 : ℝ) ≤ 2 * n)]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [CharP.cast_eq_zero, abs_nonpos_iff] at hy
      simp [hy]
    · have e : 2 * (n : ℝ) * (y ^ 2 / (2 * n) - log n / 2 - 1 + log n / 2 + 1) = y ^ 2 := by
        field_simp
        ring
      simp only [e, sqrt_sq_eq_abs]
      exact le_abs_self y
  · set φ : ℝ →ᵃ[ℝ] ℝ :=
      (2 * (n : ℝ)) • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (2 * n * (log n / 2 + 1))
    have hφ (z : ℝ) : φ z = 2 * n * (z + log n / 2 + 1) := by
      simp [φ]
      ring
    have hc := (strictConcaveOn_sqrt.concaveOn.comp_affineMap φ).subset
      (s := Ici (-(log n / 2 + 1))) (fun z hz ↦ by
      simp only [Set.mem_preimage, hφ, Set.mem_Ici] at hz ⊢
      exact mul_nonneg (by positivity) (by linarith)) (convex_Ici _)
    exact hc.congr fun z _ ↦ by simp only [Function.comp_apply, hφ]
  · exact sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end OnlineLearner

end KrichevskyTrofimov

end LMLExplore.OnlineLearning
