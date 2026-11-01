/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import LMLExplore.Analysis.SpecialFunctions.Exp
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
public import LMLExplore.Probability.Distributions.ExponentialFamily.Bernoulli
public import LMLExplore.Probability.Distributions.ExponentialFamily.Chernoff
public import TauCeti.Probability.Distributions.Bernoulli.Basic

/-!
# Chernoff bounds in relative-entropy form

For independent random variables `X i ∈ [0, 1]` whose means are at most `m`, the probability that
their sum over a finite set `s` exceeds `#s * p`, for `p ∈ [m, 1]`, is at most
`exp (-#s * d(p, m))`, where `d = klBerReal` is the binary relative entropy. Symmetrically, if the
means are at least `m`, the probability that the sum is at most `#s * p`, for `p ∈ [0, m]`, is at
most `exp (-#s * d(p, m))`. This is the Chernoff bound of the Bernoulli law, which dominates the
`[0, 1]`-valued case: by convexity of `exp`, `E[exp (t X)] ≤ 1 - m + m exp t` for `t ≥ 0`, so that
`X` is dominated above by `Ber((1 : ℝ), 0, m)` (`LMLExplore.MGFDominatedAbove`), and symmetrically
dominated below when its mean is at least `m`. The Bernoulli laws form an exponential family whose
divergence is `d`, and for `p, m ∈ (0, 1)` both bounds are the Cramér–Chernoff bounds under
domination by an exponential family
(`ProbabilityTheory.iIndepFun.measureReal_sum_ge_le_exp_expFamilyDiv`). At the boundary levels
`p = 1` (upper tail) and `p = 0` (lower tail), the bounds `m ^ #s` and `(1 - m) ^ #s` follow from
Markov's inequality, since the sum reaches `#s` (resp. `0`) only if every `X i` is `1`
(resp. `0`). By Pinsker's
inequality `d(p, m) ≥ 2 (p - m)²`, these bounds are sharper than Hoeffding's inequality.

The lower tail controls the upper confidence level `U(μ̂, c)` of the KL-UCB algorithm at the
empirical mean `μ̂ = (∑ i ∈ s, X i) / #s`: for a level `q < 1` with `q ≤ m`, `U(μ̂, L / #s) ≤ q`
has probability at most `exp (-L) exp (-2 #s (m - q)²)`. This is the confidence bound that controls
the underestimation of an optimal arm in the analysis of KL-UCB.

Hoeffding's inequality also controls the overestimation of the KL-UCB index [LS, Lemma 10.8]: for
independent `X₀, X₁, …` in `[0, 1]` with means at most `m` and a level `c ∈ (m + ε, 1)`, the
expected number of sample sizes `s` at which `s = 0`, `c ≤ μ̂_s` or `d(μ̂_s, c) ≤ L / s` is at most
`1 + L / d(m + ε, c) + 1 / (2 ε²)`, since `d(μ̂_s, c) ≥ d(m + ε, c)` unless `μ̂_s ≥ m + ε`.

## Main statements

* `LMLExplore.mgf_le_one_sub_integral_add_integral_mul_exp`: for `X ∈ [0, 1]` a.s. and every
  `t`, `mgf X μ t ≤ 1 - E[X] + E[X] exp t`.
* `LMLExplore.mgf_le_one_sub_add_mul_exp`: for `X ∈ [0, 1]` a.s. with `E[X] ≤ m` and `t ≥ 0`,
  `mgf X μ t ≤ 1 - m + m exp t`.
* `LMLExplore.mgfDominatedAbove_bernoulliMeasure`, `LMLExplore.mgfDominatedBelow_bernoulliMeasure`:
  a random variable with values in `[0, 1]` and mean at most (resp. at least) `q` is dominated
  above (resp. below) by `Ber((1 : ℝ), 0, q)`.
* `LMLExplore.measureReal_sum_ge_le_exp_klBerReal`: the upper tail
  `P(#s * p ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(p, m)))` for `0 < m ≤ p ≤ 1`.
* `LMLExplore.measureReal_card_mul_add_le_sum_le`: Hoeffding's inequality
  `P(#s * (m + ε) ≤ ∑ i ∈ s, X i) ≤ exp (-2 ε² #s)` for `ε ≥ 0`.
* `LMLExplore.measureReal_sum_le_le_exp_klBerReal`: the lower tail
  `P(∑ i ∈ s, X i ≤ #s * p) ≤ exp (-(#s * d(p, m)))` for `0 ≤ p ≤ m < 1`.
* `LMLExplore.measureReal_exists_sum_le_and_le_klBerReal_le`: the lower tail for all levels
  `p ∈ [0, m]` with `y ≤ d(p, m)` at once, `P(∃ p, ∑ i ∈ s, X i ≤ #s * p ∧ y ≤ d(p, m))
  ≤ exp (-(#s * y))`.
* `LMLExplore.measureReal_klUpper_le_le`: for `q < 1` with `q ≤ m`,
  `P(U(μ̂, L / #s) ≤ q) ≤ exp (-L) exp (-2 (m - q)² #s)` for the empirical mean `μ̂`.
* `LMLExplore.sum_measureReal_eq_zero_or_le_div_or_klBer_div_le_le`: [LS, Lemma 10.8], for
  `m + ε < c < 1` and `L ≥ 0`, `∑_{s < n} P(s = 0 ∨ c ≤ μ̂_s ∨ d(μ̂_s, c) ≤ L / s)
  ≤ 1 + L / d(m + ε, c) + 1 / (2 ε²)` for the empirical means `μ̂_s` of the first `s` variables.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 10.3, Note 10.3.1, Corollary 10.4 and Lemma 10.8.
-/

public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped NNReal Topology unitInterval

namespace LMLExplore

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m p : ℝ}

/-- For `x ∈ [0, 1]` and every `t`, `exp (t x) ≤ 1 - x + x exp t`, by convexity of `exp`. -/
theorem exp_mul_le_one_sub_add_mul_exp {x : ℝ} (hx : x ∈ Set.Icc 0 1) (t : ℝ) :
    exp (t * x) ≤ 1 - x + x * exp t := by
  rw [mul_comm t x]
  simpa using convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ t) (sub_nonneg.2 hx.2) hx.1
    (sub_add_cancel 1 x)

/-- **Moment generating function of a `[0, 1]`-valued variable**: if `X ∈ [0, 1]` almost surely,
then for every `t`, `mgf X μ t ≤ 1 - E[X] + E[X] exp t`, the moment generating function of the
Bernoulli law with the mean of `X`. -/
theorem mgf_le_one_sub_integral_add_integral_mul_exp [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) (t : ℝ) :
    mgf X μ t ≤ 1 - μ[X] + μ[X] * exp t := by
  have hint : Integrable X μ := .of_mem_Icc 0 1 hXm hX
  have hint_exp : Integrable (fun ω ↦ exp (t * X ω)) μ := integrable_exp_mul_of_mem_Icc hXm hX
  calc mgf X μ t = ∫ ω, exp (t * X ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 - X ω + X ω * exp t) ∂μ := by
        refine integral_mono_ae hint_exp (((integrable_const 1).sub hint).add
          (hint.mul_const _)) ?_
        filter_upwards [hX] with ω hω using exp_mul_le_one_sub_add_mul_exp hω t
    _ = 1 - μ[X] + μ[X] * exp t := by
        have h1 : Integrable (fun ω ↦ 1 - X ω) μ := (integrable_const 1).sub hint
        rw [integral_add h1 (hint.mul_const _),
          integral_sub (integrable_const 1) hint, integral_const, integral_mul_const]
        simp

/-- **Moment generating function of a `[0, 1]`-valued variable**: if `X ∈ [0, 1]` almost surely
and `E[X] ≤ m`, then for `t ≥ 0`, `mgf X μ t ≤ 1 - m + m exp t`, the moment generating function of
the Bernoulli law of mean `m`. -/
theorem mgf_le_one_sub_add_mul_exp [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) (hmean : μ[X] ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    mgf X μ t ≤ 1 - m + m * exp t := by
  have := mul_le_mul_of_nonneg_right hmean (sub_nonneg.2 (one_le_exp ht))
  linarith [mgf_le_one_sub_integral_add_integral_mul_exp hXm hX t]

/-- A random variable with values in `[0, 1]` and mean at most `q` is dominated above by the
Bernoulli law of mean `q`: `mgf X μ t ≤ mgf id Ber((1 : ℝ), 0, q) t` for `t ≥ 0`. -/
theorem mgfDominatedAbove_bernoulliMeasure [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) {q : I} (hmean : μ[X] ≤ (q : ℝ)) :
    MGFDominatedAbove X μ id Ber((1 : ℝ), 0, q) where
  integrable_exp_mul _ _ _ := integrable_exp_mul_of_mem_Icc hXm hX
  mgf_le _ ht _ := by
    rw [TauCeti.Probability.mgf_id_bernoulliMeasure]
    exact mgf_le_one_sub_add_mul_exp hXm hX hmean ht

/-- A random variable with values in `[0, 1]` and mean at least `q` is dominated below by the
Bernoulli law of mean `q`: `mgf X μ t ≤ mgf id Ber((1 : ℝ), 0, q) t` for `t ≤ 0`. -/
theorem mgfDominatedBelow_bernoulliMeasure [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) {q : I} (hmean : (q : ℝ) ≤ μ[X]) :
    MGFDominatedBelow X μ id Ber((1 : ℝ), 0, q) where
  integrable_exp_mul _ _ _ := integrable_exp_mul_of_mem_Icc hXm hX
  mgf_le t ht _ := by
    rw [TauCeti.Probability.mgf_id_bernoulliMeasure]
    have := mul_le_mul_of_nonpos_right hmean (sub_nonpos.2 (exp_le_one_iff.2 ht))
    linarith [mgf_le_one_sub_integral_add_integral_mul_exp hXm hX t]

/-- For independent random variables `X i ∈ [0, 1]` with means at most `m`, the sum
`∑ i ∈ s, X i` reaches `#s` with probability at most `m ^ #s`: it does so only if every `X i` is
`1`, which has probability at most `m` by Markov's inequality. -/
private lemma measureReal_card_le_sum_le_pow {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, μ[X i] ≤ m) :
    μ.real {ω | (#s : ℝ) ≤ ∑ i ∈ s, X i ω} ≤ m ^ #s := by
  have := h_indep.isProbabilityMeasure
  have hX' : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω ∈ Set.Icc 0 1 := (eventually_all_finset s).2 hX
  -- the sum reaches `#s` only if every `X i` is at least `1`
  have h_sub : {ω | (#s : ℝ) ≤ ∑ i ∈ s, X i ω} ≤ᵐ[μ] ⋂ i ∈ s, X i ⁻¹' Set.Ici 1 := by
    filter_upwards [hX'] with ω hω h_sum
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Ici]
    intro i hi
    by_contra! h
    have h_lt : ∑ j ∈ s, X j ω < ∑ _j ∈ s, (1 : ℝ) :=
      Finset.sum_lt_sum (fun j hj ↦ (hω j hj).2) ⟨i, hi, h⟩
    simp only [sum_const, nsmul_eq_mul, mul_one] at h_lt
    linarith
  calc μ.real {ω | (#s : ℝ) ≤ ∑ i ∈ s, X i ω}
  _ ≤ μ.real (⋂ i ∈ s, X i ⁻¹' Set.Ici 1) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h_sub)
  _ = ∏ i ∈ s, μ.real (X i ⁻¹' Set.Ici 1) := by
    simp only [measureReal_def,
      h_indep.measure_inter_preimage_eq_mul s (fun _ _ ↦ measurableSet_Ici), ENNReal.toReal_prod]
  _ ≤ ∏ _i ∈ s, m := by
    refine prod_le_prod₀ (fun _ _ ↦ measureReal_nonneg) fun i hi ↦ ?_
    have h_int : Integrable (X i) μ := .of_mem_Icc 0 1 (hXm i hi) (hX i hi)
    have h_markov := mul_meas_ge_le_integral_of_nonneg
      ((hX i hi).mono fun _ hω ↦ hω.1) h_int 1
    rw [one_mul] at h_markov
    exact h_markov.trans (hmean i hi)
  _ = m ^ #s := prod_const _

/-- **Chernoff bound in relative-entropy form, upper tail** ([LS, Lemma 10.3 and Note 10.3.1]):
for independent random variables `X i ∈ [0, 1]` with means at most `m > 0`, and `p ∈ [m, 1]`,
`P(#s * p ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(p, m)))`. -/
theorem measureReal_sum_ge_le_exp_klBerReal {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, μ[X i] ≤ m) (hm : 0 < m)
    (hp : p ∈ Set.Icc m 1) :
    μ.real {ω | #s * p ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * klBerReal p m)) := by
  have := h_indep.isProbabilityMeasure
  rcases hp.1.eq_or_lt with rfl | hmp
  · simp
  have hm1 : m < 1 := hmp.trans_le hp.2
  rcases hp.2.eq_or_lt with rfl | hp1
  · -- `p = 1`: the sum reaches `#s` with probability at most `m ^ #s = exp (-(#s * d(1, m)))`
    rw [mul_one, klBerReal_one_left, mul_neg, neg_neg, exp_nat_mul, exp_log hm]
    exact measureReal_card_le_sum_le_pow h_indep hXm hX hmean
  · -- `m < p < 1`: the `X i` are dominated above by `Ber(1, 0, m)`, the member of mean `m` of the
    -- exponential family of `Ber(1, 0, 1/2)`, whose divergence is `d`
    have hm' : m ∈ Set.Ioo 0 1 := ⟨hm, hm1⟩
    have hp' : p ∈ Set.Ioo 0 1 := ⟨hm.trans hmp, hp1⟩
    rw [← expFamilyDiv_bernoulliMeasure_sigmoid 0 hp' hm']
    refine h_indep.measureReal_sum_ge_le_exp_expFamilyDiv (fun i hi ↦ ?_)
      (by rwa [expFamilyMeans_bernoulliMeasure_sigmoid])
      (by rwa [expFamilyMeans_bernoulliMeasure_sigmoid]) hmp.le
    rw [expFamily_natParam_bernoulliMeasure_sigmoid 0 hm']
    exact mgfDominatedAbove_bernoulliMeasure (hXm i hi) (hX i hi) (hmean i hi)

/-- **Hoeffding's inequality** for independent random variables `X i ∈ [0, 1]` with means at
most `m`: for `ε ≥ 0`, `P(#s * (m + ε) ≤ ∑ i ∈ s, X i) ≤ exp (-2 ε² #s)`. -/
theorem measureReal_card_mul_add_le_sum_le {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, μ[X i] ≤ m) {ε : ℝ}
    (hε : 0 ≤ ε) :
    μ.real {ω | #s * (m + ε) ≤ ∑ i ∈ s, X i ω} ≤ exp (-(2 * ε ^ 2 * #s)) := by
  have := h_indep.isProbabilityMeasure
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hs' : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  -- the centered variables are independent and `1 / 4`-sub-Gaussian
  have h_indep' : iIndepFun (fun i ω ↦ X i ω - μ[X i]) μ :=
    h_indep.comp (g := fun i (y : ℝ) ↦ y - ∫ ω, X i ω ∂μ) fun _ ↦ measurable_sub_const _
  have h_subG : ∀ i ∈ s,
      HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ :=
    fun i hi ↦ hasSubgaussianMGF_of_mem_Icc (hXm i hi) (hX i hi)
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
    ext
    norm_num
  refine le_trans (measureReal_mono fun ω (hω : _ ≤ _) ↦ ?_)
    ((HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep' h_subG (ε := #s * ε)
      (by positivity)).trans_eq ?_)
  · have : ∑ i ∈ s, μ[X i] ≤ #s * m := (sum_le_sum hmean).trans_eq (by simp)
    simp only [Set.mem_ofPred_eq, sum_sub_distrib]
    linarith
  · rw [hc]
    congr 1
    simp only [sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
    field_simp
    norm_num
    ring

/-- **Chernoff bound in relative-entropy form, lower tail** ([LS, Lemma 10.3 and Note 10.3.1]):
for independent random variables `X i ∈ [0, 1]` with means at least `m < 1`, and `p ∈ [0, m]`,
`P(∑ i ∈ s, X i ≤ #s * p) ≤ exp (-(#s * d(p, m)))`. -/
theorem measureReal_sum_le_le_exp_klBerReal {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, m ≤ μ[X i]) (hm : m < 1)
    (hp : p ∈ Set.Icc 0 m) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ #s * p} ≤ exp (-(#s * klBerReal p m)) := by
  have := h_indep.isProbabilityMeasure
  rcases hp.2.eq_or_lt with rfl | hpm
  · simp
  have hm0 : 0 < m := hp.1.trans_lt hpm
  rcases hp.1.eq_or_lt with rfl | hp0
  · -- `p = 0`: the sum vanishes only if every `1 - X i` is `1`, which has probability at most
    -- `(1 - m) ^ #s = exp (-(#s * d(0, m)))`
    have h := measureReal_card_le_sum_le_pow (X := fun i ω ↦ 1 - X i ω) (m := 1 - m)
      (h_indep.comp (fun _ x ↦ 1 - x) fun _ ↦ measurable_const.sub measurable_id)
      (fun i hi ↦ aemeasurable_const.sub (hXm i hi))
      (fun i hi ↦ by
        filter_upwards [hX i hi] with ω hω using ⟨sub_nonneg.2 hω.2, sub_le_self _ hω.1⟩)
      (fun i hi ↦ by
        simp [integral_sub (integrable_const 1) (.of_mem_Icc 0 1 (hXm i hi) (hX i hi))]
        linarith [hmean i hi])
    rw [← klBerReal_one_sub_one_sub, sub_zero, klBerReal_one_left, mul_neg, neg_neg, exp_nat_mul,
      exp_log (sub_pos.2 hm)]
    refine le_of_eq_of_le ?_ h
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, mul_zero, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
    constructor <;> intro h <;> linarith
  · -- `0 < p < m`: the `X i` are dominated below by `Ber(1, 0, m)`, the member of mean `m` of the
    -- exponential family of `Ber(1, 0, 1/2)`, whose divergence is `d`
    have hm' : m ∈ Set.Ioo 0 1 := ⟨hm0, hm⟩
    have hp' : p ∈ Set.Ioo 0 1 := ⟨hp0, hpm.trans hm⟩
    rw [← expFamilyDiv_bernoulliMeasure_sigmoid 0 hp' hm']
    refine h_indep.measureReal_sum_le_le_exp_expFamilyDiv (fun i hi ↦ ?_)
      (by rwa [expFamilyMeans_bernoulliMeasure_sigmoid])
      (by rwa [expFamilyMeans_bernoulliMeasure_sigmoid]) hpm.le
    rw [expFamily_natParam_bernoulliMeasure_sigmoid 0 hm']
    exact mgfDominatedBelow_bernoulliMeasure (hXm i hi) (hX i hi) (hmean i hi)

/-- **Chernoff bound in relative-entropy form, lower tail, for a set of levels**
([LS, (10.3) of Corollary 10.4]): for independent random variables `X i ∈ [0, 1]` with means at
least `m < 1` and every real `y`, the probability that `∑ i ∈ s, X i ≤ #s * p` for some level
`p ∈ [0, m]` with `y ≤ d(p, m)` is at most `exp (-(#s * y))`. -/
theorem measureReal_exists_sum_le_and_le_klBerReal_le {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, m ≤ μ[X i]) (hm : m < 1)
    (y : ℝ) :
    μ.real {ω | ∃ p ∈ Set.Icc 0 m, ∑ i ∈ s, X i ω ≤ #s * p ∧ y ≤ klBerReal p m} ≤
      exp (-(#s * y)) := by
  have := h_indep.isProbabilityMeasure
  set K := {p | p ∈ Set.Icc 0 m ∧ y ≤ klBerReal p m} with hK_def
  rcases K.eq_empty_or_nonempty with hK | hK
  · -- no level qualifies, and the event is empty
    have h_empty : {ω | ∃ p ∈ Set.Icc 0 m, ∑ i ∈ s, X i ω ≤ #s * p ∧ y ≤ klBerReal p m} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨p, hp, _, hy⟩ ↦ hK.subset ⟨hp, hy⟩
    rw [h_empty, measureReal_empty]
    positivity
  -- the set of levels is closed and bounded, so it has a largest element `p₀`, and the event is
  -- contained in `{∑ i ∈ s, X i ≤ #s * p₀}`
  have hcont : ContinuousOn (fun p ↦ klBerReal p m) (Set.Icc 0 m) := by
    rcases le_or_gt m 0 with hm0 | hm0
    · exact (Set.subsingleton_Icc_of_ge hm0).continuousOn _
    · exact (continuousOn_klBerReal.comp_continuous (continuous_id.prodMk continuous_const)
        fun _ ↦ ⟨trivial, hm0, hm⟩).continuousOn
  have hKc : IsClosed K := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hKb : BddAbove K := ⟨m, fun p hp ↦ hp.1.2⟩
  have hp₀ : sSup K ∈ K := hKc.csSup_mem hK hKb
  calc μ.real {ω | ∃ p ∈ Set.Icc 0 m, ∑ i ∈ s, X i ω ≤ #s * p ∧ y ≤ klBerReal p m}
  _ ≤ μ.real {ω | ∑ i ∈ s, X i ω ≤ #s * sSup K} :=
    measureReal_mono fun ω ⟨p, hp, hsum, hy⟩ ↦ hsum.trans (by gcongr; exact le_csSup hKb ⟨hp, hy⟩)
  _ ≤ exp (-(#s * klBerReal (sSup K) m)) :=
    measureReal_sum_le_le_exp_klBerReal h_indep hXm hX hmean hm hp₀.1
  _ ≤ exp (-(#s * y)) := by
    gcongr
    exact hp₀.2

/-- **Confidence bound for the upper confidence level** (the upper confidence level part of
[LS, Corollary 10.4], with an additional margin): for independent random variables `X i ∈ [0, 1]`
with means at least `m`, a nonempty finite set `s` with empirical mean
`μ̂ = (∑ i ∈ s, X i) / #s`, a level `q < 1` with `q ≤ m` and a real `L`, the upper confidence level
`U(μ̂, L / #s)` is at most `q` with probability at most `exp (-L) exp (-2 (m - q)² #s)`. -/
theorem measureReal_klUpper_le_le {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) {s : Finset ι}
    (hs : s.Nonempty) (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, m ≤ μ[X i]) {q : ℝ}
    (hq : q < 1) (hqm : q ≤ m) (L : ℝ) :
    μ.real {ω | klUpper ((∑ i ∈ s, X i ω) / #s) (ENNReal.ofReal (L / #s)) ≤ q} ≤
      exp (-L) * exp (-(2 * (m - q) ^ 2 * #s)) := by
  have := h_indep.isProbabilityMeasure
  have hs0 : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have hX' : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω ∈ Set.Icc 0 1 := (eventually_all_finset s).2 hX
  rcases lt_or_ge m 1 with hm | hm
  swap
  · -- for `m ≥ 1`, all the `X i` equal `1` almost surely, and `U(1, ·) = 1 > q`
    have h1 : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω = 1 := (eventually_all_finset s).2 fun i hi ↦ by
      -- `X i ≤ 1` and `1 ≤ E[X i]`, so `E[X i] = E[1]` and `X i = 1` almost surely
      have hint : Integrable (X i) μ := .of_mem_Icc 0 1 (hXm i hi) (hX i hi)
      have hle : X i ≤ᵐ[μ] fun _ ↦ 1 := (hX i hi).mono fun ω hω ↦ hω.2
      refine (integral_eq_iff_of_ae_le hint (integrable_const 1) hle).1 (le_antisymm ?_ ?_)
      · exact integral_mono_ae hint (integrable_const 1) hle
      · simpa using hm.trans (hmean i hi)
    have h_null : μ {ω | klUpper ((∑ i ∈ s, X i ω) / #s) (ENNReal.ofReal (L / #s)) ≤ q} = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [h1] with ω hω hU
      rw [sum_congr rfl hω, sum_const, nsmul_one, div_self hs0.ne',
        klUpper_one_left] at hU
      linarith
    rw [measureReal_def, h_null, ENNReal.toReal_zero]
    positivity
  -- on the event, `d(μ̂, m) ≥ d(μ̂, q) + d(q, m) ≥ L / #s + 2 (m - q)²` by the three-point
  -- inequality and Pinsker's inequality, and the lower tail Chernoff bound applies
  calc μ.real {ω | klUpper ((∑ i ∈ s, X i ω) / #s) (ENNReal.ofReal (L / #s)) ≤ q}
  _ ≤ μ.real {ω | ∃ p ∈ Set.Icc 0 m, ∑ i ∈ s, X i ω ≤ #s * p ∧
      L / #s + 2 * (m - q) ^ 2 ≤ klBerReal p m} := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hX'] with ω hω hU
    -- the empirical mean `x` lies in `[0, 1]` and satisfies `x ≤ U(x, L / #s) ≤ q`
    set x := (∑ i ∈ s, X i ω) / #s with hx_def
    have hx : x ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (sum_nonneg fun i hi ↦ (hω i hi).1) hs0.le, (div_le_one hs0).2
        ((sum_le_sum fun i hi ↦ (hω i hi).2).trans_eq (by simp))⟩
    have hxq : x ≤ q := (klUpper_mem_Icc hx.2 _).1.trans hU
    have hq' : q ∈ Set.Icc 0 1 := ⟨hx.1.trans hxq, hq.le⟩
    have hm' : m ∈ Set.Icc 0 1 := ⟨hq'.1.trans hqm, hm.le⟩
    have h_fin : klBer x m ≠ ⊤ := (klBer_ne_top_iff hx hm').2
      ⟨fun hm0 ↦ le_antisymm (hxq.trans (hqm.trans hm0.le)) hx.1, fun hm1 ↦ absurd hm1 hm.ne⟩
    -- `L / #s + 2 (m - q)² ≤ d(x, q) + d(q, m) ≤ d(x, m)`
    have h_le : ENNReal.ofReal (L / #s + 2 * (m - q) ^ 2) ≤ ENNReal.ofReal (klBerReal x m) := by
      rw [← klBer_eq_ofReal_klBerReal hx hm' h_fin]
      refine ENNReal.ofReal_add_le.trans ((add_le_add (le_klBer_of_klUpper_le hx hq hU) ?_).trans
        (klBer_add_klBer_le hxq hqm))
      rw [sub_sq_comm]
      exact ofReal_two_mul_sq_le_klBer hq' hm'
    refine ⟨x, ⟨hx.1, hxq.trans hqm⟩, (mul_div_cancel₀ _ hs0.ne').ge, ?_⟩
    exact (ENNReal.ofReal_le_ofReal_iff (klBerReal_nonneg hx hm' h_fin)).1 h_le
  _ ≤ exp (-(#s * (L / #s + 2 * (m - q) ^ 2))) :=
    measureReal_exists_sum_le_and_le_klBerReal_le h_indep hXm hX hmean hm _
  _ = exp (-L) * exp (-(2 * (m - q) ^ 2 * #s)) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring

/-- **Overestimation of the KL-UCB index** ([LS, Lemma 10.8] for rewards in `[0, 1]`). Let
`X₀, X₁, …` be independent, in `[0, 1]`, with means at most `m`, let `ε > 0` and `c < 1` with
`m + ε < c`, and let `L ≥ 0`. Then the expected number of sample sizes `s < n` at which `s = 0`, or
the empirical mean `μ̂_s = (X₀ + ⋯ + X_{s-1}) / s` is at least `c`, or `d(μ̂_s, c) ≤ L / s`, is at
most `1 + L / d(m + ε, c) + 1 / (2 ε²)`, uniformly in `n`. For an arm of mean `m`, `c` below the
optimal mean and `L = log f(n)`, this bounds the number of sample sizes at which the KL-UCB index
of the arm exceeds `c`. -/
theorem sum_measureReal_eq_zero_or_le_div_or_klBer_div_le_le {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (hXm : ∀ i, AEMeasurable (X i) μ)
    (hX : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i, μ[X i] ≤ m) {ε c : ℝ} (hε : 0 < ε)
    (hc : m + ε < c) (hc1 : c < 1) {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    ∑ s ∈ range n, μ.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
        klBer ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)} ≤
      1 + L / klBerReal (m + ε) c + 1 / (2 * ε ^ 2) := by
  have := h_indep.isProbabilityMeasure
  have hm0 : 0 ≤ m := (integral_nonneg_of_ae ((hX 0).mono fun ω hω ↦ hω.1)).trans (hmean 0)
  have hme : m + ε ∈ Set.Icc 0 1 := ⟨by linarith, by linarith⟩
  have hc' : c ∈ Set.Ioo 0 1 := ⟨by linarith, hc1⟩
  set D := klBerReal (m + ε) c with hD_def
  have hD : 0 < D := by
    have := two_mul_sq_le_klBerReal hme (Set.Ioo_subset_Icc_self hc') (klBer_ne_top hc')
    nlinarith
  -- the term of `s` is at most `1` if `s D ≤ L`, and otherwise at most the Hoeffding bound
  -- `exp (-2 ε² s)`: if `μ̂_s < m + ε`, then `D ≤ d(μ̂_s, c)`, and `μ̂_s < c`
  have h_term (s : ℕ) : μ.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
      klBer ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)} ≤
        if s * D ≤ L then 1 else exp (-(2 * ε ^ 2 * s)) := by
    split_ifs with hsD
    · exact measureReal_le_one
    have h_hoeffding := measureReal_card_mul_add_le_sum_le h_indep (s := range s)
      (fun i _ ↦ hXm i) (fun i _ ↦ hX i) (fun i _ ↦ hmean i) hε.le
    rw [card_range] at h_hoeffding
    refine le_trans (measureReal_mono fun ω hω ↦ ?_) h_hoeffding
    have hs : s ≠ 0 := by
      rintro rfl
      simp only [CharP.cast_eq_zero, zero_mul] at hsD
      exact hsD hL
    have hs' : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra! hlt
    have hx : (∑ i ∈ range s, X i ω) / s < m + ε := by rwa [div_lt_iff₀ hs', mul_comm]
    rcases hω with h0 | hcx | hkl
    · exact hs h0
    · linarith
    · refine hsD ?_
      have h1 : klBer (m + ε) c ≤ klBer ((∑ i ∈ range s, X i ω) / s) c :=
        antitoneOn_klBer_left c (Set.mem_Iic.2 (by linarith)) (Set.mem_Iic.2 hc.le) hx.le
      rw [klBer_eq_ofReal_klBerReal hme (Set.Ioo_subset_Icc_self hc') (klBer_ne_top hc')] at h1
      have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans hkl)
      rw [le_div_iff₀ hs'] at h2
      linarith
  calc ∑ s ∈ range n, μ.real {ω | s = 0 ∨ c ≤ (∑ i ∈ range s, X i ω) / s ∨
      klBer ((∑ i ∈ range s, X i ω) / s) c ≤ ENNReal.ofReal (L / s)}
  _ ≤ ∑ s ∈ range n, (if s * D ≤ L then 1 else exp (-(2 * ε ^ 2 * s))) :=
    sum_le_sum fun s _ ↦ h_term s
  _ ≤ 1 + L / D + 1 / (2 * ε ^ 2) := by
    rcases n with _ | k
    · simp only [range_zero, sum_empty]
      positivity
    -- the term of `s = 0` is `1`; the others are at most `1_{(s + 1) D ≤ L} + exp (-2 ε² (s + 1))`
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, hL, ite_true, Nat.cast_add_one]
    calc ∑ s ∈ range k, (if (s + 1) * D ≤ L then 1 else exp (-(2 * ε ^ 2 * (s + 1)))) + 1
    _ ≤ ∑ s ∈ range k, ((if (s + 1) * D ≤ L then (1 : ℝ) else 0) +
        exp (-(2 * ε ^ 2 * (s + 1)))) + 1 := by
      gcongr with s
      split_ifs <;> simp [exp_nonneg]
    _ ≤ L / D + (2 * ε ^ 2)⁻¹ + 1 := by
      rw [sum_add_distrib]
      gcongr
      · exact sum_range_ite_add_one_mul_le_le hD hL k
      · exact sum_range_exp_neg_mul_le (by positivity) k
    _ = 1 + L / D + 1 / (2 * ε ^ 2) := by ring

end LMLExplore
