/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Probability.Moments.Basic
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# Chernoff bounds in relative-entropy form

For independent random variables `X i ∈ [0, 1]` whose means are at most `m`, the probability that
their sum over a finite set `s` exceeds `#s * p`, for `p ∈ [m, 1]`, is at most
`exp (-#s * d(p, m))`, where `d = klBerReal` is the binary relative entropy. Symmetrically, if the
means are at least `m`, the probability that the sum is at most `#s * p`, for `p ∈ [0, m]`, is at
most `exp (-#s * d(p, m))`. This is the Chernoff bound of the Bernoulli law, which dominates the
`[0, 1]`-valued case: by convexity of `exp`, `E[exp (t X)] ≤ 1 - m + m exp t` for `t ≥ 0`. By
Pinsker's inequality `d(p, m) ≥ 2 (p - m)²`, it is sharper than Hoeffding's inequality.

The lower tail controls the upper confidence level `U(μ̂, c)` of the KL-UCB algorithm at the
empirical mean `μ̂ = (∑ i ∈ s, X i) / #s`: for a level `q < 1` with `q ≤ m`, `U(μ̂, L / #s) ≤ q`
has probability at most `exp (-L) exp (-2 #s (m - q)²)`. This is the confidence bound that controls
the underestimation of an optimal arm in the analysis of KL-UCB.

## Main statements

* `LMLExplore.mgf_le_one_sub_add_mul_exp`: for `X ∈ [0, 1]` a.s. with `E[X] ≤ m` and `t ≥ 0`,
  `mgf X μ t ≤ 1 - m + m exp t`.
* `LMLExplore.measureReal_sum_ge_le_exp_mul_pow`: the Chernoff bound at a fixed `t ≥ 0`,
  `P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (1 - m + m exp t) ^ #s`.
* `LMLExplore.measureReal_sum_ge_le_exp_klBerReal`: the upper tail
  `P(#s * p ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(p, m)))` for `0 < m ≤ p ≤ 1`.
* `LMLExplore.measureReal_sum_le_le_exp_klBerReal`: the lower tail
  `P(∑ i ∈ s, X i ≤ #s * p) ≤ exp (-(#s * d(p, m)))` for `0 ≤ p ≤ m < 1`.
* `LMLExplore.measureReal_exists_sum_le_and_le_klBerReal_le`: the lower tail for all levels
  `p ∈ [0, m]` with `y ≤ d(p, m)` at once, `P(∃ p, ∑ i ∈ s, X i ≤ #s * p ∧ y ≤ d(p, m))
  ≤ exp (-(#s * y))`.
* `LMLExplore.measureReal_klUpper_le_le`: for `q < 1` with `q ≤ m`,
  `P(U(μ̂, L / #s) ≤ q) ≤ exp (-L) exp (-2 (m - q)² #s)` for the empirical mean `μ̂`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 10.3, Note 10.3.1 and Corollary 10.4.
-/

public section

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Topology

namespace LMLExplore

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m p : ℝ}

/-- For `x ∈ [0, 1]` and every `t`, `exp (t x) ≤ 1 - x + x exp t`, by convexity of `exp`. -/
theorem exp_mul_le_one_sub_add_mul_exp {x : ℝ} (hx : x ∈ Set.Icc 0 1) (t : ℝ) :
    exp (t * x) ≤ 1 - x + x * exp t := by
  rw [mul_comm t x]
  simpa using convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ t) (sub_nonneg.2 hx.2) hx.1
    (sub_add_cancel 1 x)

/-- **Moment generating function of a `[0, 1]`-valued variable**: if `X ∈ [0, 1]` almost surely
and `E[X] ≤ m`, then for `t ≥ 0`, `mgf X μ t ≤ 1 - m + m exp t`, the moment generating function
of the Bernoulli law of mean `m`. -/
theorem mgf_le_one_sub_add_mul_exp [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) (hmean : μ[X] ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    mgf X μ t ≤ 1 - m + m * exp t := by
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
    _ ≤ 1 - m + m * exp t := by
        have := mul_le_mul_of_nonneg_right hmean (sub_nonneg.2 (one_le_exp ht))
        linarith

/-- **Chernoff bound for `[0, 1]`-valued variables**: for independent random variables
`X i ∈ [0, 1]` with means at most `m`, every threshold `a` and every `t ≥ 0`,
`P(a ≤ ∑ i ∈ s, X i) ≤ exp (-t a) (1 - m + m exp t) ^ #s`. -/
theorem measureReal_sum_ge_le_exp_mul_pow {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, μ[X i] ≤ m) (a : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | a ≤ ∑ i ∈ s, X i ω} ≤ exp (-t * a) * (1 - m + m * exp t) ^ #s := by
  have := h_indep.isProbabilityMeasure
  have hX' : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω ∈ Set.Icc 0 1 := (eventually_all_finset s).2 hX
  have hint : Integrable (fun ω ↦ exp (t * ∑ i ∈ s, X i ω)) μ := by
    refine integrable_exp_mul_of_le t #s ht (Finset.aemeasurable_fun_sum s hXm) ?_
    filter_upwards [hX'] with ω hω
    calc ∑ i ∈ s, X i ω ≤ ∑ _i ∈ s, (1 : ℝ) := sum_le_sum fun i hi ↦ (hω i hi).2
      _ = #s := by simp
  refine (measure_ge_le_exp_mul_mgf _ ht hint).trans
    (mul_le_mul_of_nonneg_left ?_ (exp_pos _).le)
  have hsum := (h_indep.precomp (Subtype.val_injective (p := (· ∈ s)))).mgf_sum₀ (t := t)
    (fun i ↦ hXm i i.2) univ
  have hfun : (fun ω ↦ ∑ i ∈ s, X i ω) = ∑ i : s, X i := by
    ext ω
    rw [Finset.sum_apply, Finset.sum_coe_sort s fun i ↦ X i ω]
  rw [hfun, hsum, Finset.prod_coe_sort s fun i ↦ mgf (X i) μ t]
  calc ∏ i ∈ s, mgf (X i) μ t ≤ ∏ _i ∈ s, (1 - m + m * exp t) :=
        prod_le_prod₀ (fun _ _ ↦ mgf_nonneg)
          fun i hi ↦ mgf_le_one_sub_add_mul_exp (hXm i hi) (hX i hi) (hmean i hi) ht
    _ = (1 - m + m * exp t) ^ #s := prod_const _

/-- **Chernoff bound in relative-entropy form, upper tail** ([LS, Lemma 10.3 and Note 10.3.1]):
for independent random variables `X i ∈ [0, 1]` with means at most `m > 0`, and `p ∈ [m, 1]`,
`P(#s * p ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(p, m)))`. -/
theorem measureReal_sum_ge_le_exp_klBerReal {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, μ[X i] ≤ m) (hm : 0 < m)
    (hp : p ∈ Set.Icc m 1) :
    μ.real {ω | #s * p ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * klBerReal p m)) := by
  have := h_indep.isProbabilityMeasure
  have hbound (t : ℝ) (ht : 0 ≤ t) :=
    measureReal_sum_ge_le_exp_mul_pow h_indep hXm hX hmean (#s * p) ht
  rcases hp.1.eq_or_lt with rfl | hmp
  · simp
  have hm1 : m < 1 := hmp.trans_le hp.2
  rcases hp.2.eq_or_lt with rfl | hp1
  · -- `p = 1`: let `t → ∞` in the Chernoff bound
    have heq (t : ℝ) : exp (-t * (#s * 1)) * (1 - m + m * exp t) ^ #s
        = ((1 - m) * exp (-t) + m) ^ #s := by
      rw [mul_one, mul_comm (-t), exp_nat_mul, ← mul_pow, exp_neg]
      field_simp
    have hlim : Tendsto (fun t ↦ ((1 - m) * exp (-t) + m) ^ #s) atTop (𝓝 (m ^ #s)) := by
      simpa using ((tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - m)).add_const m).pow #s
    refine (ge_of_tendsto hlim ((eventually_ge_atTop 0).mono fun t ht ↦
      (hbound t ht).trans_eq (heq t))).trans_eq ?_
    simp [exp_nat_mul, exp_log hm]
  · -- `m < p < 1`: the optimal `t = log (p (1 - m) / (m (1 - p)))`
    have hp0 : 0 < p := hm.trans hmp
    have h1p : 0 < 1 - p := sub_pos.2 hp1
    have h1m : 0 < 1 - m := sub_pos.2 hm1
    have hpos : 0 < p * (1 - m) / (m * (1 - p)) := by positivity
    have ht : 0 ≤ log (p * (1 - m) / (m * (1 - p))) :=
      log_nonneg ((one_le_div (by positivity)).2 (by nlinarith))
    refine (hbound _ ht).trans_eq ?_
    have h1 : 1 - m + m * exp (log (p * (1 - m) / (m * (1 - p))))
        = exp (log (1 - m) - log (1 - p)) := by
      rw [exp_log hpos, exp_sub, exp_log h1m, exp_log h1p]
      field_simp
      ring
    rw [h1, ← exp_nat_mul, ← exp_add, klBerReal_def]
    simp only [log_div, log_mul, hp0.ne', hm.ne', h1p.ne', h1m.ne', ne_eq, mul_eq_zero, or_self,
      not_false_eq_true]
    congr 1
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
  have h := measureReal_sum_ge_le_exp_klBerReal (X := fun i ω ↦ 1 - X i ω) (m := 1 - m)
    (p := 1 - p) (h_indep.comp (fun _ x ↦ 1 - x) fun _ ↦ measurable_const.sub measurable_id)
    (fun i hi ↦ aemeasurable_const.sub (hXm i hi))
    (fun i hi ↦ by
      filter_upwards [hX i hi] with ω hω using ⟨sub_nonneg.2 hω.2, sub_le_self _ hω.1⟩)
    (fun i hi ↦ by
      simp [integral_sub (integrable_const 1) (.of_mem_Icc 0 1 (hXm i hi) (hX i hi))]
      linarith [hmean i hi])
    (sub_pos.2 hm) ⟨sub_le_sub_left hp.2 1, sub_le_self _ hp.1⟩
  rw [klBerReal_one_sub_one_sub] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
  constructor <;> intro h <;> linarith

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

/-- If `X ∈ [0, 1]` almost surely and `E[X] ≥ 1`, then `X = 1` almost surely. -/
private lemma ae_eq_one_of_mem_Icc_of_one_le_integral [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc 0 1) (hmean : 1 ≤ μ[X]) :
    ∀ᵐ ω ∂μ, X ω = 1 := by
  have hint : Integrable X μ := .of_mem_Icc 0 1 hXm hX
  have h_nonneg : 0 ≤ᵐ[μ] fun ω ↦ 1 - X ω := by
    filter_upwards [hX] with ω hω using sub_nonneg.2 hω.2
  have h_zero : ∫ ω, (1 - X ω) ∂μ = 0 := by
    refine le_antisymm ?_ (integral_nonneg_of_ae h_nonneg)
    rw [integral_sub (integrable_const 1) hint]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae h_nonneg
    ((integrable_const 1).sub hint)).1 h_zero] with ω hω
  simp only [Pi.zero_apply] at hω
  linarith

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
    have h1 : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω = 1 := (eventually_all_finset s).2 fun i hi ↦
      ae_eq_one_of_mem_Icc_of_one_le_integral (hXm i hi) (hX i hi) (hm.trans (hmean i hi))
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

end LMLExplore
