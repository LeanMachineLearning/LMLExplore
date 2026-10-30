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

## Main statements

* `LMLExplore.mgf_le_one_sub_add_mul_exp`: for `X ∈ [0, 1]` a.s. with `E[X] ≤ m` and `t ≥ 0`,
  `mgf X μ t ≤ 1 - m + m exp t`.
* `LMLExplore.measureReal_sum_ge_le_exp_klBerReal`: the upper tail
  `P(#s * p ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(p, m)))` for `0 < m ≤ p ≤ 1`.
* `LMLExplore.measureReal_sum_le_le_exp_klBerReal`: the lower tail
  `P(∑ i ∈ s, X i ≤ #s * p) ≤ exp (-(#s * d(p, m)))` for `0 ≤ p ≤ m < 1`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Lemma 10.3 and Note 10.3.1.
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
  have hint_exp : Integrable (fun ω ↦ exp (t * X ω)) μ := by
    refine .of_mem_Icc 0 (exp t) (measurable_exp.comp_aemeasurable (hXm.const_mul t)) ?_
    filter_upwards [hX] with ω hω
    exact ⟨(exp_pos _).le, exp_le_exp.2 (mul_le_of_le_one_right ht hω.2)⟩
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

/-- **Chernoff bound in relative-entropy form, upper tail** ([LS, Lemma 10.3 and Note 10.3.1]):
for independent random variables `X i ∈ [0, 1]` with means at most `m > 0`, and `p ∈ [m, 1]`,
`P(#s * p ≤ ∑ i ∈ s, X i) ≤ exp (-(#s * d(p, m)))`. -/
theorem measureReal_sum_ge_le_exp_klBerReal {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {s : Finset ι} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc 0 1) (hmean : ∀ i ∈ s, μ[X i] ≤ m) (hm : 0 < m)
    (hp : p ∈ Set.Icc m 1) :
    μ.real {ω | #s * p ≤ ∑ i ∈ s, X i ω} ≤ exp (-(#s * klBerReal p m)) := by
  have := h_indep.isProbabilityMeasure
  -- the Chernoff bound at every `t ≥ 0`
  have hbound (t : ℝ) (ht : 0 ≤ t) : μ.real {ω | #s * p ≤ ∑ i ∈ s, X i ω}
      ≤ exp (-t * (#s * p)) * (1 - m + m * exp t) ^ #s := by
    have hX' : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω ∈ Set.Icc 0 1 := (eventually_all_finset s).2 hX
    have hint : Integrable (fun ω ↦ exp (t * ∑ i ∈ s, X i ω)) μ := by
      refine .of_mem_Icc 0 (exp (t * #s)) (measurable_exp.comp_aemeasurable
        ((Finset.aemeasurable_fun_sum s hXm).const_mul t)) ?_
      filter_upwards [hX'] with ω hω
      refine ⟨(exp_pos _).le, exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ ht)⟩
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
  rcases hp.1.eq_or_lt with rfl | hmp
  · rw [klBerReal_self, mul_zero, neg_zero, exp_zero]
    exact measureReal_le_one
  have hm1 : m < 1 := hmp.trans_le hp.2
  rcases hp.2.eq_or_lt with rfl | hp1
  · -- `p = 1`: let `t → ∞` in the Chernoff bound
    have heq (t : ℝ) : exp (-t * (#s * 1)) * (1 - m + m * exp t) ^ #s
        = ((1 - m) * exp (-t) + m) ^ #s := by
      rw [mul_one, mul_comm (-t), exp_nat_mul, ← mul_pow, exp_neg]
      congr 1
      field_simp
    have hlim : Tendsto (fun t ↦ ((1 - m) * exp (-t) + m) ^ #s) atTop (𝓝 (m ^ #s)) := by
      simpa using ((tendsto_exp_neg_atTop_nhds_zero.const_mul (1 - m)).add_const m).pow #s
    refine (ge_of_tendsto hlim ((eventually_ge_atTop 0).mono fun t ht ↦
      (hbound t ht).trans_eq (heq t))).trans_eq ?_
    rw [klBerReal_def, sub_self, zero_mul, add_zero, one_mul, one_div, log_inv, mul_neg, neg_neg,
      exp_nat_mul, exp_log hm]
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
    rw [h1, ← exp_nat_mul, ← exp_add, klBerReal_def, log_div hp0.ne' hm.ne',
      log_div h1p.ne' h1m.ne', log_div (mul_pos hp0 h1m).ne' (mul_pos hm h1p).ne',
      log_mul hp0.ne' h1m.ne', log_mul hm.ne' h1p.ne']
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
      rw [integral_sub (integrable_const 1) (.of_mem_Icc 0 1 (hXm i hi) (hX i hi)),
        integral_const, probReal_univ, smul_eq_mul, mul_one]
      linarith [hmean i hi])
    (sub_pos.2 hm) ⟨sub_le_sub_left hp.2 1, sub_le_self _ hp.1⟩
  rw [klBerReal_one_sub_one_sub] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
  constructor <;> intro h <;> linarith

end LMLExplore
