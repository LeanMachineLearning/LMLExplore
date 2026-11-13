/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Moments.Variance
import LMLExplore.Algebra.Order.Ring.Abs
import LMLExplore.Analysis.Convex.Integral
import LMLExplore.Analysis.SpecialFunctions.Exp
import LMLExplore.Probability.Moments.Bernstein
import LMLExplore.Probability.Moments.Variance
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# Transport of means and variances under a Kullback–Leibler constraint

If `KL(μ ‖ ν) ≤ a`, the mean of a function under `μ` is close to its mean under `ν`, at a
Bernstein-type distance governed by the variance under `ν`: for `f` with values in an interval of
length `b`,
`|∫ f ∂μ - ∫ f ∂ν| ≤ √(2 Var_ν(f) a) + b a / 3`.
This is the form in which a confidence region `{p | KL(p̂ ‖ p) ≤ a}` around an empirical law `p̂`
controls the means of value functions, in the analysis of optimistic exploration algorithms. It
also transports variances: `Var_ν(f) ≤ 2 Var_μ(f) + (8 / 3) b² a` and
`Var_μ(f) ≤ 2 Var_ν(f) + (5 / 6) b² a`.

The proof combines the Donsker–Varadhan inequality
`∫ g ∂μ - log ∫ exp g ∂ν ≤ KL(μ ‖ ν)` (Tau Ceti's
`TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`), applied to `g = t (f - ∫ f ∂ν)`, with
Bennett's bound on the moment-generating function of the centred function
(`MeasureTheory.MemLp.mgf_le_exp_mul_exp_sub_one_sub_of_ae_le`). Its sub-gamma form
`exp x - 1 - x ≤ x² / (2 (1 - x / 3))` then inverts in closed form, as in the high-probability form
of Bernstein's inequality [BLM13, Theorem 2.10]
(`Real.exists_pos_le_mul_sqrt_add_sub_mul_exp_sub_one_sub`).

The statements, their order and the decomposition into [MDJKLV21, Lemmas 10 and 11] are adapted
from the paper project Essakine2026Tight (`github.com/RemyDegenne/Essakine2026Tight`, file
`Essakine2026Tight/ForLMLExplore/InformationTheory/KLBernstein.lean`, by Rémy Degenne,
Apache 2.0), with a new proof of the transport of the mean and sharper constants.

## Main statements

* `LMLExplore.absolutelyContinuous_of_klDiv_ne_top`: a finite `KL(μ ‖ ν)` gives `μ ≪ ν`.
* `LMLExplore.integral_sub_integral_le_of_klDiv_le`: the one-sided transport, for `f` bounded
  above by its `ν`-mean plus `b`.
* `LMLExplore.abs_integral_sub_integral_le_of_klDiv_le`: the two-sided transport for `f` with
  values in `[c, d]` [TM18], [MDJKLV21, Lemma 10].
* `LMLExplore.variance_le_two_mul_variance_add_of_klDiv_le` and
  `LMLExplore.variance_le_two_mul_variance_add_of_klDiv_le'`: the transport of variances
  [MDJKLV21, Lemma 11].

The sources state the two-sided transport with `2 b a / 3` in place of `b a / 3`, and the
transport of variances with `4 b² a`; the constants here are sharper.

## References

* [BLM13] S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford
  University Press, 2013.
* [TM18] M. S. Talebi and O.-A. Maillard, *Variance-aware regret bounds for undiscounted
  reinforcement learning in MDPs*, ALT 2018.
* [MDJKLV21] P. Ménard, O. D. Domingues, A. Jonsson, E. Kaufmann, E. Leurent and M. Valko,
  *Fast active learning for pure exploration in reinforcement learning*, ICML 2021.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real

open scoped ENNReal

namespace LMLExplore

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν] {f : α → ℝ} {a b c d : ℝ}

/-- A finite Kullback–Leibler divergence `KL(μ ‖ ν) ≠ ∞` gives `μ ≪ ν`. -/
theorem absolutelyContinuous_of_klDiv_ne_top {μ ν : Measure α} (h : klDiv μ ν ≠ ∞) : μ ≪ ν :=
  (klDiv_ne_top_iff.1 h).1

/-- The Donsker–Varadhan inequality at `g = t (f - ∫ f ∂ν)`, with Bennett's bound on the
moment-generating function: for every `t ≥ 0`,
`t (∫ f ∂μ - ∫ f ∂ν) - Var_ν(f) ψ_b(t) ≤ a`, with `ψ_b(t) = (exp (t b) - 1 - t b) / b²`. -/
private lemma mul_sub_le_of_klDiv_le (hfν : MemLp f 2 ν) (hfμ : Integrable f μ) (hb : 0 < b)
    (hfb : ∀ᵐ x ∂ν, f x - ν[f] ≤ b) (ha : 0 ≤ a) (h : klDiv μ ν ≤ ENNReal.ofReal a) {t : ℝ}
    (ht : 0 ≤ t) :
    t * (∫ x, f x ∂μ - ∫ x, f x ∂ν) - Var[f; ν] * ((exp (t * b) - 1 - t * b) / b ^ 2) ≤ a := by
  set Y := fun x ↦ f x - ν[f]
  have hY : MemLp Y 2 ν := hfν.sub (memLp_const _)
  have hmean : ν[Y] = 0 := by
    simp [Y, integral_sub (hfν.integrable one_le_two) (integrable_const _)]
  have hexp : Integrable (fun x ↦ exp (t * Y x)) ν :=
    integrable_exp_mul_of_le t b ht hY.aestronglyMeasurable.aemeasurable hfb
  have hmgf := hY.mgf_le_exp_mul_exp_sub_one_sub_of_ae_le hmean.le hb hfb ht
  rw [← variance_eq_integral hfν.aestronglyMeasurable.aemeasurable] at hmgf
  have hDV := TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv (μ := μ) (ν := ν)
    (f := fun x ↦ t * Y x) ((hfμ.sub (integrable_const _)).const_mul t) hexp
  have hDV' : ∫ x, t * Y x ∂μ - log (mgf Y ν t) ≤ a :=
    (ENNReal.ofReal_le_ofReal_iff ha).1 (hDV.trans h)
  have hint : ∫ x, t * Y x ∂μ = t * (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
    simp [Y, integral_const_mul, integral_sub hfμ (integrable_const _)]
  have hlog := (log_le_log (mgf_pos hexp) hmgf).trans_eq (log_exp _)
  linarith

/-- `integral_sub_integral_le_of_klDiv_le` for `b > 0`. -/
private lemma integral_sub_integral_le_of_klDiv_le_of_pos (hfν : MemLp f 2 ν)
    (hfμ : Integrable f μ) (hb : 0 < b) (hfb : ∀ᵐ x ∂ν, f x - ν[f] ≤ b) (ha : 0 ≤ a)
    (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ √(2 * Var[f; ν] * a) + b * a / 3 := by
  set D := ∫ x, f x ∂μ - ∫ x, f x ∂ν
  set v := Var[f; ν]
  have key {t : ℝ} (ht : 0 ≤ t) := mul_sub_le_of_klDiv_le hfν hfμ hb hfb ha h ht
  rcases ha.eq_or_lt with rfl | ha'
  · -- `KL(μ ‖ ν) = 0` forces `μ = ν`
    have hμν : μ = ν := klDiv_eq_zero_iff.1 (le_antisymm (by simpa using h) zero_le)
    simp [D, hμν]
  rcases (variance_nonneg f ν).eq_or_lt with hv | hv
  · -- zero variance: `t D ≤ a` for every `t ≥ 0`, so `D ≤ 0`
    by_contra! hD
    have hD0 : 0 < D := lt_of_le_of_lt (by positivity) hD
    have := key (t := (a + 1) / D) (by positivity)
    rw [← hv, div_mul_cancel₀ _ hD0.ne'] at this
    linarith
  -- Chernoff's choice of `t`, at which `t (√(2 v a) + b a / 3) - v ψ_b(t)` is at least `a`
  obtain ⟨t, ht, hta⟩ := exists_pos_le_mul_sqrt_add_sub_mul_exp_sub_one_sub hb hv ha'
  have hkey := key ht.le
  exact le_of_mul_le_mul_left (by linarith) ht

/-- **Transport of the mean under a Kullback–Leibler constraint**, one-sided form: if
`KL(μ ‖ ν) ≤ a` and `f ≤ ∫ f ∂ν + b` holds `ν`-almost everywhere, then
`∫ f ∂μ - ∫ f ∂ν ≤ √(2 Var_ν(f) a) + b a / 3`. -/
theorem integral_sub_integral_le_of_klDiv_le (hfν : MemLp f 2 ν) (hfμ : Integrable f μ)
    (hfb : ∀ᵐ x ∂ν, f x - ν[f] ≤ b) (ha : 0 ≤ a) (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ √(2 * Var[f; ν] * a) + b * a / 3 := by
  -- the bound `b` is nonnegative, as `f - ∫ f ∂ν` has mean zero
  have hb : 0 ≤ b := by
    have hint := integral_mono_ae (hfν.integrable one_le_two |>.sub (integrable_const _))
      (integrable_const b) hfb
    simpa [integral_sub (hfν.integrable one_le_two) (integrable_const _)] using hint
  -- the case `b = 0` is the limit of the bounds for `b + 3 ε / (a + 1)`, `ε > 0`
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hε' : 0 < 3 * ε / (a + 1) := by positivity
  have := integral_sub_integral_le_of_klDiv_le_of_pos hfν hfμ (b := b + 3 * ε / (a + 1))
    (by positivity) (hfb.mono fun x hx ↦ by linarith) ha h
  have hle : 3 * ε / (a + 1) * a / 3 ≤ ε := by
    rw [div_mul_eq_mul_div, div_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith [show (b + 3 * ε / (a + 1)) * a / 3 = b * a / 3 + 3 * ε / (a + 1) * a / 3 by ring]

/-- **Transport of the mean under a Kullback–Leibler constraint** [TM18], [MDJKLV21, Lemma 10]:
if `KL(μ ‖ ν) ≤ a` and `f` has values in `[c, d]` `ν`-almost everywhere, then
`|∫ f ∂μ - ∫ f ∂ν| ≤ √(2 Var_ν(f) a) + (d - c) a / 3`. -/
theorem abs_integral_sub_integral_le_of_klDiv_le (hfm : AEStronglyMeasurable f ν)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc c d) (ha : 0 ≤ a) (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ √(2 * Var[f; ν] * a) + (d - c) * a / 3 := by
  have hμν : μ ≪ ν :=
    absolutelyContinuous_of_klDiv_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have hfν : MemLp f 2 ν := memLp_of_bounded hf hfm 2
  have hfμ : Integrable f μ :=
    .of_mem_Icc c d (hfm.mono_ac hμν).aemeasurable (hμν.ae_le hf)
  have hm : ν[f] ∈ Set.Icc c d := integral_mem_Icc_of_ae_mem_Icc hfm.aemeasurable hf
  have hup := integral_sub_integral_le_of_klDiv_le hfν hfμ (b := d - c)
    (hf.mono fun x hx ↦ by linarith [hx.2, hm.1]) ha h
  have hdown := integral_sub_integral_le_of_klDiv_le (f := fun x ↦ -f x) hfν.neg hfμ.neg
    (b := d - c) (hf.mono fun x hx ↦ by rw [integral_neg]; linarith [hx.1, hm.2]) ha h
  rw [variance_fun_neg, integral_neg, integral_neg] at hdown
  rw [abs_sub_le_iff]
  exact ⟨hup, by linarith⟩

/-- The transport of the mean for a function with values in `[0, B]`, with the variance bounded
by `B` times the mean: `|∫ g ∂μ - ∫ g ∂ν| ≤ √(2 B (∫ g ∂ν) a) + B a / 3`. -/
private lemma abs_integral_sub_integral_le_of_klDiv_le_of_nonneg {g : α → ℝ} {B : ℝ}
    (hgm : AEStronglyMeasurable g ν) (hg : ∀ᵐ x ∂ν, g x ∈ Set.Icc 0 B) (ha : 0 ≤ a)
    (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    |∫ x, g x ∂μ - ∫ x, g x ∂ν| ≤ √(2 * (B * ∫ x, g x ∂ν) * a) + B * a / 3 := by
  have hvar := variance_le_mul_integral_sub hgm.aemeasurable hg
  simp only [sub_zero] at hvar
  refine (abs_integral_sub_integral_le_of_klDiv_le hgm hg ha h).trans ?_
  simp only [sub_zero]
  gcongr

/-- **Transport of the variance under a Kullback–Leibler constraint** [MDJKLV21, Lemma 11]: if
`KL(μ ‖ ν) ≤ a` and `f` has values in `[c, d]` `ν`-almost everywhere, then
`Var_ν(f) ≤ 2 Var_μ(f) + (8 / 3) (d - c)² a`. -/
theorem variance_le_two_mul_variance_add_of_klDiv_le (hfm : AEStronglyMeasurable f ν)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc c d) (ha : 0 ≤ a) (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    Var[f; ν] ≤ 2 * Var[f; μ] + 8 / 3 * (d - c) ^ 2 * a := by
  have hμν : μ ≪ ν :=
    absolutelyContinuous_of_klDiv_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have hfμ : ∀ᵐ x ∂μ, f x ∈ Set.Icc c d := hμν.ae_le hf
  have hm : μ[f] ∈ Set.Icc c d :=
    integral_mem_Icc_of_ae_mem_Icc (hfm.mono_ac hμν).aemeasurable hfμ
  -- the square `g = (f - ∫ f ∂μ) ^ 2` has values in `[0, (d - c) ^ 2]`
  have hg : ∀ᵐ x ∂ν, (f x - μ[f]) ^ 2 ∈ Set.Icc 0 ((d - c) ^ 2) :=
    hf.mono fun _ hx ↦ sq_sub_mem_Icc_of_mem_Icc hx hm
  have hT := abs_integral_sub_integral_le_of_klDiv_le_of_nonneg (μ := μ)
    (by fun_prop) hg ha h
  rw [← variance_eq_integral (hfm.mono_ac hμν).aemeasurable] at hT
  set x := ∫ y, (f y - μ[f]) ^ 2 ∂ν
  have hx : Var[f; ν] ≤ x := variance_le_integral_sub_sq hfm _
  have hx0 : 0 ≤ x := integral_nonneg_of_ae (hg.mono fun _ hy ↦ hy.1)
  -- `√(2 (d - c)² x a) ≤ x / 2 + (d - c)² a`
  have hsq : √(2 * ((d - c) ^ 2 * x) * a) ≤ x / 2 + (d - c) ^ 2 * a := by
    rw [sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (x / 2 - (d - c) ^ 2 * a)]
  linarith [(abs_le.1 hT).1]

/-- **Transport of the variance under a Kullback–Leibler constraint**, the other direction
[MDJKLV21, Lemma 11]: if `KL(μ ‖ ν) ≤ a` and `f` has values in `[c, d]` `ν`-almost everywhere,
then `Var_μ(f) ≤ 2 Var_ν(f) + (5 / 6) (d - c)² a`. -/
theorem variance_le_two_mul_variance_add_of_klDiv_le' (hfm : AEStronglyMeasurable f ν)
    (hf : ∀ᵐ x ∂ν, f x ∈ Set.Icc c d) (ha : 0 ≤ a) (h : klDiv μ ν ≤ ENNReal.ofReal a) :
    Var[f; μ] ≤ 2 * Var[f; ν] + 5 / 6 * (d - c) ^ 2 * a := by
  have hμν : μ ≪ ν :=
    absolutelyContinuous_of_klDiv_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
  have hm : ν[f] ∈ Set.Icc c d := integral_mem_Icc_of_ae_mem_Icc hfm.aemeasurable hf
  -- the square `g = (f - ∫ f ∂ν) ^ 2` has values in `[0, (d - c) ^ 2]`
  have hg : ∀ᵐ x ∂ν, (f x - ν[f]) ^ 2 ∈ Set.Icc 0 ((d - c) ^ 2) :=
    hf.mono fun _ hx ↦ sq_sub_mem_Icc_of_mem_Icc hx hm
  have hT := abs_integral_sub_integral_le_of_klDiv_le_of_nonneg (μ := μ)
    (by fun_prop) hg ha h
  rw [← variance_eq_integral hfm.aemeasurable] at hT
  have hx : Var[f; μ] ≤ ∫ y, (f y - ν[f]) ^ 2 ∂μ := variance_le_integral_sub_sq (hfm.mono_ac hμν) _
  have hv := variance_nonneg f ν
  -- `√(2 (d - c)² Var_ν(f) a) ≤ Var_ν(f) + (d - c)² a / 2`
  have hsq : √(2 * ((d - c) ^ 2 * Var[f; ν]) * a) ≤ Var[f; ν] + (d - c) ^ 2 * a / 2 := by
    rw [sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (Var[f; ν] - (d - c) ^ 2 * a / 2)]
  linarith [(abs_le.1 hT).2]

end LMLExplore
