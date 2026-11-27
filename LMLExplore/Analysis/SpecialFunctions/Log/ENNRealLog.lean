/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.MeanInequalities
import LMLExplore.Data.EReal.Inv

/-!
# Bounds on the logarithm of extended nonnegative reals

## Main statements

* `ENNReal.log_ofReal_exp`: the logarithm of `exp x` is `x`.
* `ENNReal.log_le_log_add_of_div_le`: if `x / y ≤ exp c`, then `log x ≤ log y + c`.
* `ENNReal.le_neg_log_div_of_le_ofReal_exp`: for `0 < n`, if `x ≤ exp (-(n r))`, then
  `r ≤ -(log x) / n`.
* `ENNReal.neg_log_div_le_of_ofReal_exp_le`: for `0 < n`, if `exp (-(n r)) ≤ x`, then
  `-(log x) / n ≤ r`.
* `ENNReal.toENNReal_log_le_div_add`: for `0 < r < ∞`, `(log a)⁺ ≤ a / r + (log r)⁺`.
* `ENNReal.log_le_sub_one`: `log x ≤ x - 1` in `EReal`, for every `x : ℝ≥0∞`.
* `ENNReal.toENNReal_log_pow`: the positive part of `log (x ^ n)` is `n` times that of `log x`.
* `ENNReal.mul_log_add_mul_log_le_log`: the concavity of the logarithm on `ℝ≥0∞`,
  `s log x + t log y ≤ log (s x + t y)` for weights `s, t : ℝ≥0` of sum `1`.
* `ENNReal.le_prod_iff_toReal_log_le_sum`: for positive finite `c` and factors `x i`,
  `c ≤ ∏ i ∈ s, x i` if and only if `log c ≤ ∑ i ∈ s, log (x i)`, in `ℝ`. It turns the first time
  a product reaches a level into the first passage time of a random walk.
* `ENNReal.ofReal_add_sum_add_one_le_sum_add_div_prod`: the pathwise form
  `c + ∑ i, (log (x i))⁻ + 1 ≤ ∑ i, (log (x i))⁺ + exp c / ∏ i, x i` of `t + 1 ≤ exp t`, for
  `c ≥ 0`.
* `ENNReal.tendsto_toReal_log_inv_nhdsGT_zero`: the level `log (1/α)` tends to `∞` as `α → 0`.
* `ENNReal.limsup_div_toENNReal_log_inv_le`: a function bounded by `K + log (1/α) * r`, with `K`
  finite, has `limsup_{α → 0} f α / log (1/α) ≤ r`. This is the form of the bounds on the expected
  number of observations of a sequential test of level `α`.

## Implementation notes

`toENNReal_log_le_div_add` is adapted from the lemma of the same name in
`EValuesResearch/Results/TTestGrowAux.lean` (commit `562b62e`) of the paper project
`RemyDegenne/evalues_research`.
-/

public section

open Filter Topology
open scoped ENNReal NNReal

namespace ENNReal

/-- The logarithm of `exp x`, as an extended nonnegative real, is `x`. It is not a simp lemma:
simp rewrites its left-hand side with `ENNReal.log_ofReal` first. -/
lemma log_ofReal_exp (x : ℝ) : log (ENNReal.ofReal (Real.exp x)) = x := by
  rw [log_ofReal_of_pos (Real.exp_pos x), Real.log_exp]

/-- If `x / y ≤ exp c`, then `log x ≤ log y + c`. -/
lemma log_le_log_add_of_div_le {x y : ℝ≥0∞} {c : ℝ}
    (h : x / y ≤ ENNReal.ofReal (Real.exp c)) : log x ≤ log y + c := by
  rcases eq_or_ne y ∞ with rfl | hy
  · simp
  rcases eq_or_ne y 0 with rfl | hy0
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · simp [ENNReal.div_zero hx0] at h
  have hle : x ≤ ENNReal.ofReal (Real.exp c) * y :=
    (ENNReal.div_le_iff hy0 hy).1 h
  calc log x ≤ log (ENNReal.ofReal (Real.exp c) * y) := log_le_log hle
  _ = log y + c := by
    rw [log_mul_add, log_ofReal_exp, add_comm]

/-- For `0 < n`, an `x` at most `exp (-(n r))` has `r ≤ -(log x) / n`. -/
lemma le_neg_log_div_of_le_ofReal_exp {x : ℝ≥0∞} {n : ℕ} {r : ℝ} (hn : 0 < n)
    (h : x ≤ ENNReal.ofReal (Real.exp (-(n * r)))) : (r : EReal) ≤ -log x / (n : EReal) := by
  have hlog := log_le_log h
  rw [log_ofReal_exp, EReal.coe_neg] at hlog
  rw [EReal.coe_le_div_natCast_iff hn]
  exact EReal.le_neg_of_le_neg hlog

/-- For `0 < n`, an `x` at least `exp (-(n r))` has `-(log x) / n ≤ r`. -/
lemma neg_log_div_le_of_ofReal_exp_le {x : ℝ≥0∞} {n : ℕ} {r : ℝ} (hn : 0 < n)
    (h : ENNReal.ofReal (Real.exp (-(n * r))) ≤ x) : -log x / (n : EReal) ≤ r := by
  have hlog := log_le_log h
  rw [log_ofReal_exp, EReal.coe_neg] at hlog
  rw [EReal.div_natCast_le_coe_iff hn]
  exact EReal.neg_le_of_neg_le hlog

/-- For `0 < r < ∞`, the positive part of `log a` is at most `a / r + (log r)⁺`: this is
`log (a / r) ≤ a / r - 1`. -/
lemma toENNReal_log_le_div_add {a r : ℝ≥0∞} (hr0 : 0 < r) (hr : r ≠ ∞) :
    (log a).toENNReal ≤ a / r + ENNReal.ofReal (Real.log r.toReal) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  rcases eq_or_ne a ∞ with rfl | hatop
  · simp [ENNReal.top_div_of_ne_top hr]
  have hr' : 0 < r.toReal := ENNReal.toReal_pos hr0.ne' hr
  have ha' : 0 < a.toReal := ENNReal.toReal_pos ha0 hatop
  rw [log_pos_real ha0 hatop, EReal.real_coe_toENNReal,
    ← ENNReal.ofReal_toReal (ENNReal.div_ne_top hatop hr0.ne'), ENNReal.toReal_div]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
  have h1 : Real.log a.toReal = Real.log (a.toReal / r.toReal) + Real.log r.toReal := by
    rw [Real.log_div ha'.ne' hr'.ne', sub_add_cancel]
  have h2 := Real.log_le_sub_one_of_pos (div_pos ha' hr')
  linarith

/-- `log x ≤ x - 1` in `EReal`, for every `x : ℝ≥0∞`; at `0` the left side is `⊥`, and at `∞`
both sides are `⊤`. -/
lemma log_le_sub_one (x : ℝ≥0∞) : log x ≤ (x : EReal) - 1 := by
  by_cases h0 : x = 0
  · simp [h0]
  by_cases htop : x = ∞
  · simp only [htop, log_top, EReal.coe_ennreal_top]
    exact (EReal.top_sub_coe 1).ge
  rw [log_pos_real h0 htop, ← EReal.coe_ennreal_toReal htop, ← EReal.coe_one, ← EReal.coe_sub,
    EReal.coe_le_coe_iff]
  exact Real.log_le_sub_one_of_pos (ENNReal.toReal_pos h0 htop)

/-- The positive part of `log (x ^ n)` is `n` times the positive part of `log x`. -/
lemma toENNReal_log_pow (x : ℝ≥0∞) (n : ℕ) : (log (x ^ n)).toENNReal = n * (log x).toENNReal := by
  rw [log_pow, EReal.toENNReal_mul (by positivity), ← ENNReal.toEReal_natCast, EReal.toENNReal_coe]

/-- **The concavity of the logarithm** on `ℝ≥0∞`: for weights `s, t : ℝ≥0` of sum `1`,
`s log x + t log y ≤ log (s x + t y)` in `EReal`, for all `x, y : ℝ≥0∞`. A zero weight cancels
an infinite logarithm, as `0 * ⊥ = 0` in `EReal`. -/
lemma mul_log_add_mul_log_le_log {s t : ℝ≥0} (hst : s + t = 1) (x y : ℝ≥0∞) :
    ((s : ℝ) : EReal) * log x + ((t : ℝ) : EReal) * log y ≤ log (s * x + t * y) := by
  rw [← log_rpow, ← log_rpow, ← log_mul_add]
  exact log_monotone (geom_mean_le_arith_mean2_weighted s t x y hst)

/-- For a positive finite `c` and positive finite factors `x i`, `c ≤ ∏ i ∈ s, x i` if and only if
`log c ≤ ∑ i ∈ s, log (x i)`, with the logarithms taken in `ℝ`. -/
lemma le_prod_iff_toReal_log_le_sum {ι : Type*} {s : Finset ι} {x : ι → ℝ≥0∞}
    (hx : ∀ i ∈ s, x i ≠ 0 ∧ x i ≠ ∞) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    c ≤ ∏ i ∈ s, x i ↔ (log c).toReal ≤ ∑ i ∈ s, (log (x i)).toReal := by
  -- a positive finite `y` is `exp (log y)`, with the logarithm in `ℝ`
  have hexp {y : ℝ≥0∞} (h0 : y ≠ 0) (htop : y ≠ ∞) :
      y = ENNReal.ofReal (Real.exp (log y).toReal) := by
    rw [← log_eq_iff, log_ofReal_exp, EReal.coe_toReal (by simpa using htop) (by simpa using h0)]
  conv_lhs => rw [Finset.prod_congr rfl fun i hi ↦ hexp (hx i hi).1 (hx i hi).2, hexp hc0 hc]
  rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Real.exp_sum,
    ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le, Real.exp_le_exp]

/-- **A pathwise form of `t + 1 ≤ exp t`.** For nonzero factors `x i` and `c ≥ 0`,
`c + ∑ i ∈ s, (log (x i))⁻ + 1 ≤ ∑ i ∈ s, (log (x i))⁺ + exp c / ∏ i ∈ s, x i`, with the positive
and negative parts of the logarithms kept apart so that the inequality lives in `ℝ≥0∞`. -/
lemma ofReal_add_sum_add_one_le_sum_add_div_prod {ι : Type*} {s : Finset ι} {x : ι → ℝ≥0∞}
    (hx0 : ∀ i ∈ s, x i ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    ENNReal.ofReal c + ∑ i ∈ s, (-log (x i)).toENNReal + 1 ≤
      ∑ i ∈ s, (log (x i)).toENNReal + ENNReal.ofReal (Real.exp c) / ∏ i ∈ s, x i := by
  by_cases htop : ∃ i ∈ s, x i = ⊤
  · obtain ⟨i, hi, hit⟩ := htop
    have hsum : ∑ i ∈ s, (log (x i)).toENNReal = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨i, hi, by simp [hit]⟩
    simp [hsum]
  simp only [not_exists, not_and] at htop
  set l : ι → ℝ := fun i ↦ Real.log (x i).toReal with hl
  have hlog : ∀ i ∈ s, log (x i) = (l i : EReal) := fun i hi ↦
    log_pos_real (hx0 i hi) (htop i hi)
  have hofmax (r : ℝ) : ENNReal.ofReal r = ENNReal.ofReal (max r 0) := by
    rcases le_total r 0 with h | h
    · simp [ENNReal.ofReal_of_nonpos h, max_eq_right h]
    · simp [max_eq_left h]
  have h1 : ∑ i ∈ s, (log (x i)).toENNReal = ENNReal.ofReal (∑ i ∈ s, max (l i) 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ le_max_right _ _]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hlog i hi, EReal.real_coe_toENNReal, hofmax]
  have h2 : ∑ i ∈ s, (-log (x i)).toENNReal = ENNReal.ofReal (∑ i ∈ s, max (-l i) 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ le_max_right _ _]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hlog i hi, ← EReal.coe_neg, EReal.real_coe_toENNReal, hofmax]
  have h3 : ∏ i ∈ s, x i = ENNReal.ofReal (Real.exp (∑ i ∈ s, l i)) := by
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [hl, Real.exp_log (ENNReal.toReal_pos (hx0 i hi) (htop i hi)),
      ENNReal.ofReal_toReal (htop i hi)]
  have hL : ∑ i ∈ s, l i = ∑ i ∈ s, max (l i) 0 - ∑ i ∈ s, max (-l i) 0 := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (max_zero_sub_max_neg_zero_eq_self _).symm
  have hA : 0 ≤ ∑ i ∈ s, max (l i) 0 := Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  have hB : 0 ≤ ∑ i ∈ s, max (-l i) 0 := Finset.sum_nonneg fun i _ ↦ le_max_right _ _
  rw [h1, h2, h3, ← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hc hB,
    ← ENNReal.ofReal_add (by positivity) zero_le_one,
    ← ENNReal.ofReal_add hA (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Real.add_one_le_exp (c - ∑ i ∈ s, l i)
  rw [hL] at this ⊢
  linarith

/-- The level `log (1/α)`, in `ℝ`, tends to `∞` as `α` tends to `0` from above. -/
lemma tendsto_toReal_log_inv_nhdsGT_zero :
    Tendsto (fun α : ℝ≥0∞ ↦ (log α⁻¹).toReal) (𝓝[>] 0) atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  have hM : (0 : ℝ≥0∞) < (ENNReal.ofReal (Real.exp M))⁻¹ := ENNReal.inv_pos.2 ENNReal.ofReal_ne_top
  filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hM), self_mem_nhdsWithin]
    with α hα (hα0 : 0 < α)
  -- `exp M ≤ α⁻¹`, so `M ≤ log α⁻¹`
  have hle : (M : EReal) ≤ log α⁻¹ := by
    rw [← log_ofReal_exp M, log_le_log_iff, ENNReal.le_inv_iff_le_inv]
    exact hα.le
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal (by simpa using hα0.ne')
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot M) hle)]
  exact hle

/-- A function bounded by `K + log (1/α) * r` on `(0, 1)`, with `K` finite, has
`limsup_{α → 0} f α / log (1/α) ≤ r`: the constant `K` is negligible against the level
`log (1/α)`, which tends to `∞`. -/
lemma limsup_div_toENNReal_log_inv_le {f : ℝ≥0∞ → ℝ≥0∞} {K r : ℝ≥0∞} (hK : K ≠ ∞)
    (hf : ∀ α, 0 < α → α < 1 → f α ≤ K + (log α⁻¹).toENNReal * r) :
    limsup (fun α ↦ f α / (log α⁻¹).toENNReal) (𝓝[>] 0) ≤ r := by
  set B : ℝ≥0∞ → ℝ≥0∞ := fun α ↦ (log α⁻¹).toENNReal
  have hB : Tendsto B (𝓝[>] 0) (𝓝 ⊤) := by
    have h : Continuous B :=
      EReal.continuous_toENNReal.comp (continuous_log.comp continuous_inv)
    simpa [B] using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun α ↦ K / B α + r) (𝓝[>] 0) (𝓝 r) := by
    have h := (ENNReal.Tendsto.const_mul (tendsto_inv_iff.2 hB) (.inr hK)).add_const r
    simpa [div_eq_mul_inv] using h
  have hbound : ∀ᶠ α in 𝓝[>] (0 : ℝ≥0∞), f α / B α ≤ K / B α + r := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with α ⟨hα0, hα1⟩
    have hB0 : B α ≠ 0 :=
      EReal.toENNReal_ne_zero_iff.2 (zero_lt_log_iff.2 (ENNReal.one_lt_inv.2 hα1))
    have hBtop : B α ≠ ⊤ := by simpa [B] using hα0.ne'
    calc f α / B α
    _ ≤ (K + B α * r) / B α := by gcongr; exact hf α hα0 hα1
    _ = K / B α + r := by
      rw [ENNReal.add_div, mul_comm, ENNReal.mul_div_cancel_right hB0 hBtop]
  calc limsup (fun α ↦ f α / B α) (𝓝[>] 0)
  _ ≤ limsup (fun α ↦ K / B α + r) (𝓝[>] 0) := limsup_le_limsup hbound
  _ = r := hlim.limsup_eq

end ENNReal
