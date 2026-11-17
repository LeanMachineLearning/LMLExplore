/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Filtration
import LMLExplore.MeasureTheory.Measure.Real
import LMLExplore.Probability.Martingale.Hoeffding
import TauCeti.Probability.Independence.CondExp

/-!
# Online-to-batch conversions with high probability

An online learner is run on the losses `f (·) (ξ t)` of a stream of data `ξ t`. Its plays `x t`
are predictable for a filtration `ℱ` (`x t` is `ℱ t`-measurable), the datum `ξ t` is
`ℱ (t + 1)`-measurable, and the loss `f` takes values in `[0, 1]`. The risk `F` is the conditional
mean of the loss given the past: `μ[f (x t) (ξ t) | ℱ t] = F (x t)` almost everywhere. This file
turns the regret of the learner into bounds on the risks of its plays that hold with
probability at least `1 - δ`.

* The average risk of the plays exceeds their average loss by at most `√(log (1 / δ) / (2 n))`.
  This needs no regret bound: `F (x t) - f (x t) (ξ t)` is a martingale difference whose range,
  `[F (x t) - 1, F (x t)]`, has width `1` and is known before `ξ t` is drawn [CCG04].
* If the regret of the plays against a fixed comparator `u` is at most `R` along almost every
  path, as for a deterministic learner with a regret bound on every loss sequence, then the
  average risk of the plays is at most `F u + R / n + √(2 log (1 / δ) / n)`.
* For a convex risk on a convex set of plays, the same bound holds for the risk of the average
  play, by Jensen's inequality.

The hypothesis on the risk is a statement about the conditional mean at the play, because the
play is random: a conditional mean `μ[f y (ξ t) | ℱ t] = F y` for each fixed `y` has a null set
depending on `y`, and does not determine the conditional mean at `x t`. When `ξ t` is independent
of `ℱ t` with law `ρ`, the risk is `F y = ∫ z, f y z ∂ρ` and the hypothesis holds by freezing the
play (`condExp_ae_eq_integral_of_indep`, from
`TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep`); this is the setting of
[Ora, Theorem 3.10].

The concentration step is the Azuma–Hoeffding inequality around conditional means,
`LMLExplore.measureReal_le_sum_condExp_sub_le`. For the comparator bound it is applied once to
`f (x t) (ξ t) - f u (ξ t)`, with values in `[-1, 1]`, rather than twice to `f (x t) (ξ t)` and
`f u (ξ t)` with a union bound. This gives `√(2 log (1 / δ) / n)`, which improves both
`√(2 log (2 / δ) / n)` (two bounds with ranges of width `1`) and the constant
`2 √(2 log (2 / δ) / n)` of [Ora, Theorem 3.10] (two bounds with increments bounded by `1`).

## Main statements

* `LMLExplore.OnlineLearning.measureReal_le_sum_sub_le`: the Azuma–Hoeffding bound
  `P(ε ≤ ∑ t < n, (F (x t) - f (x t) (ξ t))) ≤ exp (-2 ε ^ 2 / n)`.
* `LMLExplore.OnlineLearning.measureReal_le_abs_sum_sub_le`: its two-sided form
  `P(ε ≤ |∑ t < n, (F (x t) - f (x t) (ξ t))|) ≤ 2 exp (-2 ε ^ 2 / n)`.
* `LMLExplore.OnlineLearning.condExp_ae_eq_integral_of_indep`: for a datum independent of the past
  with law `ρ`, the conditional mean of the loss at a known play is `∫ z, f (x t) z ∂ρ`.
* `LMLExplore.OnlineLearning.measureReal_sum_div_add_sqrt_lt_sum_div_le`: with probability at least
  `1 - δ`, `(∑ t < n, F (x t)) / n ≤ (∑ t < n, f (x t) (ξ t)) / n + √(log (1 / δ) / (2 n))`.
* `LMLExplore.OnlineLearning.measureReal_add_div_add_sqrt_lt_sum_div_le`: with probability at
  least `1 - δ`, `(∑ t < n, F (x t)) / n ≤ F u + R / n + √(2 log (1 / δ) / n)`.
* `LMLExplore.OnlineLearning.measureReal_add_div_add_sqrt_lt_apply_smul_sum_le`: the same bound
  for `F` of the average play `(n : ℝ)⁻¹ • ∑ t < n, x t`, for `F` convex on a convex set
  containing the plays.
* `LMLExplore.OnlineLearning.measureReal_add_div_add_sqrt_lt_sum_div_le_of_indep`: the comparator
  bound for data independent of the past with a common law `ρ`, and the risk
  `F y = ∫ z, f y z ∂ρ`.

## References

* [CCG04] N. Cesa-Bianchi, A. Conconi and C. Gentile, *On the generalization ability of on-line
  learning algorithms*, IEEE Transactions on Information Theory 50 (2004), 2050–2057.
* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Theorem 3.10.
-/

public section

open MeasureTheory ProbabilityTheory Real Finset

namespace LMLExplore.OnlineLearning

variable {Ω α Z : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {mα : MeasurableSpace α} {mZ : MeasurableSpace Z}
  {f : α → Z → ℝ} {F : α → ℝ} {x : ℕ → Ω → α} {ξ : ℕ → Ω → Z} {n : ℕ} {ε δ R : ℝ}

/-- The loss at a comparator `y` known at time `t` is known at time `t + 1`. -/
private lemma measurable_loss (hf : Measurable (Function.uncurry f)) {t : ℕ} {y : Ω → α}
    (hy : Measurable[ℱ t] y) (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t)) :
    Measurable[ℱ (t + 1)] fun ω ↦ f (y ω) (ξ t ω) :=
  hf.comp ((hy.mono (ℱ.mono t.le_succ) le_rfl).prodMk (hξ t))

/-- A loss at a comparator `y` known at time `t` is integrable. -/
private lemma integrable_loss (hf : Measurable (Function.uncurry f))
    (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) {t : ℕ} {y : Ω → α} (hy : Measurable[ℱ t] y)
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t)) : Integrable (fun ω ↦ f (y ω) (ξ t ω)) μ :=
  Integrable.of_mem_Icc 0 1 ((measurable_loss hf hy hξ).mono (ℱ.le _) le_rfl).aemeasurable
    (ae_of_all _ fun _ ↦ hf01 _ _)

/-- For the deviation `ε = n √(c log (1 / δ) / n)`, the Azuma–Hoeffding bound
`exp (-2 ε ^ 2 / (n (2 c)))` is `δ`. -/
private lemma exp_neg_two_mul_sq_mul_sqrt_div_eq {c : ℝ} (hc : 0 < c) (hn : n ≠ 0) (hδ : 0 < δ)
    (hδ1 : δ < 1) : exp (-2 * ((n : ℝ) * √(c * log (1 / δ) / n)) ^ 2 / (n * (2 * c))) = δ := by
  have hL : 0 ≤ log (1 / δ) := log_nonneg (one_le_one_div hδ hδ1.le)
  have hn' : (0 : ℝ) < n := by positivity
  rw [mul_pow, sq_sqrt (by positivity), one_div, log_inv]
  field_simp
  exact exp_log hδ

/-- **Freezing a known play.** If the datum `ξ t` is independent of `ℱ t` with law `ρ`, then given
`ℱ t` the conditional mean of the loss at an `ℱ t`-measurable play `y` is the risk
`∫ z, f (y ω) z ∂ρ` at the play: the play is frozen and the datum keeps its law. -/
theorem condExp_ae_eq_integral_of_indep {ρ : Measure Z} (hf : Measurable (Function.uncurry f))
    (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) {t : ℕ} {y : Ω → α} (hy : Measurable[ℱ t] y)
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t)) (hindep : Indep (mZ.comap (ξ t)) (ℱ t) μ)
    (hρ : μ.map (ξ t) = ρ) :
    μ[fun ω ↦ f (y ω) (ξ t ω) | ℱ t] =ᵐ[μ] fun ω ↦ ∫ z, f (y ω) z ∂ρ := by
  have h := TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep (ℱ.le t) hy
    ((hξ t).mono (ℱ.le _) le_rfl) hindep hf.stronglyMeasurable (integrable_loss hf hf01 hy hξ)
  simpa only [Function.uncurry_apply_pair, hρ] using h

/-- **Azuma–Hoeffding bound for the risks of the plays.** For a loss `f` with values in `[0, 1]`
whose conditional mean at the play `x t` given `ℱ t` is the risk `F (x t)`, and `ε ≥ 0`,
`P(ε ≤ ∑ t < n, (F (x t) - f (x t) (ξ t))) ≤ exp (-2 ε ^ 2 / n)`. -/
theorem measureReal_le_sum_sub_le (hf : Measurable (Function.uncurry f))
    (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) (hx : ∀ t, Measurable[ℱ t] (x t))
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hF : ∀ t < n, μ[fun ω ↦ f (x t ω) (ξ t ω) | ℱ t] =ᵐ[μ] fun ω ↦ F (x t ω))
    (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ t ∈ range n, (F (x t ω) - f (x t ω) (ξ t ω))} ≤
      exp (-2 * ε ^ 2 / n) := by
  have h := measureReal_le_sum_condExp_sub_le (ℱ := ℱ) (μ := μ)
    (X := fun t ω ↦ f (x t ω) (ξ t ω)) (a := fun _ ↦ 0) (b := fun _ ↦ 1)
    (fun t ↦ measurable_loss hf (hx t) hξ) n (fun t _ ↦ ae_of_all _ fun ω ↦ hf01 _ _) hε
  simp only [sub_zero, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  refine (measureReal_congr ?_).trans_le h
  filter_upwards [(Filter.eventually_all_finset _).2 fun t ht ↦ hF t (mem_range.1 ht)] with ω hω
  simp only [sum_congr rfl fun t ht ↦ congrArg (· - f (x t ω) (ξ t ω)) (hω t ht)]

/-- **Two-sided Azuma–Hoeffding bound for the risks of the plays.** For a loss `f` with values in
`[0, 1]` whose conditional mean at the play `x t` given `ℱ t` is the risk `F (x t)`, and `ε ≥ 0`,
`P(ε ≤ |∑ t < n, (F (x t) - f (x t) (ξ t))|) ≤ 2 exp (-2 ε ^ 2 / n)`. -/
theorem measureReal_le_abs_sum_sub_le (hf : Measurable (Function.uncurry f))
    (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) (hx : ∀ t, Measurable[ℱ t] (x t))
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hF : ∀ t < n, μ[fun ω ↦ f (x t ω) (ξ t ω) | ℱ t] =ᵐ[μ] fun ω ↦ F (x t ω))
    (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ t ∈ range n, (F (x t ω) - f (x t ω) (ξ t ω))|} ≤
      2 * exp (-2 * ε ^ 2 / n) := by
  have h := measureReal_le_abs_sum_condExp_sub_le (ℱ := ℱ) (μ := μ)
    (X := fun t ω ↦ f (x t ω) (ξ t ω)) (a := fun _ ↦ 0) (b := fun _ ↦ 1)
    (fun t ↦ measurable_loss hf (hx t) hξ) n (fun t _ ↦ ae_of_all _ fun ω ↦ hf01 _ _) hε
  simp only [sub_zero, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one] at h
  refine (measureReal_congr ?_).trans_le h
  filter_upwards [(Filter.eventually_all_finset _).2 fun t ht ↦ hF t (mem_range.1 ht)] with ω hω
  simp only [sum_congr rfl fun t ht ↦ congrArg (· - f (x t ω) (ξ t ω)) (hω t ht)]

/-- **Online-to-batch with high probability, with no regret bound** [CCG04]. For a loss `f` with
values in `[0, 1]` whose conditional mean at the play `x t` given `ℱ t` is the risk `F (x t)`,
and `δ > 0`, the event
`(∑ t < n, f (x t) (ξ t)) / n + √(log (1 / δ) / (2 n)) < (∑ t < n, F (x t)) / n` has probability
at most `δ`. -/
theorem measureReal_sum_div_add_sqrt_lt_sum_div_le (hf : Measurable (Function.uncurry f))
    (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) (hx : ∀ t, Measurable[ℱ t] (x t))
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hF : ∀ t < n, μ[fun ω ↦ f (x t ω) (ξ t ω) | ℱ t] =ᵐ[μ] fun ω ↦ F (x t ω)) (hδ : 0 < δ) :
    μ.real {ω | (∑ t ∈ range n, f (x t ω) (ξ t ω)) / n + √(log (1 / δ) / (2 * n)) <
      (∑ t ∈ range n, F (x t ω)) / n} ≤ δ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hδ.le]
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  have hn' : (0 : ℝ) < n := by positivity
  rw [show log (1 / δ) / (2 * n) = 2⁻¹ * log (1 / δ) / n by ring]
  refine (measureReal_mono fun ω hω ↦ ?_).trans
    ((measureReal_le_sum_sub_le hf hf01 hx hξ hF (ε := n * √(2⁻¹ * log (1 / δ) / n))
      (by positivity)).trans_eq ?_)
  · simp only [Set.mem_ofPred_eq, sum_sub_distrib] at hω ⊢
    rw [← lt_sub_iff_add_lt', ← sub_div, lt_div_iff₀ hn'] at hω
    linarith
  · simpa only [mul_inv_cancel₀ (two_ne_zero (α := ℝ)), mul_one] using
      exp_neg_two_mul_sq_mul_sqrt_div_eq (c := 2⁻¹) (by norm_num) hn hδ hδ1

/-- **Online-to-batch with high probability** [Ora, Theorem 3.10]. Let `f` be a loss with values
in `[0, 1]`, `F` its conditional mean given the past at the plays `x t` and at a fixed comparator
`u`, and suppose that the regret of the plays against `u` on the losses `f (·) (ξ t)` is at most
`R` along almost every path, as for a deterministic learner with a regret bound on every loss
sequence. Then for `n ≠ 0` and `δ > 0`, the event
`F u + R / n + √(2 log (1 / δ) / n) < (∑ t < n, F (x t)) / n` has probability at most `δ`.

The constant improves the `2 √(2 log (2 / δ) / n)` of [Ora, Theorem 3.10]. -/
theorem measureReal_add_div_add_sqrt_lt_sum_div_le (hf : Measurable (Function.uncurry f))
    (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1) (hx : ∀ t, Measurable[ℱ t] (x t))
    (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hF : ∀ t < n, μ[fun ω ↦ f (x t ω) (ξ t ω) | ℱ t] =ᵐ[μ] fun ω ↦ F (x t ω)) (u : α)
    (hu : ∀ t < n, μ[fun ω ↦ f u (ξ t ω) | ℱ t] =ᵐ[μ] fun _ ↦ F u)
    (hR : ∀ᵐ ω ∂μ, ∑ t ∈ range n, (f (x t ω) (ξ t ω) - f u (ξ t ω)) ≤ R) (hn : n ≠ 0)
    (hδ : 0 < δ) :
    μ.real {ω | F u + R / n + √(2 * log (1 / δ) / n) < (∑ t ∈ range n, F (x t ω)) / n} ≤ δ := by
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  have hn' : (0 : ℝ) < n := by positivity
  -- The excess loss over the comparator, with values in `[-1, 1]`, and its conditional mean.
  set X : ℕ → Ω → ℝ := fun t ω ↦ f (x t ω) (ξ t ω) - f u (ξ t ω)
  have hmean (t : ℕ) (ht : t < n) : μ[X t | ℱ t] =ᵐ[μ] fun ω ↦ F (x t ω) - F u := by
    have hXt : X t = (fun ω ↦ f (x t ω) (ξ t ω)) - fun ω ↦ f u (ξ t ω) := by
      simp only [X, Pi.sub_def]
    filter_upwards [condExp_sub (m := ℱ t) (integrable_loss hf hf01 (hx t) hξ)
      (integrable_loss hf hf01 measurable_const hξ), hF t ht, hu t ht] with ω h1 h2 h3
    rw [hXt, h1, Pi.sub_apply, h2, h3]
  have h := measureReal_le_sum_condExp_sub_le (ℱ := ℱ) (μ := μ) (X := X) (a := fun _ ↦ -1)
    (b := fun _ ↦ 1)
    (fun t ↦ (measurable_loss hf (hx t) hξ).sub (measurable_loss hf measurable_const hξ)) n
    (fun t _ ↦ ae_of_all _ fun ω ↦ ⟨by linarith [(hf01 (x t ω) (ξ t ω)).1, (hf01 u (ξ t ω)).2],
      by linarith [(hf01 (x t ω) (ξ t ω)).2, (hf01 u (ξ t ω)).1]⟩)
    (ε := n * √(2 * log (1 / δ) / n)) (by positivity)
  refine (measureReal_mono_ae ?_).trans (h.trans_eq ?_)
  · filter_upwards [hR, (Filter.eventually_all_finset _).2 fun t ht ↦ hmean t (mem_range.1 ht)]
      with ω hRω hω hbad
    rw [sum_sub_distrib, sum_congr rfl hω, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rw [lt_div_iff₀ hn'] at hbad
    have hRn : R / n * n = R := div_mul_cancel₀ _ hn'.ne'
    have hX : ∑ t ∈ range n, X t ω ≤ R := by simpa only [X] using hRω
    linarith
  · simp only [sum_const, card_range, nsmul_eq_mul]
    rw [show ((1 : ℝ) - -1) ^ 2 = 2 * 2 by norm_num]
    exact exp_neg_two_mul_sq_mul_sqrt_div_eq two_pos hn hδ hδ1

/-- **Online-to-batch with high probability, for the average play** [Ora, Theorem 3.10]. Under
the hypotheses of `measureReal_add_div_add_sqrt_lt_sum_div_le`, if moreover the plays lie in a
convex set `V` on which the risk `F` is convex, then the event
`F u + R / n + √(2 log (1 / δ) / n) < F ((n : ℝ)⁻¹ • ∑ t < n, x t)` has probability at most
`δ`. -/
theorem measureReal_add_div_add_sqrt_lt_apply_smul_sum_le {E : Type*} [AddCommGroup E]
    [Module ℝ E] {mE : MeasurableSpace E} {f : E → Z → ℝ} {F : E → ℝ} {x : ℕ → Ω → E} {V : Set E}
    (hf : Measurable (Function.uncurry f)) (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1)
    (hx : ∀ t, Measurable[ℱ t] (x t)) (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hF : ∀ t < n, μ[fun ω ↦ f (x t ω) (ξ t ω) | ℱ t] =ᵐ[μ] fun ω ↦ F (x t ω)) (u : E)
    (hu : ∀ t < n, μ[fun ω ↦ f u (ξ t ω) | ℱ t] =ᵐ[μ] fun _ ↦ F u)
    (hR : ∀ᵐ ω ∂μ, ∑ t ∈ range n, (f (x t ω) (ξ t ω) - f u (ξ t ω)) ≤ R)
    (hFV : ConvexOn ℝ V F) (hxV : ∀ᵐ ω ∂μ, ∀ t < n, x t ω ∈ V) (hn : n ≠ 0) (hδ : 0 < δ) :
    μ.real {ω | F u + R / n + √(2 * log (1 / δ) / n) <
      F ((n : ℝ)⁻¹ • ∑ t ∈ range n, x t ω)} ≤ δ := by
  refine (measureReal_mono_ae ?_).trans
    (measureReal_add_div_add_sqrt_lt_sum_div_le hf hf01 hx hξ hF u hu hR hn hδ)
  filter_upwards [hxV] with ω hω hbad
  refine hbad.trans_le ?_
  -- Jensen's inequality for the uniform weights `1 / n`.
  have h := hFV.map_sum_le (t := range n) (w := fun _ ↦ (n : ℝ)⁻¹) (p := fun t ↦ x t ω)
    (fun _ _ ↦ by positivity) (by simp [hn]) fun t ht ↦ hω t (mem_range.1 ht)
  rw [← smul_sum, ← smul_sum, smul_eq_mul, inv_mul_eq_div] at h
  exact h

/-- **Online-to-batch with high probability for independent data** [Ora, Theorem 3.10]. If each
datum `ξ t` is independent of `ℱ t` with law `ρ`, the loss `f` has values in `[0, 1]`, and the
regret of the plays against a fixed comparator `u` is at most `R` along almost every path, then
for the risk `F y = ∫ z, f y z ∂ρ`, `n ≠ 0` and `δ > 0`, the event
`F u + R / n + √(2 log (1 / δ) / n) < (∑ t < n, F (x t)) / n` has probability at most `δ`. -/
theorem measureReal_add_div_add_sqrt_lt_sum_div_le_of_indep {ρ : Measure Z}
    (hf : Measurable (Function.uncurry f)) (hf01 : ∀ y z, f y z ∈ Set.Icc 0 1)
    (hx : ∀ t, Measurable[ℱ t] (x t)) (hξ : ∀ t, Measurable[ℱ (t + 1)] (ξ t))
    (hindep : ∀ t, Indep (mZ.comap (ξ t)) (ℱ t) μ) (hρ : ∀ t, μ.map (ξ t) = ρ) (u : α)
    (hR : ∀ᵐ ω ∂μ, ∑ t ∈ range n, (f (x t ω) (ξ t ω) - f u (ξ t ω)) ≤ R) (hn : n ≠ 0)
    (hδ : 0 < δ) :
    μ.real {ω | (∫ z, f u z ∂ρ) + R / n + √(2 * log (1 / δ) / n) <
      (∑ t ∈ range n, ∫ z, f (x t ω) z ∂ρ) / n} ≤ δ :=
  measureReal_add_div_add_sqrt_lt_sum_div_le (F := fun y ↦ ∫ z, f y z ∂ρ) hf hf01 hx hξ
    (fun t _ ↦ condExp_ae_eq_integral_of_indep hf hf01 (hx t) hξ (hindep t) (hρ t)) u
    (fun t _ ↦ condExp_ae_eq_integral_of_indep hf hf01 measurable_const hξ (hindep t) (hρ t)) hR
    hn hδ

end LMLExplore.OnlineLearning
