/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import LMLExplore.Probability.Moments.Bernstein

/-!
# The empirical Bernstein inequality

Let `X i`, `i ∈ s`, be `n = #s ≥ 1` independent random variables with values in `[a, b]` and
common mean `m`, with empirical mean `X̂ = (∑ i ∈ s, X i) / n` and biased sample variance
`V = (∑ i ∈ s, (X i - X̂) ^ 2) / n`. The **empirical Bernstein inequality** [AMS09, Theorem 1]
states that for every `x`, with probability at least `1 - 3 exp (-x)`,
`|X̂ - m| < √(2 V x / n) + 3 (b - a) x / n`.

Bernstein's inequality bounds `|X̂ - m|` by `√(2 σ ^ 2 x / n) + (b - a) x / (3 n)`, where `σ ^ 2`
is the average variance of the `X i`, which is unknown to a statistician. The empirical form
replaces it by the observed `V`, at the price of a third deviation event and of a larger linear
term. Confidence intervals of this form adapt to the variance of the data, and variance-aware
exploration algorithms in bandits and reinforcement learning use them.

## Main statements

* `ProbabilityTheory.iIndepFun.measureReal_sqrt_add_le_abs_sum_div_card_sub_le`: the empirical
  Bernstein inequality, `P(√(2 V x / n) + 3 (b - a) x / n ≤ |X̂ - m|) ≤ 3 exp (-x)`.
* `ProbabilityTheory.iIndepFun.measureReal_sqrt_log_add_le_abs_sum_div_card_sub_le`: its form at
  confidence level `δ`, with `x = log (3 / δ)`.

## Implementation notes

The proof follows [AMS09, Appendix A.3]. Bernstein's inequality in high-probability form is
applied to the centred variables `X i - m` in both directions
(`ProbabilityTheory.iIndepFun.measureReal_sqrt_add_le_abs_sum_le_of_abs_le`), which controls
`|X̂ - m|` by the average variance `σ ^ 2`, and to `Var (X i) - (X i - m) ^ 2`
(`ProbabilityTheory.iIndepFun.measureReal_sqrt_add_le_sum_le_of_ae_le`), which bounds `σ ^ 2` from
above by the empirical second moment `V + (X̂ - m) ^ 2` around `m` up to a deviation term. Write
`w = b - a` for the width of the range. In the second application, Popoviciu's inequality
`Var (X i) ≤ w ^ 2 / 4` bounds the summands, and `|X i - m| ≤ w` bounds their second moments by
`E (X i - m) ^ 4 ≤ w ^ 2 Var (X i)`. Solving the resulting quadratic inequality in `σ` (the
"square-root trick") gives `σ ≤ √V + (15 / 8) w √(x / n)`, and the first bound then gives the
result, since `(15 / 8) √2 + 1 / 3 ≤ 3`.

[AMS09] uses a version of Bernstein's inequality without a linear term for the nonpositive
variables `-(X i - m) ^ 2`; the bounded summands used here instead add the term `w ^ 2 x / (12 n)`,
which the constant `3` still absorbs. The variables need not be identically distributed: they only
share their mean.

## References

* [AMS09] J.-Y. Audibert, R. Munos and Cs. Szepesvári, *Exploration–exploitation tradeoff using
  variance estimates in multi-armed bandits*, Theoretical Computer Science 410 (2009),
  1876–1902, Theorem 1.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ} {s : Finset ι}

namespace ProbabilityTheory.iIndepFun

/-- The deviation event of the empirical second moment around `m`, from Bernstein's inequality
for the centred variables `Var (X i) - (X i - m) ^ 2`: if `|X i - m| ≤ b` and
`E (X i - m) ^ 2 ≤ b ^ 2 / 4`, these are at most `b ^ 2 / 4`, and their second moments, the
variances of `(X i - m) ^ 2`, are at most `E (X i - m) ^ 4 ≤ b ^ 2 E (X i - m) ^ 2`. -/
private lemma measureReal_sqrt_add_le_sum_integral_sub_sum_sq_le (h_indep : iIndepFun X μ)
    {b m x : ℝ} (hb : 0 < b) (hX : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hXm : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω - m| ≤ b)
    (hqb : ∀ i ∈ s, ∫ ω, (X i ω - m) ^ 2 ∂μ ≤ b ^ 2 / 4) :
    μ.real {ω | √(2 * (b ^ 2 * ∑ i ∈ s, ∫ ω', (X i ω' - m) ^ 2 ∂μ) * x) + b ^ 2 / 4 * x / 3 ≤
      ∑ i ∈ s, ∫ ω', (X i ω' - m) ^ 2 ∂μ - ∑ i ∈ s, (X i ω - m) ^ 2} ≤ exp (-x) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  set q : ι → ℝ := fun i ↦ ∫ ω, (X i ω - m) ^ 2 ∂μ with hq_def
  have hZ : ∀ i ∈ s, ∀ᵐ ω ∂μ, 0 ≤ (X i ω - m) ^ 2 ∧ (X i ω - m) ^ 2 ≤ b ^ 2 := fun i hi ↦
    (hXm i hi).mono fun ω h ↦ ⟨sq_nonneg _, sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2⟩
  have hZL2 : ∀ i ∈ s, MemLp (fun ω ↦ (X i ω - m) ^ 2) 2 μ := fun i hi ↦
    memLp_of_bounded (hZ i hi) (((hX i hi).sub_const m).pow_const 2).aestronglyMeasurable 2
  have hZint : ∀ i ∈ s, Integrable (fun ω ↦ (X i ω - m) ^ 2) μ := fun i hi ↦
    (hZL2 i hi).integrable one_le_two
  have hW2 : ∀ i ∈ s, ∫ ω, (q i - (X i ω - m) ^ 2) ^ 2 ∂μ ≤ b ^ 2 * q i := fun i hi ↦ by
    have hvar := variance_eq_integral (hZL2 i hi).aestronglyMeasurable.aemeasurable
    calc ∫ ω, (q i - (X i ω - m) ^ 2) ^ 2 ∂μ
        = variance (fun ω ↦ (X i ω - m) ^ 2) μ := by
          rw [hvar]; exact integral_congr_ae (ae_of_all _ fun ω ↦ by simp only [hq_def]; ring)
      _ ≤ μ[(fun ω ↦ (X i ω - m) ^ 2) ^ 2] :=
          variance_le_expectation_sq (hZL2 i hi).aestronglyMeasurable
      _ ≤ ∫ ω, b ^ 2 * (X i ω - m) ^ 2 ∂μ := by
          refine integral_mono_ae ((hZL2 i hi).integrable_sq) ((hZint i hi).const_mul _) ?_
          filter_upwards [hZ i hi] with ω h
          simp only [Pi.pow_apply]
          nlinarith [h.1, h.2]
      _ = b ^ 2 * q i := integral_const_mul _ _
  have hE := (h_indep.comp (fun i y ↦ q i - (y - m) ^ 2)
    fun _ ↦ measurable_const.sub ((measurable_id.sub_const m).pow_const 2)
    ).measureReal_sqrt_add_le_sum_le_of_ae_le (X := fun i ω ↦ q i - (X i ω - m) ^ 2)
    (b := b ^ 2 / 4) (v := b ^ 2 * ∑ i ∈ s, q i) (L := x)
    (fun i hi ↦ (memLp_const _).sub (hZL2 i hi))
    (fun i hi ↦ by rw [integral_sub (integrable_const _) (hZint i hi)]; simp [hq_def])
    (by positivity) (fun i hi ↦ (hZ i hi).mono fun ω h ↦ by linarith [hqb i hi, h.1])
    (by rw [mul_sum]; exact sum_le_sum hW2)
  simpa only [sum_sub_distrib] using hE

/-- The square-root trick of the empirical Bernstein inequality, in the scale of sums: here `d`
stands for `|∑ i, (X i - m)|`, `σ ^ 2` for the sum of the variances, `u ^ 2` for the sum of the
squared deviations from the empirical mean, `r ^ 2` for the confidence parameter `x` and `k` for
`√2`. The first hypothesis is Bernstein's bound on the mean, the second is Bernstein's bound on
the empirical second moment `u ^ 2 + d ^ 2 / n` around `m`, and the third is Popoviciu's
inequality. -/
private lemma lt_of_sq_sub_lt {b n σ u r d k : ℝ} (hb : 0 < b) (hn : 0 < n) (hσ : 0 ≤ σ)
    (hu : 0 ≤ u) (hr : 0 ≤ r) (hd : 0 ≤ d) (hk0 : 0 ≤ k) (hk : k ^ 2 = 2)
    (h₁ : d < k * σ * r + b * r ^ 2 / 3)
    (h₂ : σ ^ 2 - (u ^ 2 + d ^ 2 / n) < k * b * σ * r + b ^ 2 * r ^ 2 / 12)
    (hpop : σ ^ 2 ≤ n * b ^ 2 / 4) :
    d < k * u * r + 3 * b * r ^ 2 := by
  have hk_lt : k < 1.415 := by nlinarith
  -- The square-root trick: `σ ≤ u + (15 / 8) b r`.
  have hsu : σ ≤ u + 15 / 8 * b * r := by
    rcases le_or_gt (16 / 225 * n) (r ^ 2) with hrn | hrn
    · -- For large `r`, Popoviciu's inequality alone gives `σ ≤ (15 / 8) b r`.
      have : σ ^ 2 ≤ (15 / 8 * b * r) ^ 2 := by nlinarith
      have := (pow_le_pow_iff_left₀ hσ (by positivity) two_ne_zero).1 this
      linarith
    · -- For small `r`, bound `d ^ 2 / n` through the first hypothesis.
      set P := σ * r with hP
      have hP0 : 0 ≤ P := mul_nonneg hσ hr
      have hPn : P ≤ 2 / 15 * b * n := by
        have : P ^ 2 ≤ (2 / 15 * b * n) ^ 2 := by
          rw [hP, mul_pow]
          calc σ ^ 2 * r ^ 2 ≤ n * b ^ 2 / 4 * (16 / 225 * n) := by gcongr
            _ = (2 / 15 * b * n) ^ 2 := by ring
        exact pow_le_pow_iff_left₀ hP0 (by positivity) two_ne_zero |>.1 this
      have hd2 : d ^ 2 ≤ 2 * P ^ 2 + 2 * k / 3 * b * P * r ^ 2 + b ^ 2 * r ^ 4 / 9 := by
        have : d ^ 2 ≤ (k * σ * r + b * r ^ 2 / 3) ^ 2 := pow_le_pow_left₀ hd h₁.le 2
        calc d ^ 2 ≤ (k * σ * r + b * r ^ 2 / 3) ^ 2 := this
          _ = 2 * P ^ 2 + 2 * k / 3 * b * P * r ^ 2 + b ^ 2 * r ^ 4 / 9 := by
            rw [hP]; linear_combination σ ^ 2 * r ^ 2 * hk
      have hdn : d ^ 2 / n ≤ (4 / 15 + 32 * k / 675) * b * P + 16 / 2025 * b ^ 2 * r ^ 2 := by
        rw [div_le_iff₀ hn]
        have h1 : 2 * P ^ 2 ≤ 4 / 15 * b * P * n := by nlinarith
        have h2 : 2 * k / 3 * b * P * r ^ 2 ≤ 32 * k / 675 * b * P * n := by
          have : 0 ≤ k * b * P := by positivity
          nlinarith
        have h3 : b ^ 2 * r ^ 4 / 9 ≤ 16 / 2025 * b ^ 2 * r ^ 2 * n := by
          have : 0 ≤ b ^ 2 * r ^ 2 := by positivity
          nlinarith
        nlinarith
      have hquad : σ ^ 2 ≤ u ^ 2 + 7 / 4 * b * σ * r + 1 / 10 * b ^ 2 * r ^ 2 := by
        have : 0 ≤ b * P := by positivity
        have : 0 ≤ b ^ 2 * r ^ 2 := by positivity
        nlinarith
      by_contra! hlt
      have hpos : 0 < σ - (u + 15 / 8 * b * r) := by linarith
      have hpos' : 0 < σ + (u + 15 / 8 * b * r) - 7 / 4 * b * r := by
        have : 0 ≤ b * r := by positivity
        linarith
      have : 0 ≤ b * r * u := by positivity
      nlinarith [mul_pos hpos hpos']
  -- Plug the bound on `σ` into the first hypothesis.
  have : 0 ≤ k * r := by positivity
  calc d < k * σ * r + b * r ^ 2 / 3 := h₁
    _ ≤ k * (u + 15 / 8 * b * r) * r + b * r ^ 2 / 3 := by gcongr
    _ = k * u * r + (15 / 8 * k + 1 / 3) * b * r ^ 2 := by ring
    _ ≤ k * u * r + 3 * b * r ^ 2 := by
        have : 0 ≤ b * r ^ 2 := by positivity
        nlinarith

/-- The deterministic step of the empirical Bernstein inequality: outside the deviation events of
Bernstein's inequality for the mean, in both directions, and for the empirical second moment
around `m`, the empirical mean of `f` is within `√(2 V x / n) + 3 b x / n` of `m`, where `V` is the
biased sample variance and `v`, the sum of the variances, satisfies Popoviciu's bound. -/
private lemma abs_sum_div_card_sub_lt {f : ι → ℝ} {b m x v : ℝ} (hs : s.Nonempty) (hb : 0 < b)
    (hx : 0 < x) (hv : 0 ≤ v) (hpop : v ≤ #s * b ^ 2 / 4)
    (h₁ : |∑ i ∈ s, (f i - m)| < √(2 * v * x) + b * x / 3)
    (h₃ : v - ∑ i ∈ s, (f i - m) ^ 2 < √(2 * (b ^ 2 * v) * x) + b ^ 2 / 4 * x / 3) :
    |(∑ i ∈ s, f i) / #s - m| <
      √(2 * ((∑ i ∈ s, (f i - (∑ j ∈ s, f j) / #s) ^ 2) / #s) * x / #s) + 3 * b * x / #s := by
  have hn : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  set S := ∑ i ∈ s, f i
  set A := ∑ i ∈ s, (f i - S / #s) ^ 2
  set D := S - #s * m with hD
  have hsumD : ∑ i ∈ s, (f i - m) = D := by rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  -- The second moment around `m` is the second moment around the mean plus `D ^ 2 / n`.
  have hsumQ : ∑ i ∈ s, (f i - m) ^ 2 = A + D ^ 2 / #s := by
    simp only [A, D, S, sub_sq, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
      sum_const, nsmul_eq_mul]
    field_simp
    ring
  rw [hsumD] at h₁
  rw [hsumQ] at h₃
  -- Square roots in terms of `k = √2`, `√v`, `√A` and `r = √x`.
  set k := √2
  set r := √x
  have hk2 : k ^ 2 = 2 := sq_sqrt zero_le_two
  have hr2 : r ^ 2 = x := sq_sqrt hx.le
  have hv2 : √v ^ 2 = v := sq_sqrt hv
  have hA2 : √A ^ 2 = A := sq_sqrt (sum_nonneg fun i _ ↦ sq_nonneg _)
  have hsq : ∀ {y z : ℝ}, 0 ≤ z → y = z ^ 2 → √y = z := fun hz h ↦ by rw [h, sqrt_sq hz]
  have e₁ : √(2 * v * x) = k * √v * r :=
    hsq (by positivity) (by rw [mul_pow, mul_pow, hk2, hv2, hr2])
  have e₃ : √(2 * (b ^ 2 * v) * x) = k * b * √v * r :=
    hsq (by positivity) (by rw [mul_pow, mul_pow, mul_pow, hk2, hv2, hr2]; ring)
  have e₀ : √(2 * (A / #s) * x / #s) = k * √A * r / #s :=
    hsq (by positivity) (by rw [div_pow, mul_pow, mul_pow, hk2, hA2, hr2]; field_simp)
  rw [e₁] at h₁
  rw [e₃] at h₃
  have hSD : S / #s - m = D / #s := by rw [hD]; field_simp
  -- The square-root trick bounds `|D|`, in terms of `x = r ^ 2`.
  have hmain : |D| < k * √A * r + 3 * b * x := by
    have := lt_of_sq_sub_lt hb hn (sqrt_nonneg v) (sqrt_nonneg A) (sqrt_nonneg x)
      (abs_nonneg D) (sqrt_nonneg 2) hk2 (by rwa [hr2])
      (by rw [hv2, sq_abs, hr2]; linarith) (by rw [hv2]; exact hpop)
    rwa [hr2] at this
  rw [e₀, hSD, abs_div, abs_of_pos hn]
  calc |D| / #s < (k * √A * r + 3 * b * x) / #s := div_lt_div_of_pos_right hmain hn
    _ = k * √A * r / #s + 3 * b * x / #s := by ring

/-- **The empirical Bernstein inequality** [AMS09, Theorem 1]. Let the `X i`, `i ∈ s`, be
`n = #s ≥ 1` independent random variables with values in `[a, b]` almost surely, `a < b`, and
with common mean `m`. Let `X̂ = (∑ i ∈ s, X i) / n` be their empirical mean and
`V = (∑ i ∈ s, (X i - X̂) ^ 2) / n` their biased sample variance. Then for every `x`,
`P(√(2 V x / n) + 3 (b - a) x / n ≤ |X̂ - m|) ≤ 3 exp (-x)`. -/
theorem measureReal_sqrt_add_le_abs_sum_div_card_sub_le (h_indep : iIndepFun X μ) {a b m x : ℝ}
    (hs : s.Nonempty) (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hab : a < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b) (hmean : ∀ i ∈ s, μ[X i] = m) :
    μ.real {ω | √(2 * ((∑ i ∈ s, (X i ω - (∑ j ∈ s, X j ω) / #s) ^ 2) / #s) * x / #s) +
      3 * (b - a) * x / #s ≤ |(∑ i ∈ s, X i ω) / #s - m|} ≤ 3 * exp (-x) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  rcases le_or_gt x 0 with hx | hx
  · exact measureReal_le_one.trans (by linarith [one_le_exp (neg_nonneg.2 hx)])
  have hw : 0 < b - a := sub_pos.2 hab
  have hL2 : ∀ i ∈ s, MemLp (X i) 2 μ := fun i hi ↦
    memLp_of_bounded (hXb i hi) (hX i hi).aestronglyMeasurable 2
  -- The common mean lies in `[a, b]`.
  obtain ⟨i₀, hi₀⟩ := hs
  have hma : a ≤ m := by
    rw [← hmean i₀ hi₀]
    calc a = ∫ _, a ∂μ := by simp
      _ ≤ μ[X i₀] := integral_mono_ae (integrable_const a)
          ((hL2 i₀ hi₀).integrable one_le_two) ((hXb i₀ hi₀).mono fun ω h ↦ h.1)
  have hmb : m ≤ b := by
    rw [← hmean i₀ hi₀]
    calc μ[X i₀] ≤ ∫ _, b ∂μ :=
          integral_mono_ae ((hL2 i₀ hi₀).integrable one_le_two) (integrable_const b)
            ((hXb i₀ hi₀).mono fun ω h ↦ h.2)
      _ = b := by simp
  have hXm : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω - m| ≤ b - a := fun i hi ↦ (hXb i hi).mono fun ω hω ↦ by
    rw [abs_le]; constructor <;> linarith [hω.1, hω.2]
  -- Popoviciu's inequality for the variances, and their sum `v`.
  have hqb : ∀ i ∈ s, ∫ ω, (X i ω - m) ^ 2 ∂μ ≤ (b - a) ^ 2 / 4 := fun i hi ↦ by
    have := variance_le_sq_of_bounded (hXb i hi) (hX i hi)
    rw [variance_eq_integral (hX i hi), hmean i hi] at this
    exact this.trans_eq (by ring)
  set v := ∑ i ∈ s, ∫ ω, (X i ω - m) ^ 2 ∂μ with hv_def
  have hv0 : 0 ≤ v := sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _
  have hpop : v ≤ #s * (b - a) ^ 2 / 4 := by
    calc v ≤ #s • ((b - a) ^ 2 / 4) := sum_le_card_nsmul _ _ _ hqb
      _ = #s * (b - a) ^ 2 / 4 := by rw [nsmul_eq_mul]; ring
  -- Bernstein's inequality for the centred variables `X i - m`, in both directions.
  have hE₁ := (h_indep.comp (fun _ y ↦ y - m) fun _ ↦ measurable_id.sub_const m
    ).measureReal_sqrt_add_le_abs_sum_le_of_abs_le (X := fun i ω ↦ X i ω - m) (v := v) (L := x)
    (fun i hi ↦ (hX i hi).sub_const m)
    (fun i hi ↦ by rw [integral_sub ((hL2 i hi).integrable one_le_two) (integrable_const m)];
                    simp [hmean i hi])
    hw hXm le_rfl
  have hE₂ := h_indep.measureReal_sqrt_add_le_sum_integral_sub_sum_sq_le (x := x) hw hX hXm hqb
  -- On the complement of the two deviation events, the square-root trick concludes.
  refine (measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)).trans <|
    ((measureReal_union_le _ _).trans (add_le_add hE₁ hE₂)).trans_eq (by ring)
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
  by_contra! h
  exact (abs_sum_div_card_sub_lt ⟨i₀, hi₀⟩ hw hx hv0 hpop h.1 h.2).not_ge hω

/-- **The empirical Bernstein inequality at confidence level `δ`** [AMS09, Theorem 1]. Under the
hypotheses of `measureReal_sqrt_add_le_abs_sum_div_card_sub_le`, for `δ > 0`, with probability at
least `1 - δ`, `|X̂ - m| < √(2 V log (3 / δ) / n) + 3 (b - a) log (3 / δ) / n`. -/
theorem measureReal_sqrt_log_add_le_abs_sum_div_card_sub_le (h_indep : iIndepFun X μ)
    {a b m δ : ℝ} (hs : s.Nonempty) (hX : ∀ i ∈ s, AEMeasurable (X i) μ) (hab : a < b)
    (hXb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b) (hmean : ∀ i ∈ s, μ[X i] = m) (hδ : 0 < δ) :
    μ.real {ω | √(2 * ((∑ i ∈ s, (X i ω - (∑ j ∈ s, X j ω) / #s) ^ 2) / #s) * log (3 / δ) / #s) +
      3 * (b - a) * log (3 / δ) / #s ≤ |(∑ i ∈ s, X i ω) / #s - m|} ≤ δ := by
  have hexp : 3 * exp (-log (3 / δ)) = δ := by
    rw [exp_neg, exp_log (by positivity)]
    field_simp
  simpa only [hexp] using
    h_indep.measureReal_sqrt_add_le_abs_sum_div_card_sub_le (x := log (3 / δ)) hs hX hab hXb
      hmean

end ProbabilityTheory.iIndepFun
