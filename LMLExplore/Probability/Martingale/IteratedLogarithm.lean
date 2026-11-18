/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.MinMulSubLogLog
public import LMLExplore.Probability.Martingale.RateFunction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ZetaValues

/-!
# Time-uniform self-normalized deviations with an iterated-logarithm correction

Let `ℱ` be a filtration on a standard Borel space, `X` a real process with `X k`
`ℱ (k + 1)`-measurable, and `w` a process of selection indicators in `{0, 1}` adapted to `ℱ`.
After `t` rounds, `N t = ∑ k < t, w k` variables have been selected, with mean `μ̂ t`. Suppose that,
given `ℱ k`, the moment generating function of `X k` is bounded by that of a real random variable
`Y` with mean `m` and rate function `I`. For an arm of a bandit, `w k` indicates that the arm is
pulled at round `k`, and `N t I(μ̂ t)` is the self-normalized deviation of its empirical mean;
for rewards dominated by a member of an exponential family it is the generalized likelihood ratio
statistic `N t dbar(μ̂ t, μ)`. This file bounds that deviation at all rounds simultaneously, with a
threshold growing like `3 log (1 + log N t)`, as Kaufmann and Koolen [KK21] do for one arm: for
every real `x`,
`P(∃ t, 1 ≤ N t, 2 H_{3/2}((x + log (2 ζ(2))) / 2) + 3 log (1 + log N t) ≤ N t I(μ̂ t)) ≤ e^{-x}`
[KK21, Corollary 31], where `H_z(x) = min_{y ∈ (1, z]} y (x - log log y)` is
`LMLExplore.minMulSubLogLog` and `2 ζ(2) = π² / 3`; with `ζ(2)` in place of `2 ζ(2)` for the
deviations on one side of the mean.

The bound comes from peeling the numbers of selected variables along the geometric grid of ratio
`c > 1`, with a weight for each slice. On the slice `c ^ k ≤ N t < c ^ (k + 1)` the time-uniform
Chernoff bound of `LMLExplore.measure_exists_le_sum_and_gt_and_lt_rateFunction_le` bounds the
probability that `x + c log (κ (k + 1) ^ 2) ≤ N t I(μ̂ t)` by
`exp (-x / c) / (κ (k + 1) ^ 2)`, and `∑ k, 1 / (k + 1) ^ 2 = π ^ 2 / 6` (Mathlib's
`hasSum_zeta_two`). Since `k + 1 ≤ 1 + log (N t) / log c` on that slice, the threshold
`x + c log (κ (1 + log (N t) / log c) ^ 2)` is exceeded with probability at most
`π ^ 2 / (6 κ) exp (-x / c)` above the mean, and as much below. For `c ∈ (1, 3/2]`,
`c log (κ (1 + log N / log c) ^ 2) ≤ c log (κ / log² c) + 3 log (1 + log N)`, which gives the
deviation bound of [KK21, Lemma 13]: the threshold `x + c log (C(c)) + 3 log (1 + log N t)`, with
`C(c) = 2 ζ(2) / log² c`, is exceeded with probability at most `exp (-x / c)`. Kaufmann and Koolen
obtain it from a mixture over the slices of the exponential supermartingales; the union bound over
the slices gives the same probability. Minimizing the threshold over `c` gives [KK21, Corollary 31].

## Main statements

* `LMLExplore.measure_exists_gt_and_add_mul_log_le_mul_rateFunction_le`,
  `LMLExplore.measure_exists_lt_and_add_mul_log_le_mul_rateFunction_le`,
  `LMLExplore.measure_exists_add_mul_log_le_mul_rateFunction_le`: the weighted peeling bound
  `P(∃ t, 1 ≤ N t, x + c log (κ (1 + log (N t) / log c) ^ 2) ≤ N t I(μ̂ t))`
  `≤ π ^ 2 / (6 κ) exp (-x / c)` above and below the mean, and twice that on both sides.
* `LMLExplore.measure_exists_add_three_mul_log_le_mul_rateFunction_le` [KK21, Lemma 13]: for
  `c ∈ (1, 3/2]` and every real `x`,
  `P(∃ t, 1 ≤ N t, x + c log (2 ζ(2) / log² c) + 3 log (1 + log N t) ≤ N t I(μ̂ t)) ≤ exp (-x / c)`,
  and `LMLExplore.measure_exists_gt_and_add_three_mul_log_le_mul_rateFunction_le`,
  `LMLExplore.measure_exists_lt_and_add_three_mul_log_le_mul_rateFunction_le` with `ζ(2)` for one
  side of the mean.
* `LMLExplore.measure_exists_two_mul_minMulSubLogLog_add_le_mul_rateFunction_le`
  [KK21, Corollary 31]: for every real `x`,
  `P(∃ t, 1 ≤ N t, 2 H_{3/2}((x + log (2 ζ(2))) / 2) + 3 log (1 + log N t) ≤ N t I(μ̂ t)) ≤ e^{-x}`,
  and `LMLExplore.measure_exists_gt_and_two_mul_minMulSubLogLog_add_le_mul_rateFunction_le`,
  `LMLExplore.measure_exists_lt_and_two_mul_minMulSubLogLog_add_le_mul_rateFunction_le` with
  `ζ(2)` for one side of the mean.

## References

* [KK21] E. Kaufmann and W. M. Koolen, *Mixture martingales revisited with applications to
  sequential tests and confidence intervals*, JMLR 22 (2021), Lemma 13 and Corollary 31.
-/

public section

open MeasureTheory ProbabilityTheory Finset Real Set

open scoped ENNReal

namespace LMLExplore

/-- The thresholds `x + c log (κ y ^ 2)` are positive for `x > 0`, `c ≥ 0`, `κ ≥ 1` and `y ≥ 1`. -/
private lemma add_mul_log_pos {c κ x y : ℝ} (hc : 0 ≤ c) (hκ : 1 ≤ κ) (hx : 0 < x) (hy : 1 ≤ y) :
    0 < x + c * log (κ * y ^ 2) :=
  add_pos_of_pos_of_nonneg hx
    (mul_nonneg hc (log_nonneg (one_le_mul_of_one_le_of_one_le hκ (one_le_pow₀ hy))))

/-- The weights `exp (-(x + c log (κ (k + 1) ^ 2)) / c) = exp (-x / c) / (κ (k + 1) ^ 2)` of the
slices sum to `π ^ 2 / (6 κ) exp (-x / c)`. -/
private lemma hasSum_exp_neg_add_mul_log_div {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) (x : ℝ) :
    HasSum (fun k : ℕ ↦ exp (-((x + c * log (κ * ((k : ℝ) + 1) ^ 2)) / c)))
      (π ^ 2 / (6 * κ) * exp (-(x / c))) := by
  have h_zeta : HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using h
  convert h_zeta.mul_left (exp (-(x / c)) / κ) using 1
  · ext k
    have hk : 0 < κ * ((k : ℝ) + 1) ^ 2 := by positivity
    simp only [add_div, mul_div_cancel_left₀ _ hc.ne', neg_add, exp_add, exp_neg, exp_log hk]
    field_simp
  · field_simp

/-- For `c ∈ (1, 3/2]`, `κ > 0` and `N ≥ 1`, the threshold of the weighted peeling is at most the
threshold of [KK21, Lemma 13]:
`c log (κ (1 + log N / log c) ^ 2) ≤ c log (κ / log² c) + 3 log (1 + log N)`. -/
private lemma mul_log_le_mul_log_add_three_mul_log {c κ N : ℝ} (hc : 1 < c) (hc' : c ≤ 3 / 2)
    (hκ : 0 < κ) (hN : 1 ≤ N) :
    c * log (κ * (1 + log N / log c) ^ 2) ≤ c * log (κ / log c ^ 2) + 3 * log (1 + log N) := by
  have hlc : 0 < log c := log_pos hc
  have hlN : 0 ≤ log N := log_nonneg hN
  have hlc1 : log c ≤ 1 := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h_eq : κ * (1 + log N / log c) ^ 2 = κ / log c ^ 2 * (log c + log N) ^ 2 := by
    field_simp
  rw [h_eq, log_mul (by positivity) (by positivity), log_pow]
  -- it remains to see `2 c log (log c + log N) ≤ 3 log (1 + log N)`, from `2 c ≤ 3`
  have hle : log (log c + log N) ≤ log (1 + log N) := log_le_log (by positivity) (by linarith)
  have h0 : 0 ≤ log (1 + log N) := log_nonneg (by linarith)
  push_cast
  rcases le_total (log (log c + log N)) 0 with h | h <;> nlinarith

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} [IsProbabilityMeasure Q]
  {ℱ : Filtration ℕ mΩ} {X w : ℕ → Ω → ℝ} {Y : Ω' → ℝ} {c κ x : ℝ}

/-- **Weighted peeling bound for the self-normalized deviations above the mean.** Let `X k` be
`ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of `Y` on
the nonnegative parameters given `ℱ k`, and let the selection indicators `w` be adapted with values
in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, the rate function `I`
of `Y`, `c > 1`, `κ ≥ 1` and `x > 0`, the probability that, at some round `t`, `1 ≤ N t`, `μ̂ t`
is above the mean of `Y` and `x + c log (κ (1 + log (N t) / log c) ^ 2) ≤ N t I(μ̂ t)` is at most
`π ^ 2 / (6 κ) exp (-x / c)`. -/
theorem measure_exists_gt_and_add_mul_log_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Ici 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q)
    (hc : 1 < c) (hκ : 1 ≤ κ) (hx : 0 < x) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (x + c * log (κ * (1 + log (∑ k ∈ range t, w k ω) / log c) ^ 2)) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (π ^ 2 / (6 * κ) * exp (-(x / c))) := by
  have hc0 : 0 < c := one_pos.trans hc
  have hlogc : 0 < log c := log_pos hc
  -- the level `θ k` of the slice `c ^ k ≤ N t < c ^ (k + 1)`
  let θ : ℕ → ℝ := fun k ↦ x + c * log (κ * ((k : ℝ) + 1) ^ 2)
  have hθ (k : ℕ) : 0 < θ k := add_mul_log_pos hc0.le hκ hx (by simp)
  let E : ℕ → Set Ω := fun k ↦ {ω | ∃ t, c ^ k ≤ ∑ k ∈ range t, w k ω ∧
    Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
    ENNReal.ofReal (θ k / c ^ (k + 1)) <
      rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)}
  have h_sub : {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (x + c * log (κ * (1 + log (∑ k ∈ range t, w k ω) / log c) ^ 2)) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ⊆
      ⋃ k, E k := by
    rintro ω ⟨t, h1, hm, hrate⟩
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near h1 hc
    refine mem_iUnion.2 ⟨k, t, hk, hm, ?_⟩
    -- the level of the slice is at most the threshold, since `k ≤ log (N t) / log c`
    have hk_le : (k : ℝ) + 1 ≤ 1 + log (∑ k ∈ range t, w k ω) / log c := by
      have h : (k : ℝ) * log c ≤ log (∑ k ∈ range t, w k ω) := by
        rw [← log_pow]
        exact log_le_log (pow_pos hc0 k) hk
      rw [add_comm]
      gcongr
      rwa [le_div_iff₀ hlogc]
    have hθ_le : x + c * log (κ * ((k : ℝ) + 1) ^ 2) ≤
        x + c * log (κ * (1 + log (∑ k ∈ range t, w k ω) / log c) ^ 2) := by
      have hpos : 0 < κ * ((k : ℝ) + 1) ^ 2 := by positivity
      gcongr
    -- `θ k ≤ N t I(μ̂ t)` with `N t < c ^ (k + 1)` forces `θ k / c ^ (k + 1) < I(μ̂ t)`
    exact ofReal_div_lt_of_ofReal_le_ofReal_mul (zero_le_one.trans h1) (hθ k) hk'
      ((ENNReal.ofReal_le_ofReal hθ_le).trans hrate)
  have h_sum := hasSum_exp_neg_add_mul_log_div hc0 (zero_lt_one.trans_le hκ) x
  calc _ ≤ P (⋃ k, E k) := measure_mono h_sub
  _ ≤ ∑' k, P (E k) := measure_iUnion_le _
  _ ≤ ∑' k, ENNReal.ofReal (exp (-(θ k / c))) := by
    refine tsum_le_tsum fun k ↦ ?_
    have h_eq : c ^ k * (θ k / c ^ (k + 1)) = θ k / c := by
      field_simp
      ring
    rw [← h_eq]
    exact measure_exists_le_sum_and_gt_and_lt_rateFunction_le hX hψ hw hw01 hY (pow_pos hc0 k)
      (div_pos (hθ k) (pow_pos hc0 _)).le
  _ = ENNReal.ofReal (π ^ 2 / (6 * κ) * exp (-(x / c))) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k ↦ (exp_pos _).le) h_sum.summable, h_sum.tsum_eq]

/-- **Weighted peeling bound for the self-normalized deviations below the mean.** Let `X k` be
`ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of `Y` on
the nonpositive parameters given `ℱ k`, and let the selection indicators `w` be adapted with values
in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, the rate function `I`
of `Y`, `c > 1`, `κ ≥ 1` and `x > 0`, the probability that, at some round `t`, `1 ≤ N t`, `μ̂ t`
is below the mean of `Y` and `x + c log (κ (1 + log (N t) / log c) ^ 2) ≤ N t I(μ̂ t)` is at most
`π ^ 2 / (6 κ) exp (-x / c)`. -/
theorem measure_exists_lt_and_add_mul_log_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Iic 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q)
    (hc : 1 < c) (hκ : 1 ≤ κ) (hx : 0 < x) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < Q[Y] ∧
      ENNReal.ofReal (x + c * log (κ * (1 + log (∑ k ∈ range t, w k ω) / log c) ^ 2)) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (π ^ 2 / (6 * κ) * exp (-(x / c))) := by
  -- the deviations of `X` below the mean of `Y` are those of `-X` above the mean of `-Y`
  refine le_trans (measure_mono ?_) (measure_exists_gt_and_add_mul_log_le_mul_rateFunction_le
    (X := fun n ↦ -X n) (fun n ↦ (hX n).neg) (fun n ↦ (hψ n).neg_Ici_of_Iic) hw hw01 hY.neg hc
    hκ hx)
  rintro ω ⟨t, h1, hm, hrate⟩
  refine ⟨t, h1, ?_, ?_⟩
  · simpa [integral_neg, neg_div] using hm
  · simpa [neg_div] using hrate

/-- **Weighted peeling bound for the self-normalized deviations on both sides of the mean.** Let
`X k` be `ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of
`Y` given `ℱ k`, and let the selection indicators `w` be adapted with values in `{0, 1}`. For
`N t` selected variables with mean `μ̂ t` after `t` rounds, the rate function `I` of `Y`, `c > 1`,
`κ ≥ 1` and `x > 0`, the probability that, at some round `t`, `1 ≤ N t` and
`x + c log (κ (1 + log (N t) / log c) ^ 2) ≤ N t I(μ̂ t)` is at most
`π ^ 2 / (3 κ) exp (-x / c)`. -/
theorem measure_exists_add_mul_log_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q)
    (hc : 1 < c) (hκ : 1 ≤ κ) (hx : 0 < x) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (x + c * log (κ * (1 + log (∑ k ∈ range t, w k ω) / log c) ^ 2)) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (π ^ 2 / (3 * κ) * exp (-(x / c))) := by
  have h_up := measure_exists_gt_and_add_mul_log_le_mul_rateFunction_le hX
    (fun n ↦ (hψ n).mono inter_subset_right fun _ _ ↦ le_rfl) hw hw01 hY hc hκ hx
  have h_low := measure_exists_lt_and_add_mul_log_le_mul_rateFunction_le hX
    (fun n ↦ (hψ n).mono inter_subset_right fun _ _ ↦ le_rfl) hw hw01 hY hc hκ hx
  refine le_trans (measure_mono ?_)
    ((measure_union_le _ _).trans ((add_le_add h_up h_low).trans_eq ?_))
  · rintro ω ⟨t, h1, hrate⟩
    rcases lt_trichotomy ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω) Q[Y]
      with h | h | h
    · exact Or.inr ⟨t, h1, h, hrate⟩
    · -- at the mean the rate function vanishes, below the positive threshold
      refine absurd hrate (not_le.2 ?_)
      simpa [h, rateFunction_integral hY] using add_mul_log_pos (one_pos.trans hc).le hκ hx
        (le_add_of_nonneg_right (div_nonneg (log_nonneg h1) (log_pos hc).le))
    · exact Or.inl ⟨t, h1, h, hrate⟩
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring

omit [StandardBorelSpace Ω] in
/-- The reduction of the weighted peeling bound to [KK21, Lemma 13]. Let `E t ω θ` be events that
weaken as the threshold `θ` grows. If, for `κ = π ^ 2 / a ≥ 1` and `x > 0`, the weighted peeling
bound `P(∃ t, 1 ≤ N t, E t (x + c log (κ (1 + log (N t) / log c) ^ 2)))`
`≤ π ^ 2 / (a κ) exp (-x / c)` holds, then for `c ∈ (1, 3/2]` and every real `x`,
`P(∃ t, 1 ≤ N t, E t (x + c log (κ / log² c) + 3 log (1 + log N t))) ≤ exp (-x / c)`. -/
private lemma measure_exists_add_three_mul_log_le_of_peeling {N : ℕ → Ω → ℝ}
    {E : ℕ → Ω → ℝ → Prop} {a : ℝ} (hE : ∀ t ω θ θ', θ ≤ θ' → E t ω θ' → E t ω θ)
    (ha : 0 < a) (ha9 : a ≤ 9) (hc : 1 < c) (hc' : c ≤ 3 / 2)
    (h : 1 ≤ π ^ 2 / a → 0 < x →
      P {ω | ∃ t, 1 ≤ N t ω ∧ E t ω (x + c * log (π ^ 2 / a * (1 + log (N t ω) / log c) ^ 2))} ≤
        ENNReal.ofReal (π ^ 2 / (a * (π ^ 2 / a)) * exp (-(x / c)))) :
    P {ω | ∃ t, 1 ≤ N t ω ∧
      E t ω (x + c * log (π ^ 2 / a / log c ^ 2) + 3 * log (1 + log (N t ω)))} ≤
      ENNReal.ofReal (exp (-(x / c))) := by
  rcases le_or_gt x 0 with hx | hx
  · -- for `x ≤ 0` the bound is at least `1`
    refine prob_le_one.trans (ENNReal.one_le_ofReal.2 (one_le_exp ?_))
    have := div_nonpos_of_nonpos_of_nonneg hx (one_pos.trans hc).le
    linarith
  have hκ : 1 ≤ π ^ 2 / a := (one_le_div ha).2 (by nlinarith [pi_gt_three])
  have hπ : π ^ 2 / (a * (π ^ 2 / a)) = 1 := by
    have : π ≠ 0 := pi_ne_zero
    field_simp
  refine le_trans (measure_mono ?_) ((h hκ hx).trans_eq (by rw [hπ, one_mul]))
  rintro ω ⟨t, h1, hθ⟩
  refine ⟨t, h1, hE _ _ _ _ ?_ hθ⟩
  linarith [mul_log_le_mul_log_add_three_mul_log hc hc' (by positivity : 0 < π ^ 2 / a) h1]

/-- **Time-uniform deviations above the mean with an iterated-logarithm correction**
[KK21, Lemma 13]. Let `X k` be `ℱ (k + 1)`-measurable with moment generating function
conditionally bounded by that of `Y` on the nonnegative parameters given `ℱ k`, and let the
selection indicators `w` be adapted with values in `{0, 1}`. For `N t` selected variables with mean
`μ̂ t` after `t` rounds, the rate function `I` of `Y`, `c ∈ (1, 3/2]` and every real `x`, the
probability that, at some round `t`, `1 ≤ N t`, `μ̂ t` is above the mean of `Y` and
`x + c log (ζ(2) / log² c) + 3 log (1 + log N t) ≤ N t I(μ̂ t)` is at most `exp (-x / c)`, with
`ζ(2) = π ^ 2 / 6`. -/
theorem measure_exists_gt_and_add_three_mul_log_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Ici 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q)
    (hc : 1 < c) (hc' : c ≤ 3 / 2) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (x + c * log (π ^ 2 / 6 / log c ^ 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp (-(x / c))) :=
  measure_exists_add_three_mul_log_le_of_peeling (a := 6) (N := fun t ω ↦ ∑ k ∈ range t, w k ω)
    (E := fun t ω θ ↦ Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal θ ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω))
    (fun _ _ _ _ hθ h ↦ ⟨h.1, (ENNReal.ofReal_le_ofReal hθ).trans h.2⟩) (by norm_num)
    (by norm_num) hc hc' fun hκ hx ↦
      measure_exists_gt_and_add_mul_log_le_mul_rateFunction_le hX hψ hw hw01 hY hc hκ hx

/-- **Time-uniform deviations below the mean with an iterated-logarithm correction**
[KK21, Lemma 13]. Let `X k` be `ℱ (k + 1)`-measurable with moment generating function
conditionally bounded by that of `Y` on the nonpositive parameters given `ℱ k`, and let the
selection indicators `w` be adapted with values in `{0, 1}`. For `N t` selected variables with mean
`μ̂ t` after `t` rounds, the rate function `I` of `Y`, `c ∈ (1, 3/2]` and every real `x`, the
probability that, at some round `t`, `1 ≤ N t`, `μ̂ t` is below the mean of `Y` and
`x + c log (ζ(2) / log² c) + 3 log (1 + log N t) ≤ N t I(μ̂ t)` is at most `exp (-x / c)`, with
`ζ(2) = π ^ 2 / 6`. -/
theorem measure_exists_lt_and_add_three_mul_log_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Iic 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q)
    (hc : 1 < c) (hc' : c ≤ 3 / 2) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < Q[Y] ∧
      ENNReal.ofReal (x + c * log (π ^ 2 / 6 / log c ^ 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp (-(x / c))) :=
  measure_exists_add_three_mul_log_le_of_peeling (a := 6) (N := fun t ω ↦ ∑ k ∈ range t, w k ω)
    (E := fun t ω θ ↦ (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < Q[Y] ∧
      ENNReal.ofReal θ ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
        rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω))
    (fun _ _ _ _ hθ h ↦ ⟨h.1, (ENNReal.ofReal_le_ofReal hθ).trans h.2⟩) (by norm_num)
    (by norm_num) hc hc' fun hκ hx ↦
      measure_exists_lt_and_add_mul_log_le_mul_rateFunction_le hX hψ hw hw01 hY hc hκ hx

/-- **Time-uniform deviations with an iterated-logarithm correction** [KK21, Lemma 13]. Let `X k`
be `ℱ (k + 1)`-measurable with moment generating function conditionally bounded by that of `Y`
given `ℱ k`, and let the selection indicators `w` be adapted with values in `{0, 1}`. For `N t`
selected variables with mean `μ̂ t` after `t` rounds, the rate function `I` of `Y`,
`c ∈ (1, 3/2]` and every real `x`, the probability that, at some round `t`, `1 ≤ N t` and
`x + c log (2 ζ(2) / log² c) + 3 log (1 + log N t) ≤ N t I(μ̂ t)` is at most `exp (-x / c)`, with
`2 ζ(2) = π ^ 2 / 3`. -/
theorem measure_exists_add_three_mul_log_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q)
    (hc : 1 < c) (hc' : c ≤ 3 / 2) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (x + c * log (π ^ 2 / 3 / log c ^ 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp (-(x / c))) :=
  measure_exists_add_three_mul_log_le_of_peeling (a := 3) (N := fun t ω ↦ ∑ k ∈ range t, w k ω)
    (E := fun t ω θ ↦ ENNReal.ofReal θ ≤ ENNReal.ofReal (∑ k ∈ range t, w k ω) *
      rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω))
    (fun _ _ _ _ hθ h ↦ (ENNReal.ofReal_le_ofReal hθ).trans h) (by norm_num) (by norm_num) hc hc'
    fun hκ hx ↦ measure_exists_add_mul_log_le_mul_rateFunction_le hX hψ hw hw01 hY hc hκ hx

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Minimizing over `c ∈ (1, 3/2]` the thresholds `c x + c log (κ / log² c)` of
[KK21, Lemma 13], at the confidence level `x` scaled by `c`, gives the threshold
`2 H_{3/2}((x + log κ) / 2)` of [KK21, Corollary 31]: if each event `E (x + c log (κ / log² c))`
has probability at most `exp (-x / c)`, then `E (2 H_{3/2}((x + log κ) / 2))` has probability at
most `exp (-x)`, for every real `x`. -/
private lemma measure_le_exp_neg_of_forall_add_mul_log {E : ℝ → Set Ω} (hκ : 0 < κ)
    (hE : ∀ c x : ℝ, 1 < c → c ≤ 3 / 2 →
      P (E (x + c * log (κ / log c ^ 2))) ≤ ENNReal.ofReal (exp (-(x / c)))) :
    P (E (2 * minMulSubLogLog (3 / 2) ((x + log κ) / 2))) ≤ ENNReal.ofReal (exp (-x)) := by
  -- the minimizer `y ∈ (1, 3/2]` of `y ((x + log κ) / 2 - log log y)`
  obtain ⟨y, ⟨hy1, hy⟩, hyeq⟩ := (isLeast_minMulSubLogLog (z := 3 / 2) (by norm_num)
    (by linarith [add_one_le_exp (1 : ℝ)]) ((x + log κ) / 2)).1
  have hy0 : 0 < y := one_pos.trans hy1
  have h := hE y (y * x) hy1 hy
  rw [mul_div_cancel_left₀ _ hy0.ne'] at h
  have h_eq : 2 * minMulSubLogLog (3 / 2) ((x + log κ) / 2) =
      y * x + y * log (κ / log y ^ 2) := by
    rw [← hyeq, log_div hκ.ne' (by positivity [log_pos hy1]), log_pow]
    push_cast
    ring
  rwa [h_eq]

/-- **Time-uniform deviations above the mean with an iterated-logarithm correction, optimally
tuned** [KK21, Corollary 31]. Let `X k` be `ℱ (k + 1)`-measurable with moment generating function
conditionally bounded by that of `Y` on the nonnegative parameters given `ℱ k`, and let the
selection indicators `w` be adapted with values in `{0, 1}`. For `N t` selected variables with mean
`μ̂ t` after `t` rounds, the rate function `I` of `Y` and every real `x`, the probability that, at
some round `t`, `1 ≤ N t`, `μ̂ t` is above the mean of `Y` and
`2 H_{3/2}((x + log ζ(2)) / 2) + 3 log (1 + log N t) ≤ N t I(μ̂ t)` is at most `exp (-x)`, with
`H_z = LMLExplore.minMulSubLogLog z` and `ζ(2) = π ^ 2 / 6`. -/
theorem measure_exists_gt_and_two_mul_minMulSubLogLog_add_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Ici 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (2 * minMulSubLogLog (3 / 2) ((x + log (π ^ 2 / 6)) / 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp (-x)) :=
  measure_le_exp_neg_of_forall_add_mul_log (E := fun θ ↦ {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      Q[Y] < (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (θ + 3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)})
    (by positivity) fun _ _ hc hc' ↦
      measure_exists_gt_and_add_three_mul_log_le_mul_rateFunction_le hX hψ hw hw01 hY hc hc'

/-- **Time-uniform deviations below the mean with an iterated-logarithm correction, optimally
tuned** [KK21, Corollary 31]. Let `X k` be `ℱ (k + 1)`-measurable with moment generating function
conditionally bounded by that of `Y` on the nonpositive parameters given `ℱ k`, and let the
selection indicators `w` be adapted with values in `{0, 1}`. For `N t` selected variables with mean
`μ̂ t` after `t` rounds, the rate function `I` of `Y` and every real `x`, the probability that, at
some round `t`, `1 ≤ N t`, `μ̂ t` is below the mean of `Y` and
`2 H_{3/2}((x + log ζ(2)) / 2) + 3 log (1 + log N t) ≤ N t I(μ̂ t)` is at most `exp (-x)`, with
`H_z = LMLExplore.minMulSubLogLog z` and `ζ(2) = π ^ 2 / 6`. -/
theorem measure_exists_lt_and_two_mul_minMulSubLogLog_add_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (Iic 0 ∩ integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < Q[Y] ∧
      ENNReal.ofReal (2 * minMulSubLogLog (3 / 2) ((x + log (π ^ 2 / 6)) / 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp (-x)) :=
  measure_le_exp_neg_of_forall_add_mul_log (E := fun θ ↦ {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      (∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω < Q[Y] ∧
      ENNReal.ofReal (θ + 3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)})
    (by positivity) fun _ _ hc hc' ↦
      measure_exists_lt_and_add_three_mul_log_le_mul_rateFunction_le hX hψ hw hw01 hY hc hc'

/-- **Time-uniform deviations with an iterated-logarithm correction, optimally tuned**
[KK21, Corollary 31]. Let `X k` be `ℱ (k + 1)`-measurable with moment generating function
conditionally bounded by that of `Y` given `ℱ k`, and let the selection indicators `w` be adapted
with values in `{0, 1}`. For `N t` selected variables with mean `μ̂ t` after `t` rounds, the rate
function `I` of `Y` and every real `x`, the probability that, at some round `t`, `1 ≤ N t` and
`2 H_{3/2}((x + log (2 ζ(2))) / 2) + 3 log (1 + log N t) ≤ N t I(μ̂ t)` is at most `exp (-x)`, with
`H_z = LMLExplore.minMulSubLogLog z` and `2 ζ(2) = π ^ 2 / 3`. -/
theorem measure_exists_two_mul_minMulSubLogLog_add_le_mul_rateFunction_le
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hψ : ∀ n, HasCondMGFBound (ℱ n) (ℱ.le n) (X n) (cgf Y Q) (integrableExpSet Y Q) P)
    (hw : Adapted ℱ w) (hw01 : ∀ n ω, w n ω = 0 ∨ w n ω = 1) (hY : Integrable Y Q) :
    P {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (2 * minMulSubLogLog (3 / 2) ((x + log (π ^ 2 / 3)) / 2) +
        3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)} ≤
      ENNReal.ofReal (exp (-x)) :=
  measure_le_exp_neg_of_forall_add_mul_log (E := fun θ ↦ {ω | ∃ t, 1 ≤ ∑ k ∈ range t, w k ω ∧
      ENNReal.ofReal (θ + 3 * log (1 + log (∑ k ∈ range t, w k ω))) ≤
        ENNReal.ofReal (∑ k ∈ range t, w k ω) *
          rateFunction Y Q ((∑ k ∈ range t, w k ω * X k ω) / ∑ k ∈ range t, w k ω)})
    (by positivity) fun _ _ hc hc' ↦
      measure_exists_add_three_mul_log_le_mul_rateFunction_le hX hψ hw hw01 hY hc hc'

end LMLExplore
