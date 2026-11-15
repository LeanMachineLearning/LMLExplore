/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.SubLogInv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The calibration function `𝒞^exp` of Kaufmann and Koolen

Kaufmann and Koolen [KK21, Theorem 7] bound the deviations of the empirical means of several arms
of exponential families uniformly in time: for a set `S` of arms and `x > 0`, with
`X_a(t) = [N_a(t) d(μ̂_a(t), μ_a) - 3 log (1 + log N_a(t))]⁺`,
`P(∃ t, ∑_{a ∈ S} X_a(t) ≥ |S| 𝒞^exp(x / |S|)) ≤ e^{-x}`.
Their proof gives, for every `ξ ∈ (0, 1/2]` and `λ ∈ (0, 1 / (1 + ξ))`, the threshold
`|S| (x / |S| + g_ξ(λ)) / λ` with `g_ξ(λ) = λ (1 + ξ) log C(ξ) - log (1 - λ (1 + ξ))` and
`C(ξ) = 2 ζ(2) / log² (1 + ξ)`, and `𝒞^exp` is the optimal tuning of `ξ` and `λ`
[KK21, Lemma 12]. This file defines `𝒞^exp` by its closed form [KK21, (10)], proves that it is that
optimum, and bounds it: `𝒞^exp(x) = x + O(log (1 + x))`, with explicit constants.

The closed form uses the inverse `h⁻¹` of `h(u) = u - log u` on `[1, ∞)` (`Real.subLogInv`) and,
for `z ∈ (1, e]`, the function `H_z(x) = min_{y ∈ (1, z]} y (x - log log y)` [KK21, Definition 29]
(written with a tilde over `h` in [KK21]), whose minimizer is `y = exp (1 / h⁻¹(x))` when this
point is at most `z`, and `y = z` otherwise [KK21, (9), Lemma 30]. Then
`𝒞^exp(x) = 2 H_{3/2}((h⁻¹(1 + x) + log (2 ζ(2))) / 2)`, where `2 ζ(2) = π² / 3`.

## Main definitions

* `LMLExplore.minMulSubLogLog z x`: `H_z(x)`, by its closed form [KK21, (9)].
* `LMLExplore.calibrationExp x`: `𝒞^exp(x)` [KK21, (10)].

## Main statements

* `LMLExplore.isLeast_minMulSubLogLog` [KK21, Lemma 30]: `H_z(x)` is the minimum of
  `y (x - log log y)` over `y ∈ (1, z]`, for `z ∈ (1, e]` and every real `x`.
* `LMLExplore.monotone_minMulSubLogLog`, `LMLExplore.self_le_minMulSubLogLog`,
  `LMLExplore.minMulSubLogLog_le_max`: `H_z` is monotone, `x ≤ H_z(x)` for `x ≥ 0`, and
  `H_z(x) ≤ max (h⁻¹(x) + 2) (z / log z)`.
* `LMLExplore.isLeast_two_mul_minMulSubLogLog` [KK21, Lemma 12]: for `c > 0`, `x > 0` and
  `z ∈ (0, e - 1]`, the minimum of `(x - log (1 - λ (1 + ξ))) / λ + (1 + ξ) log (c / log² (1 + ξ))`
  over `ξ ∈ (0, z]` and `λ ∈ (0, 1 / (1 + ξ))` is `2 H_{1+z}((h⁻¹(1 + x) + log c) / 2)`. The case
  `c = 2 ζ(2)`, `z = 1/2` is `𝒞^exp`; the case `c = ζ(2)` is the smaller calibration of one-sided
  deviations [KK21, Theorem 7].
* `LMLExplore.isLeast_calibrationExp`: `𝒞^exp(x)` is the optimal tuning of [KK21, Lemma 12].
* `LMLExplore.monotone_calibrationExp`, `LMLExplore.one_add_add_log_le_calibrationExp`,
  `LMLExplore.calibrationExp_le_add_three_mul_log_add`: `𝒞^exp` is monotone and, for `x ≥ 0`,
  `1 + x + log (1 + x) ≤ 𝒞^exp(x) ≤ x + 3 log (1 + x) + 11`.

## References

* [KK21] E. Kaufmann and W. M. Koolen, *Mixture martingales revisited with applications to
  sequential tests and confidence intervals*, JMLR 22 (2021), Theorem 7, Lemma 12 and
  Appendix B.2.
-/

public section

open Real Set

namespace LMLExplore

/-- The function `H_z(x) = min_{y ∈ (1, z]} y (x - log log y)` of [KK21, (9)], for `z ∈ (1, e]`,
by its closed form: `exp (1 / h⁻¹(x)) h⁻¹(x)` when `h(1 / log z) ≤ x`, that is, when the
unconstrained minimizer `exp (1 / h⁻¹(x))` is at most `z`, and `z (x - log log z)` otherwise. Here
`h(u) = u - log u` and `h⁻¹` is `Real.subLogInv`. That it is the minimum is
`LMLExplore.isLeast_minMulSubLogLog`. -/
noncomputable def minMulSubLogLog (z x : ℝ) : ℝ :=
  if (log z)⁻¹ - log (log z)⁻¹ ≤ x then exp (subLogInv x)⁻¹ * subLogInv x
  else z * (x - log (log z))

/-- The derivative of `y ↦ y (x - log log y)` at `y > 1` is `x - h(1 / log y)`. -/
private theorem hasDerivAt_mul_sub_log_log (x : ℝ) {y : ℝ} (hy : 1 < y) :
    HasDerivAt (fun y ↦ y * (x - log (log y))) (x - ((log y)⁻¹ - log (log y)⁻¹)) y := by
  have hy0 : 0 < y := by linarith
  have hl : 0 < log y := log_pos hy
  have h : HasDerivAt (fun y ↦ y * (x - log (log y)))
      (1 * (x - log (log y)) + y * -(y⁻¹ / log y)) y :=
    (hasDerivAt_id' y).mul (((hasDerivAt_log hy0.ne').log hl.ne').const_sub x)
  refine h.congr_deriv ?_
  rw [log_inv]
  field_simp
  ring

/-- For `1 < y ≤ z ≤ e`, `1 ≤ 1 / log z ≤ 1 / log y`. -/
private theorem one_le_inv_log_le_inv_log {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (hze : z ≤ exp 1) : 1 ≤ (log z)⁻¹ ∧ (log z)⁻¹ ≤ (log y)⁻¹ := by
  have hly : 0 < log y := log_pos hy
  have hlz1 : log z ≤ 1 := by
    rw [← log_exp 1]
    exact log_le_log (by linarith) hze
  exact ⟨(one_le_inv₀ (hly.trans_le (log_le_log (by linarith) hyz))).2 hlz1,
    inv_anti₀ hly (log_le_log (by linarith) hyz)⟩

/-- `h(a) ≤ h(b)` for `1 ≤ a ≤ b`, with `h(u) = u - log u`. -/
private theorem sub_log_le_sub_log {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a - log a ≤ b - log b :=
  strictMonoOn_sub_log.monotoneOn ha (mem_Ici.2 (ha.trans hab)) hab

/-- **[KK21, Lemma 30]**: for `z ∈ (1, e]` and every real `x`, `H_z(x)` is the minimum of
`y (x - log log y)` over `y ∈ (1, z]`. -/
theorem isLeast_minMulSubLogLog {z : ℝ} (hz1 : 1 < z) (hze : z ≤ exp 1) (x : ℝ) :
    IsLeast ((fun y ↦ y * (x - log (log y))) '' Ioc 1 z) (minMulSubLogLog z x) := by
  set f : ℝ → ℝ := fun y ↦ y * (x - log (log y))
  have hcont : ContinuousOn f (Ioi 1) := fun y hy ↦
    (hasDerivAt_mul_sub_log_log x hy).continuousAt.continuousWithinAt
  have hderiv : ∀ D ⊆ Ioi (1 : ℝ), ∀ w ∈ interior D,
      HasDerivWithinAt f (x - ((log w)⁻¹ - log (log w)⁻¹)) (interior D) w := fun D hD w hw ↦
    (hasDerivAt_mul_sub_log_log x (hD (interior_subset hw))).hasDerivWithinAt
  have hv₀ := (one_le_inv_log_le_inv_log hz1 le_rfl hze).1
  unfold minMulSubLogLog
  split_ifs with h
  · -- the minimizer `exp (1 / h⁻¹(x))` lies in `(1, z]`
    set u := subLogInv x
    have hx1 : 1 ≤ x := by
      have := sub_log_le_sub_log le_rfl hv₀
      rw [log_one, sub_zero] at this
      linarith
    have hu : u - log u = x := subLogInv_sub_log_subLogInv hx1
    have hu0 : 0 < u := subLogInv_pos x
    have hvu : (log z)⁻¹ ≤ u := by
      by_contra hlt
      have := strictMonoOn_sub_log (one_le_subLogInv x) (mem_Ici.2 hv₀) (not_le.1 hlt)
      beta_reduce at this
      linarith
    have hy₀1 : 1 < exp u⁻¹ := one_lt_exp_iff.2 (inv_pos.2 hu0)
    have hy₀z : exp u⁻¹ ≤ z := by
      rw [← exp_log (by linarith : 0 < z)]
      exact exp_le_exp.2 (by simpa using inv_anti₀ (inv_pos.2 (log_pos hz1)) hvu)
    have hfy₀ : f (exp u⁻¹) = exp u⁻¹ * u := by
      simp only [f, log_exp, log_inv]
      congr 1
      linarith
    refine ⟨⟨exp u⁻¹, ⟨hy₀1, hy₀z⟩, hfy₀⟩, ?_⟩
    rintro _ ⟨y, ⟨hy1, hyz⟩, rfl⟩
    rw [← hfy₀]
    rcases le_total y (exp u⁻¹) with hyy | hyy
    · -- `f` is antitone on `(1, exp (1 / u)]`
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 1 (exp u⁻¹))
        (hcont.mono Ioc_subset_Ioi_self) (hderiv _ Ioc_subset_Ioi_self) ?_ ⟨hy1, hyy⟩
        ⟨hy₀1, le_rfl⟩ hyy
      intro w hw
      rw [interior_Ioc] at hw
      have hlw : log w < u⁻¹ := by
        rw [← log_exp u⁻¹]
        exact log_lt_log (by linarith [hw.1]) hw.2
      have hlw0 : 0 < log w := log_pos hw.1
      have : u ≤ (log w)⁻¹ := by
        rw [le_inv_comm₀ hu0 hlw0]
        exact hlw.le
      linarith [sub_log_le_sub_log (one_le_subLogInv x) this]
    · -- `f` is monotone on `[exp (1 / u), z]`
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (exp u⁻¹) z)
        (hcont.mono fun w hw ↦ hy₀1.trans_le hw.1) (hderiv _ fun w hw ↦ hy₀1.trans_le hw.1) ?_
        ⟨le_rfl, hy₀z⟩ ⟨hyy, hyz⟩ hyy
      intro w hw
      rw [interior_Icc] at hw
      have hw1 : 1 < w := hy₀1.trans hw.1
      have hlw : u⁻¹ < log w := by
        rw [← log_exp u⁻¹]
        exact log_lt_log (by positivity) hw.1
      have hlw0 : 0 < log w := log_pos hw1
      have hwu : (log w)⁻¹ ≤ u := by
        rw [inv_le_comm₀ hlw0 hu0]
        exact hlw.le
      have h1w := (one_le_inv_log_le_inv_log hw1 hw.2.le hze)
      linarith [sub_log_le_sub_log (h1w.1.trans h1w.2) hwu]
  · -- the minimizer is `z`: `f` is antitone on `(1, z]`
    refine ⟨⟨z, ⟨hz1, le_rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨y, ⟨hy1, hyz⟩, rfl⟩
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 1 z)
      (hcont.mono Ioc_subset_Ioi_self) (hderiv _ Ioc_subset_Ioi_self) ?_ ⟨hy1, hyz⟩
      ⟨hz1, le_rfl⟩ hyz
    intro w hw
    rw [interior_Ioc] at hw
    have h1w := one_le_inv_log_le_inv_log hw.1 hw.2.le hze
    linarith [sub_log_le_sub_log h1w.1 h1w.2]

theorem minMulSubLogLog_le {z x y : ℝ} (hz1 : 1 < z) (hze : z ≤ exp 1) (hy : y ∈ Ioc 1 z) :
    minMulSubLogLog z x ≤ y * (x - log (log y)) :=
  (isLeast_minMulSubLogLog hz1 hze x).2 ⟨y, hy, rfl⟩

theorem monotone_minMulSubLogLog {z : ℝ} (hz1 : 1 < z) (hze : z ≤ exp 1) :
    Monotone (minMulSubLogLog z) := by
  intro x x' hxx'
  obtain ⟨y, hy, hyeq⟩ := (isLeast_minMulSubLogLog hz1 hze x').1
  rw [← hyeq]
  refine (minMulSubLogLog_le hz1 hze hy).trans ?_
  have : 0 ≤ y := by linarith [hy.1]
  beta_reduce
  gcongr

/-- `x ≤ H_z(x)` for `x ≥ 0` and `z ∈ (1, e]`. -/
theorem self_le_minMulSubLogLog {z x : ℝ} (hz1 : 1 < z) (hze : z ≤ exp 1) (hx : 0 ≤ x) :
    x ≤ minMulSubLogLog z x := by
  obtain ⟨y, ⟨hy1, hyz⟩, hyeq⟩ := (isLeast_minMulSubLogLog hz1 hze x).1
  rw [← hyeq]
  have hlog : log (log y) ≤ 0 := by
    have := (one_le_inv_log_le_inv_log hy1 hyz hze)
    rw [← neg_nonneg, ← log_inv]
    exact log_nonneg (this.1.trans this.2)
  nlinarith

/-- `H_z(x) ≤ max (h⁻¹(x) + 2) (z / log z)` for `z ≥ 0`: the first term bounds the value
`exp (1 / h⁻¹(x)) h⁻¹(x)` at an interior minimizer, the second the value at `z`. -/
theorem minMulSubLogLog_le_max {z : ℝ} (hz : 0 ≤ z) (x : ℝ) :
    minMulSubLogLog z x ≤ max (subLogInv x + 2) (z / log z) := by
  unfold minMulSubLogLog
  split_ifs with h
  · refine le_max_of_le_left ?_
    set u := subLogInv x
    have hu1 : 1 ≤ u := one_le_subLogInv x
    have hu0 : 0 < u := by linarith
    have habs : |u⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.2 hu0)]
      exact inv_le_one_of_one_le₀ hu1
    have hexp := (abs_le.1 (abs_exp_sub_one_sub_id_le habs)).2
    have hinv : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
    have : exp u⁻¹ * u ≤ (1 + u⁻¹ + u⁻¹ ^ 2) * u := by gcongr; linarith
    have hcalc : (1 + u⁻¹ + u⁻¹ ^ 2) * u = u + 1 + u⁻¹ := by field_simp
    linarith
  · refine le_max_of_le_right ?_
    rw [log_inv] at h
    rw [div_eq_mul_inv]
    gcongr
    linarith

/-- `(x - log (1 - λ y)) / λ + y log (c / log² y) = 2 y ((h⁻¹(1 + x) + log c) / 2 - log log y)
+ y ((x - log (1 - λ y)) / (λ y) - h⁻¹(1 + x))`, the decomposition of the objective of
[KK21, Lemma 12] into the objective of [KK21, Lemma 30] and that of [KK21, Lemma 28]. -/
private theorem tuning_eq {c x y l : ℝ} (hc : 0 < c) (hy : 1 < y) (hl : 0 < l) :
    (x - log (1 - l * y)) / l + y * log (c / log y ^ 2) =
      2 * (y * ((subLogInv (1 + x) + log c) / 2 - log (log y))) +
        y * ((x - log (1 - l * y)) / (l * y) - subLogInv (1 + x)) := by
  have hy0 : 0 < y := by linarith
  rw [log_div hc.ne' (pow_ne_zero 2 (log_pos hy).ne'), log_pow]
  field_simp
  ring

/-- **The optimal tuning of [KK21, Lemma 12]**: for `c > 0`, `x > 0` and `z ∈ (0, e - 1]`, the
minimum of `(x - log (1 - λ (1 + ξ))) / λ + (1 + ξ) log (c / log² (1 + ξ))` over `ξ ∈ (0, z]` and
`λ ∈ (0, 1 / (1 + ξ))` is `2 H_{1+z}((h⁻¹(1 + x) + log c) / 2)`. -/
theorem isLeast_two_mul_minMulSubLogLog {c x z : ℝ} (hc : 0 < c) (hx : 0 < x) (hz0 : 0 < z)
    (hz : z ≤ exp 1 - 1) :
    IsLeast {v | ∃ ξ ∈ Ioc 0 z, ∃ l ∈ Ioo 0 (1 + ξ)⁻¹,
        v = (x - log (1 - l * (1 + ξ))) / l + (1 + ξ) * log (c / log (1 + ξ) ^ 2)}
      (2 * minMulSubLogLog (1 + z) ((subLogInv (1 + x) + log c) / 2)) := by
  have hz1 : 1 < 1 + z := by linarith
  have hze : 1 + z ≤ exp 1 := by linarith
  refine ⟨?_, ?_⟩
  · obtain ⟨y, ⟨hy1, hyz⟩, hyeq⟩ := (isLeast_minMulSubLogLog hz1 hze
      ((subLogInv (1 + x) + log c) / 2)).1
    obtain ⟨q, ⟨hq0, hq1⟩, hqeq⟩ := (Real.isLeast_subLogInv_one_add hx).1
    beta_reduce at hyeq hqeq
    have hy0 : 0 < y := by linarith
    refine ⟨y - 1, ⟨by linarith, by linarith⟩, q / y, ⟨div_pos hq0 hy0, ?_⟩, ?_⟩
    · rw [add_sub_cancel, div_lt_iff₀ hy0, inv_mul_cancel₀ hy0.ne']
      exact hq1
    · rw [add_sub_cancel, tuning_eq hc hy1 (div_pos hq0 hy0), div_mul_cancel₀ q hy0.ne',
        hqeq, sub_self, mul_zero, add_zero, ← hyeq]
  · rintro _ ⟨ξ, ⟨hξ0, hξz⟩, l, ⟨hl0, hl1⟩, rfl⟩
    have hy1 : 1 < 1 + ξ := by linarith
    have hy0 : 0 < 1 + ξ := by linarith
    rw [tuning_eq hc hy1 hl0]
    have hq1 : l * (1 + ξ) < 1 := by
      simpa [inv_mul_cancel₀ hy0.ne'] using mul_lt_mul_of_pos_right hl1 hy0
    have h28 := Real.subLogInv_one_add_le_div hx.le (mul_pos hl0 hy0) hq1
    have h30 := minMulSubLogLog_le (x := (subLogInv (1 + x) + log c) / 2) hz1 hze
      ⟨hy1, by linarith⟩
    nlinarith

/-- The calibration function `𝒞^exp(x) = 2 H_{3/2}((h⁻¹(1 + x) + log (2 ζ(2))) / 2)` of the
time-uniform deviation inequality of Kaufmann and Koolen for several arms of exponential families
[KK21, (10), Theorem 7], with `2 ζ(2) = π² / 3` (Mathlib's `hasSum_zeta_two`). -/
noncomputable def calibrationExp (x : ℝ) : ℝ :=
  2 * minMulSubLogLog (3 / 2) ((subLogInv (1 + x) + log (π ^ 2 / 3)) / 2)

private theorem three_halves_le_exp_one : (3 / 2 : ℝ) ≤ exp 1 := by
  linarith [add_one_le_exp (1 : ℝ)]

/-- `𝒞^exp(x)` is the optimal tuning of [KK21, Lemma 12] for `C(ξ) = 2 ζ(2) / log² (1 + ξ)` and
`ξ ∈ (0, 1/2]`: for `x > 0` it is the minimum of `(x + g_ξ(λ)) / λ`, with
`g_ξ(λ) = λ (1 + ξ) log C(ξ) - log (1 - λ (1 + ξ))`, over `ξ ∈ (0, 1/2]` and
`λ ∈ (0, 1 / (1 + ξ))`. -/
theorem isLeast_calibrationExp {x : ℝ} (hx : 0 < x) :
    IsLeast {v | ∃ ξ ∈ Ioc 0 (1 / 2 : ℝ), ∃ l ∈ Ioo 0 (1 + ξ)⁻¹,
        v = (x - log (1 - l * (1 + ξ))) / l + (1 + ξ) * log (π ^ 2 / 3 / log (1 + ξ) ^ 2)}
      (calibrationExp x) := by
  have h := isLeast_two_mul_minMulSubLogLog (c := π ^ 2 / 3) (z := 1 / 2) (by positivity) hx
    (by norm_num) (by linarith [three_halves_le_exp_one])
  rwa [show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] at h

theorem monotone_calibrationExp : Monotone calibrationExp := by
  intro x x' hxx'
  unfold calibrationExp
  refine mul_le_mul_of_nonneg_left (monotone_minMulSubLogLog (by norm_num)
    three_halves_le_exp_one ?_) zero_le_two
  gcongr
  exact monotone_subLogInv (by linarith)

/-- `1 ≤ log (π² / 3)`. -/
private theorem one_le_log_pi_sq_div_three : 1 ≤ log (π ^ 2 / 3) := by
  rw [le_log_iff_exp_le (by positivity)]
  have := exp_one_lt_d9
  have := pi_gt_three
  nlinarith

/-- `log (π² / 3) ≤ 2`. -/
private theorem log_pi_sq_div_three_le_two : log (π ^ 2 / 3) ≤ 2 := by
  rw [log_le_iff_le_exp (by positivity)]
  have h5 := quadratic_le_exp_of_nonneg (zero_le_two (α := ℝ))
  have := pi_lt_d2
  have := pi_pos
  nlinarith

/-- The lower bound `1 + x + log (1 + x) ≤ 𝒞^exp(x)` for `x ≥ 0`. -/
theorem one_add_add_log_le_calibrationExp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + log (1 + x) ≤ calibrationExp x := by
  have hY : 0 ≤ (subLogInv (1 + x) + log (π ^ 2 / 3)) / 2 := by
    have := one_le_log_pi_sq_div_three
    have := one_le_subLogInv (1 + x)
    positivity
  have h := self_le_minMulSubLogLog (by norm_num) three_halves_le_exp_one hY
  have h1 := Real.add_log_le_subLogInv (by linarith : (0 : ℝ) < 1 + x)
  have h2 := one_le_log_pi_sq_div_three
  unfold calibrationExp
  linarith

/-- The upper bound `𝒞^exp(x) ≤ x + 3 log (1 + x) + 11` for `x ≥ 0`: with the lower bound
`one_add_add_log_le_calibrationExp`, `𝒞^exp(x) = x + O(log (1 + x))`. -/
theorem calibrationExp_le_add_three_mul_log_add {x : ℝ} (hx : 0 ≤ x) :
    calibrationExp x ≤ x + 3 * log (1 + x) + 11 := by
  set u₁ := subLogInv (1 + x)
  set L := log (π ^ 2 / 3)
  have hL1 := one_le_log_pi_sq_div_three
  have hL2 := log_pi_sq_div_three_le_two
  have hx1 : 0 < 1 + x := by linarith
  have hlogx : 0 ≤ log (1 + x) := log_nonneg (by linarith)
  have hlog2 := log_two_lt_d9
  norm_num at hlog2
  have hu₁1 : 1 ≤ u₁ := one_le_subLogInv _
  have hY : 1 ≤ (u₁ + L) / 2 := by linarith
  -- `u₁ ≤ 1 + x + log 2 + log (1 + x)`, so `u₁ + L ≤ 4 (1 + x)`
  have hu₁ := Real.subLogInv_le_add_log_two_mul (by linarith : (1 : ℝ) ≤ 1 + x)
  rw [log_mul two_ne_zero hx1.ne'] at hu₁
  have hlogx' : log (1 + x) ≤ x := by linarith [log_le_sub_one_of_pos hx1]
  have h4 : log (2 * ((u₁ + L) / 2)) ≤ 2 * log 2 + log (1 + x) := by
    have h := log_le_log (by linarith) (by linarith : 2 * ((u₁ + L) / 2) ≤ 2 ^ 2 * (1 + x))
    rwa [log_mul (by norm_num) hx1.ne', log_pow, Nat.cast_ofNat] at h
  -- both branches of `minMulSubLogLog_le_max` are at most
  -- `(u₁ + L) / 2 + 2 log 2 + log (1 + x) + 2`
  have hl32 : 2 / 5 ≤ log (3 / 2) := by
    have := le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at this ⊢
    linarith
  have h32 : 3 / 2 / log (3 / 2) ≤ 3 / 2 / (2 / 5) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl32
  have hmax : max (subLogInv ((u₁ + L) / 2) + 2) (3 / 2 / log (3 / 2)) ≤
      (u₁ + L) / 2 + 2 * log 2 + log (1 + x) + 2 :=
    max_le (by linarith [Real.subLogInv_le_add_log_two_mul hY])
      (by norm_num at h32 ⊢; linarith [log_two_gt_d9])
  have h := minMulSubLogLog_le_max (z := 3 / 2) (by norm_num) ((u₁ + L) / 2)
  unfold calibrationExp
  linarith

end LMLExplore
