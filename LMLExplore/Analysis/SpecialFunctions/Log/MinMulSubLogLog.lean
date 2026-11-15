/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Log.SubLogInv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The minimum of `y (x - log log y)` over `(1, z]`, after Kaufmann and Koolen

For `z ∈ (1, e]`, Kaufmann and Koolen [KK21, Definition 29] introduce the function
`H_z(x) = min_{y ∈ (1, z]} y (x - log log y)` (written with a tilde over `h` in [KK21]). With the
inverse `h⁻¹` of `h(u) = u - log u` on `[1, ∞)` (`Real.subLogInv`), its minimizer is
`y = exp (1 / h⁻¹(x))` when this point is at most `z`, and `y = z` otherwise [KK21, (9), Lemma 30].
`H_z` is the outer step of the optimal tuning of their time-uniform deviation inequalities for
several arms [KK21, Lemma 12], proved with the calibration function `𝒞^exp` of [KK21, (10)] in
`LMLExplore.SequentialLearning.CalibrationExp`.

## Main definitions

* `LMLExplore.minMulSubLogLog z x`: `H_z(x)`, by its closed form [KK21, (9)].

## Main statements

* `LMLExplore.minMulSubLogLog_of_le`, `LMLExplore.minMulSubLogLog_of_lt`: the two branches of the
  closed form.
* `LMLExplore.isLeast_minMulSubLogLog` [KK21, Lemma 30]: `H_z(x)` is the minimum of
  `y (x - log log y)` over `y ∈ (1, z]`, for `z ∈ (1, e]` and every real `x`.
* `LMLExplore.monotone_minMulSubLogLog`, `LMLExplore.self_le_minMulSubLogLog`,
  `LMLExplore.minMulSubLogLog_le_max`: `H_z` is monotone, `x ≤ H_z(x)` for `x ≥ 0`, and
  `H_z(x) ≤ max (h⁻¹(x) + 2) (z / log z)`.

## Implementation notes

The closed form (9) of [KK21] as printed switches branches at `x ≥ h⁻¹(1 / log z)`. The
unconstrained minimizer `exp (1 / h⁻¹(x))` is at most `z` exactly when `h(1 / log z) ≤ x`, which is
the threshold used in the proof of [KK21, Lemma 30] (Appendix B.2), so `minMulSubLogLog` switches
at `h(1 / log z)`: with this threshold the closed form is the minimum of [KK21, Definition 29].

## References

* [KK21] E. Kaufmann and W. M. Koolen, *Mixture martingales revisited with applications to
  sequential tests and confidence intervals*, JMLR 22 (2021), Appendix B.2.
-/

public section

open Real Set

namespace LMLExplore

/-- The function `H_z(x) = min_{y ∈ (1, z]} y (x - log log y)` of [KK21, Definition 29], for
`z ∈ (1, e]`, by its closed form [KK21, (9)]: `exp (1 / h⁻¹(x)) h⁻¹(x)` when `h(1 / log z) ≤ x`,
that is, when the unconstrained minimizer `exp (1 / h⁻¹(x))` is at most `z`, and
`z (x - log log z)` otherwise. Here `h(u) = u - log u` and `h⁻¹` is `Real.subLogInv`. The
threshold `h(1 / log z)` is the one of the proof of [KK21, Lemma 30] (Appendix B.2); (9) as printed
in [KK21] has `h⁻¹(1 / log z)` instead. That it is the minimum is
`LMLExplore.isLeast_minMulSubLogLog`. -/
noncomputable def minMulSubLogLog (z x : ℝ) : ℝ :=
  if (log z)⁻¹ - log (log z)⁻¹ ≤ x then exp (subLogInv x)⁻¹ * subLogInv x
  else z * (x - log (log z))

/-- The branch of `H_z(x)` with an interior minimizer: `H_z(x) = exp (1 / h⁻¹(x)) h⁻¹(x)` when
`h(1 / log z) ≤ x`. -/
theorem minMulSubLogLog_of_le {z x : ℝ} (h : (log z)⁻¹ - log (log z)⁻¹ ≤ x) :
    minMulSubLogLog z x = exp (subLogInv x)⁻¹ * subLogInv x :=
  ite_eq_left h

/-- The branch of `H_z(x)` with minimizer `z`: `H_z(x) = z (x - log log z)` when
`x < h(1 / log z)`. -/
theorem minMulSubLogLog_of_lt {z x : ℝ} (h : x < (log z)⁻¹ - log (log z)⁻¹) :
    minMulSubLogLog z x = z * (x - log (log z)) :=
  ite_eq_right (not_le.2 h)

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

/-- `y ↦ y (x - log log y)` is antitone on `(1, b]` if `x ≤ h(1 / log w)` for `w ∈ (1, b)`. -/
private theorem antitoneOn_mul_sub_log_log {x b : ℝ}
    (h : ∀ w ∈ Ioo 1 b, x ≤ (log w)⁻¹ - log (log w)⁻¹) :
    AntitoneOn (fun y ↦ y * (x - log (log y))) (Ioc 1 b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun w ↦ x - ((log w)⁻¹ - log (log w)⁻¹))
    (convex_Ioc 1 b)
    (fun y hy ↦ (hasDerivAt_mul_sub_log_log x hy.1).continuousAt.continuousWithinAt)
    (fun w hw ↦ ?_) (fun w hw ↦ ?_) <;> rw [interior_Ioc] at hw
  · exact (hasDerivAt_mul_sub_log_log x hw.1).hasDerivWithinAt
  · linarith [h w hw]

/-- `y ↦ y (x - log log y)` is monotone on `[a, b]`, for `1 < a`, if `h(1 / log w) ≤ x` for
`w ∈ (a, b)`. -/
private theorem monotoneOn_mul_sub_log_log {x a b : ℝ} (ha : 1 < a)
    (h : ∀ w ∈ Ioo a b, (log w)⁻¹ - log (log w)⁻¹ ≤ x) :
    MonotoneOn (fun y ↦ y * (x - log (log y))) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun w ↦ x - ((log w)⁻¹ - log (log w)⁻¹))
    (convex_Icc a b)
    (fun y hy ↦ (hasDerivAt_mul_sub_log_log x (ha.trans_le hy.1)).continuousAt.continuousWithinAt)
    (fun w hw ↦ ?_) (fun w hw ↦ ?_) <;> rw [interior_Icc] at hw
  · exact (hasDerivAt_mul_sub_log_log x (ha.trans hw.1)).hasDerivWithinAt
  · linarith [h w hw]

/-- For `1 < y ≤ z ≤ e`, `1 ≤ 1 / log z ≤ 1 / log y`. -/
private theorem one_le_inv_log_le_inv_log {y z : ℝ} (hy : 1 < y) (hyz : y ≤ z)
    (hze : z ≤ exp 1) : 1 ≤ (log z)⁻¹ ∧ (log z)⁻¹ ≤ (log y)⁻¹ := by
  have hly : 0 < log y := log_pos hy
  have hlz1 : log z ≤ 1 := by
    rw [← log_exp 1]
    exact log_le_log (by linarith) hze
  exact ⟨(one_le_inv₀ (hly.trans_le (log_le_log (by linarith) hyz))).2 hlz1,
    inv_anti₀ hly (log_le_log (by linarith) hyz)⟩

/-- **[KK21, Lemma 30]**: for `z ∈ (1, e]` and every real `x`, `H_z(x)` is the minimum of
`y (x - log log y)` over `y ∈ (1, z]`. -/
theorem isLeast_minMulSubLogLog {z : ℝ} (hz1 : 1 < z) (hze : z ≤ exp 1) (x : ℝ) :
    IsLeast ((fun y ↦ y * (x - log (log y))) '' Ioc 1 z) (minMulSubLogLog z x) := by
  set f : ℝ → ℝ := fun y ↦ y * (x - log (log y))
  rcases le_or_gt ((log z)⁻¹ - log (log z)⁻¹) x with h | h
  · -- the minimizer `exp (1 / h⁻¹(x))` lies in `(1, z]`
    rw [minMulSubLogLog_of_le h]
    set u := subLogInv x
    have hx1 : 1 ≤ x := by
      have := one_le_sub_log (inv_pos.2 (log_pos hz1))
      linarith
    have hu : u - log u = x := subLogInv_sub_log_subLogInv hx1
    have hu0 : 0 < u := subLogInv_pos x
    have hvu : (log z)⁻¹ ≤ u := by
      by_contra hlt
      have := sub_log_lt_sub_log (one_le_subLogInv x) (not_le.1 hlt)
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
      refine antitoneOn_mul_sub_log_log (fun w hw ↦ ?_) ⟨hy1, hyy⟩ ⟨hy₀1, le_rfl⟩ hyy
      have hlw : log w < u⁻¹ := by
        rw [← log_exp u⁻¹]
        exact log_lt_log (by linarith [hw.1]) hw.2
      have : u ≤ (log w)⁻¹ := by
        rw [le_inv_comm₀ hu0 (log_pos hw.1)]
        exact hlw.le
      linarith [sub_log_le_sub_log (one_le_subLogInv x) this]
    · -- `f` is monotone on `[exp (1 / u), z]`
      refine monotoneOn_mul_sub_log_log hy₀1 (fun w hw ↦ ?_) ⟨le_rfl, hy₀z⟩ ⟨hyy, hyz⟩ hyy
      have hw1 : 1 < w := hy₀1.trans hw.1
      have hlw : u⁻¹ < log w := by
        rw [← log_exp u⁻¹]
        exact log_lt_log (by positivity) hw.1
      have hwu : (log w)⁻¹ ≤ u := by
        rw [inv_le_comm₀ (log_pos hw1) hu0]
        exact hlw.le
      have h1w := (one_le_inv_log_le_inv_log hw1 hw.2.le hze)
      linarith [sub_log_le_sub_log (h1w.1.trans h1w.2) hwu]
  · -- the minimizer is `z`: `f` is antitone on `(1, z]`
    rw [minMulSubLogLog_of_lt h]
    refine ⟨⟨z, ⟨hz1, le_rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    refine antitoneOn_mul_sub_log_log (fun w hw ↦ ?_) hy ⟨hz1, le_rfl⟩ hy.2
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
  rcases le_or_gt ((log z)⁻¹ - log (log z)⁻¹) x with h | h
  · rw [minMulSubLogLog_of_le h]
    refine le_max_of_le_left ?_
    set u := subLogInv x
    have hu1 : 1 ≤ u := one_le_subLogInv x
    have hu0 : 0 < u := by linarith
    have hinv : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
    have hexp := (abs_le.1 (abs_exp_sub_one_sub_id_le
      (by rwa [abs_of_pos (inv_pos.2 hu0)] : |u⁻¹| ≤ 1))).2
    have : exp u⁻¹ * u ≤ (1 + u⁻¹ + u⁻¹ ^ 2) * u := by gcongr; linarith
    have hcalc : (1 + u⁻¹ + u⁻¹ ^ 2) * u = u + 1 + u⁻¹ := by field_simp
    linarith
  · rw [minMulSubLogLog_of_lt h]
    refine le_max_of_le_right ?_
    rw [log_inv] at h
    rw [div_eq_mul_inv]
    gcongr
    linarith

end LMLExplore
