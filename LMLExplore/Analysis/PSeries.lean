/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.Basic

/-!
# Explicit bounds on the sums of `1 / n ^ p` and `log n / n ^ p`

For `p > 1`, the series `∑ 1 / n ^ p` and `∑ log n / n ^ p` converge, and comparison with the
integrals `∫_1^∞ x ^ (-p) dx = 1 / (p - 1)` and `∫_1^∞ log x / x ^ p dx = 1 / (p - 1) ^ 2` gives
`∑_{n ≥ 1} 1 / n ^ p ≤ 1 + 1 / (p - 1)` and `∑_{n ≥ 1} log n / n ^ p ≤ 1 + 1 / (p - 1) ^ 2`.
The integrands are antitone on `[1, ∞)` and on `[3, ∞)` respectively, and the terms of
`log n / n ^ p` before that, `log 2 / 2 ^ p + log 3 / 3 ^ p ≤ 2 / e`, are at most `1`. These are
the constants with which a union bound over the rounds `n` of thresholds `log (C n ^ p)`, as in the
exploration rates of [KK13, Theorem 1], is summed.

The terms of index `0` vanish, since `log 0 = 0` and `1 / 0 ^ p = 0`, so the sums are over `ℕ`.

## Main statements

* `Real.hasDerivAt_neg_log_mul_rpow_div`: the antiderivative
  `-(log x x ^ (-(p - 1))) / (p - 1) - x ^ (-(p - 1)) / (p - 1) ^ 2` of `log x / x ^ p` on
  `(0, ∞)`, for `p ≠ 1`.
* `Real.sum_range_one_div_nat_rpow_le`, `Real.sum_range_log_div_nat_rpow_le`: the partial sums
  `∑_{n < N} 1 / n ^ p ≤ 1 + 1 / (p - 1)` and `∑_{n < N} log n / n ^ p ≤ 1 + 1 / (p - 1) ^ 2`
  for `p > 1`, the form that a union bound over a fixed horizon needs.
* `Real.tsum_one_div_nat_rpow_le`: `∑ 1 / n ^ p ≤ 1 + 1 / (p - 1)` for `p > 1`.
* `Real.summable_log_div_nat_rpow`: `∑ log n / n ^ p` converges for `p > 1`.
* `Real.tsum_log_div_nat_rpow_le`: `∑ log n / n ^ p ≤ 1 + 1 / (p - 1) ^ 2` for `p > 1`.

## References

* [KK13] E. Kaufmann and S. Kalyanakrishnan, *Information complexity in bandit subset selection*,
  COLT 2013, proof of Theorem 1 (Appendix A).
-/

public section

open Finset Set

namespace Real

variable {p : ℝ}

/-- An antiderivative of `log x / x ^ p` on `(0, ∞)`, for `p ≠ 1`. -/
theorem hasDerivAt_neg_log_mul_rpow_div {x : ℝ} (hx : 0 < x) (hp : p ≠ 1) :
    HasDerivAt (fun y : ℝ ↦ -(log y * y ^ (-(p - 1))) / (p - 1) - y ^ (-(p - 1)) / (p - 1) ^ 2)
      (log x / x ^ p) x := by
  have hp1 : p - 1 ≠ 0 := sub_ne_zero.2 hp
  have h_rpow := hasDerivAt_rpow_const (p := -(p - 1)) (Or.inl hx.ne')
  have h := (((hasDerivAt_log hx.ne').mul h_rpow).neg.div_const (p - 1)).sub
    (h_rpow.div_const ((p - 1) ^ 2))
  have e1 : x ^ (-(p - 1) - 1) = (x ^ p)⁻¹ := by rw [show -(p - 1) - 1 = -p by ring, rpow_neg hx.le]
  have e2 : x ^ (-(p - 1)) = x / x ^ p := by
    rw [show -(p - 1) = 1 - p by ring, rpow_sub hx, rpow_one]
  have hxp : 0 < x ^ p := rpow_pos_of_pos hx p
  convert h using 1
  simp only [e1, e2]
  field_simp
  ring

/-- For `p > 1`, the partial sums of `∑ 1 / n ^ p` are at most `1 + 1 / (p - 1)`. -/
theorem sum_range_one_div_nat_rpow_le (hp : 1 < p) (N : ℕ) :
    ∑ n ∈ range N, 1 / (n : ℝ) ^ p ≤ 1 + 1 / (p - 1) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have h_anti : AntitoneOn (fun x : ℝ ↦ 1 / x ^ p) (Icc 1 (1 + N)) := fun x hx y _ hxy ↦
    one_div_le_one_div_of_le (rpow_pos_of_pos (by linarith [hx.1]) p)
      (rpow_le_rpow (by linarith [hx.1]) hxy hp0.le)
  -- the terms of index `n ≥ 2` are at most the integral of `1 / x ^ p` over `[n - 1, n]`
  have h_int : ∫ x in (1 : ℝ)..1 + N, 1 / x ^ p = ((1 + N : ℝ) ^ (1 - p) - 1) / (1 - p) := by
    have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (N : ℝ)) := by
      rw [Set.uIcc_of_le (by simp)]
      exact fun h ↦ by linarith [h.1]
    rw [intervalIntegral.integral_congr (g := fun x : ℝ ↦ x ^ (-p)) fun x hx ↦ ?_,
      integral_rpow (Or.inr ⟨by linarith, h0⟩), show -p + 1 = 1 - p by ring, one_rpow]
    rw [Set.uIcc_of_le (by simp)] at hx
    simp only [one_div, rpow_neg (by linarith [hx.1] : (0 : ℝ) ≤ x)]
  have h_sum := h_anti.sum_le_integral
  rw [h_int] at h_sum
  have h_pos : 0 ≤ (1 + N : ℝ) ^ (1 - p) / (p - 1) := by positivity
  have h_eq : ((1 + N : ℝ) ^ (1 - p) - 1) / (1 - p) =
      1 / (p - 1) - (1 + N : ℝ) ^ (1 - p) / (p - 1) := by
    rw [← neg_sub p 1, div_neg, ← neg_div, neg_sub, sub_div]
  rw [h_eq] at h_sum
  calc ∑ n ∈ range N, 1 / (n : ℝ) ^ p
  _ ≤ ∑ n ∈ range (2 + N), 1 / (n : ℝ) ^ p :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun _ _ _ ↦ by positivity
  _ = 1 + ∑ i ∈ range N, 1 / (1 + ((i + 1 : ℕ) : ℝ)) ^ p := by
    have h_cast (i : ℕ) : ((2 + i : ℕ) : ℝ) = 1 + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [sum_range_add]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      zero_rpow hp0.ne', div_zero, one_rpow, div_one, h_cast]
    ring
  _ ≤ 1 + 1 / (p - 1) := by linarith

/-- For `p > 1`, `∑_{n ≥ 1} 1 / n ^ p ≤ 1 + 1 / (p - 1)`. -/
theorem tsum_one_div_nat_rpow_le (hp : 1 < p) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ p ≤ 1 + 1 / (p - 1) :=
  tsum_le_of_sum_range_le (fun _ ↦ by positivity) (sum_range_one_div_nat_rpow_le hp)

/-- For `p > 1`, the partial sums of `∑ log n / n ^ p` are at most `1 + 1 / (p - 1) ^ 2`. -/
theorem sum_range_log_div_nat_rpow_le (hp : 1 < p) (N : ℕ) :
    ∑ n ∈ range N, log n / (n : ℝ) ^ p ≤ 1 + 1 / (p - 1) ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  -- `log x / x ^ p` is antitone on `[e ^ (1 / p), ∞) ⊇ [3, ∞)`
  have h3 : exp p⁻¹ ≤ 3 := by
    have := exp_one_lt_d9
    have : exp p⁻¹ ≤ exp 1 := exp_le_exp.2 (inv_le_one_of_one_le₀ hp.le)
    linarith
  have h_anti : AntitoneOn (fun x : ℝ ↦ log x / x ^ p) (Icc 3 (3 + N)) :=
    (log_div_self_rpow_antitoneOn hp0).mono fun x hx ↦ h3.trans hx.1
  -- the terms of index `n ≥ 4` are at most the integral of `log x / x ^ p` over `[n - 1, n]`
  set G : ℝ → ℝ := fun y ↦ -(log y * y ^ (-(p - 1))) / (p - 1) - y ^ (-(p - 1)) / (p - 1) ^ 2
  have h_int : ∫ x in (3 : ℝ)..3 + N, log x / x ^ p = G (3 + N) - G 3 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G) (fun x hx ↦ ?_)
      (h_anti.mono (Set.uIcc_of_le (by simp)).subset).intervalIntegrable
    rw [Set.uIcc_of_le (by simp)] at hx
    exact hasDerivAt_neg_log_mul_rpow_div (by linarith [hx.1]) hp.ne'
  have h_sum := h_anti.sum_le_integral
  rw [h_int] at h_sum
  -- `G ≤ 0` on `[1, ∞)`, and `-G 3 = 3 ^ (-(p - 1)) (1 + (p - 1) log 3) / (p - 1) ^ 2`
  have hG : G (3 + N) ≤ 0 := by
    have : 0 ≤ log (3 + N) := log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
    have : 0 ≤ (3 + N : ℝ) ^ (-(p - 1)) := by positivity
    simp only [G]
    have : 0 ≤ log (3 + N) * (3 + N : ℝ) ^ (-(p - 1)) / (p - 1) := by positivity
    have : 0 ≤ (3 + N : ℝ) ^ (-(p - 1)) / (p - 1) ^ 2 := by positivity
    rw [neg_div]
    linarith
  have hG3 : -G 3 ≤ 1 / (p - 1) ^ 2 := by
    have h_rpow : (3 : ℝ) ^ (-(p - 1)) = exp (-((p - 1) * log 3)) := by
      rw [rpow_def_of_pos (by norm_num)]
      ring_nf
    have h_exp : exp (-((p - 1) * log 3)) * (1 + (p - 1) * log 3) ≤ 1 := by
      calc exp (-((p - 1) * log 3)) * (1 + (p - 1) * log 3)
      _ ≤ exp (-((p - 1) * log 3)) * exp ((p - 1) * log 3) := by
        gcongr
        linarith [add_one_le_exp ((p - 1) * log 3)]
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    have h_eq : -G 3 = exp (-((p - 1) * log 3)) * (1 + (p - 1) * log 3) / (p - 1) ^ 2 := by
      simp only [G, h_rpow]
      field_simp
      ring
    rw [h_eq]
    gcongr
  -- the terms of index `2` and `3` are at most `1 / e` each
  have h2 := log_div_rpow_le_exp_neg_one (x := 2) (by norm_num) hp.le
  have h3' := log_div_rpow_le_exp_neg_one (x := 3) (by norm_num) hp.le
  have he : exp (-1) ≤ 1 / 2 := by
    rw [exp_neg, one_div]
    have := exp_one_gt_d9
    exact inv_anti₀ (by norm_num) (by linarith)
  calc ∑ n ∈ range N, log n / (n : ℝ) ^ p
  _ ≤ ∑ n ∈ range (4 + N), log n / (n : ℝ) ^ p :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun n _ _ ↦
      div_nonneg (log_natCast_nonneg n) (by positivity)
  _ = log 2 / 2 ^ p + log 3 / 3 ^ p +
      ∑ i ∈ range N, log (3 + ((i + 1 : ℕ) : ℝ)) / (3 + ((i + 1 : ℕ) : ℝ)) ^ p := by
    have h_cast (i : ℕ) : ((4 + i : ℕ) : ℝ) = 3 + ((i + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [sum_range_add]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, log_zero,
      log_one, zero_div, Nat.cast_ofNat, h_cast]
    ring
  _ ≤ 1 + 1 / (p - 1) ^ 2 := by linarith

/-- For `p > 1`, the series `∑ log n / n ^ p` converges. -/
theorem summable_log_div_nat_rpow (hp : 1 < p) : Summable fun n : ℕ ↦ log n / (n : ℝ) ^ p :=
  summable_of_sum_range_le (fun n ↦ div_nonneg (log_natCast_nonneg n) (by positivity))
    (sum_range_log_div_nat_rpow_le hp)

/-- For `p > 1`, `∑_{n ≥ 2} log n / n ^ p ≤ 1 + 1 / (p - 1) ^ 2`. -/
theorem tsum_log_div_nat_rpow_le (hp : 1 < p) :
    ∑' n : ℕ, log n / (n : ℝ) ^ p ≤ 1 + 1 / (p - 1) ^ 2 :=
  tsum_le_of_sum_range_le (fun n ↦ div_nonneg (log_natCast_nonneg n) (by positivity))
    (sum_range_log_div_nat_rpow_le hp)

end Real
