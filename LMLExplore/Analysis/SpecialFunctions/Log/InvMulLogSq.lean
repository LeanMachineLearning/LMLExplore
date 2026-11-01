/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import LMLExplore.Analysis.SpecialFunctions.Exp

/-!
# Sums of `1 / (t log² t)`

The series `∑ 1 / (t log² t)` converges, and its tail from `T` is of order `1 / log T`. This file
proves the explicit telescoping bound `1 / (t log² t) ≤ 1 / log (t - 1/2) - 1 / log (t + 1/2)`
for `t ≥ 2`, and from it the numerical bound
`∑_{t ≥ 1} 1 / (1 + t log² t) ≤ 5 / 2`.

The function `f(t) = 1 + t log² t` is the exploration function of the asymptotically optimal UCB
algorithm [LS, Algorithm 6], and the bound `∑_t 1 / f(t) ≤ 5 / 2` gives the constant `5 σ² / ε²` of
[LS, Theorem 8.1]: with the bound `∑_{s ≥ 1} exp (-s ε² / (2 σ²)) ≤ 2 σ² / ε²` on the sub-Gaussian
tails, `∑_{t ≥ 1} 1 / f(t) ∑_{s ≥ 1} exp (-s ε² / (2 σ²)) ≤ 5 σ² / ε²` [LS, Exercise 8.1]. The true
value of the sum `∑_{t ≥ 1} 1 / f(t)` is about `2.4919`.

## Main statements

* `Real.inv_mul_log_sq_le_inv_log_sub_inv_log`: the telescoping bound.
* `Real.sum_range_inv_mul_log_sq_le`: the tail bound
  `∑_{i < m} 1 / ((T + i) log² (T + i)) ≤ 1 / log (T - 1/2)` for `T ≥ 2`.
* `Real.sum_range_inv_one_add_mul_log_sq_le`: `∑_{t < n} 1 / (1 + (t + 1) log² (t + 1)) ≤ 5 / 2`.
* `Real.sum_range_inv_mul_sum_range_exp_neg_le`: [LS, Exercise 8.1], the bound
  `∑_{t ≤ n} 1 / f(t) ∑_{s ≤ m} exp (-c s) ≤ 5 / (2 c)` for `c > 0`, which is `5 σ² / ε²` for the
  sub-Gaussian rate `c = ε² / (2 σ²)`.

## Implementation notes

The numerical bound sums the first eight terms exactly, with the lower bounds on `log 2`, `log 3`
and `log 5` of `Mathlib.Analysis.Complex.ExponentialBounds` and lower bounds on `log 7` and
`log (17 / 2)` from `Real.le_log_one_add_of_nonneg`, and bounds the rest by the telescoping sum
`Real.sum_range_inv_mul_log_sq_le` for `T = 9`, which is at most `1 / log (17 / 2)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset

namespace Real

/-- For `t ≥ 2`, `1 / (t log² t) ≤ 1 / log (t - 1/2) - 1 / log (t + 1/2)`, so that the tail
`∑_{t > T} 1 / (t log² t)` is at most `1 / log (T + 1/2)`. -/
theorem inv_mul_log_sq_le_inv_log_sub_inv_log {t : ℝ} (ht : 2 ≤ t) :
    (t * log t ^ 2)⁻¹ ≤ (log (t - 1 / 2))⁻¹ - (log (t + 1 / 2))⁻¹ := by
  have ha : 0 < log (t - 1 / 2) := log_pos (by linarith)
  have hb : 0 < log (t + 1 / 2) := log_pos (by linarith)
  have hlogt : 0 < log t := log_pos (by linarith)
  -- `log (t + 1/2) - log (t - 1/2) = log (1 + 1 / (t - 1/2)) ≥ 1 / t`
  have h_sub : t⁻¹ ≤ log (t + 1 / 2) - log (t - 1 / 2) := by
    set u := t - 1 / 2 with hu
    have hu0 : 0 < u := by linarith
    have h := le_log_one_add_of_nonneg (inv_nonneg.mpr hu0.le)
    have e1 : 1 + u⁻¹ = (t + 1 / 2) / u := by
      rw [show t + 1 / 2 = u + 1 by linarith]
      field_simp
    have e2 : 2 * u⁻¹ / (u⁻¹ + 2) = t⁻¹ := by
      rw [show t = u + 1 / 2 by linarith]
      field_simp
      ring
    rwa [← log_div (by linarith) hu0.ne', ← e1, ← e2]
  -- `log (t - 1/2) log (t + 1/2) ≤ log² t`, since `log (t - 1/2) + log (t + 1/2) ≤ 2 log t`
  have h_add : log (t - 1 / 2) + log (t + 1 / 2) ≤ 2 * log t := by
    rw [← log_mul (by linarith) (by linarith), show 2 * log t = log (t ^ 2) by simp [log_pow]]
    exact log_le_log (by nlinarith) (by nlinarith)
  have h_mul : log (t - 1 / 2) * log (t + 1 / 2) ≤ log t ^ 2 := by
    nlinarith [sq_nonneg (log (t - 1 / 2) - log (t + 1 / 2))]
  rw [inv_sub_inv ha.ne' hb.ne', inv_eq_one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (log (t - 1 / 2) * log (t + 1 / 2))
  _ ≤ log t ^ 2 := by linarith
  _ = t * log t ^ 2 * t⁻¹ := by field_simp
  _ ≤ t * log t ^ 2 * (log (t + 1 / 2) - log (t - 1 / 2)) := by gcongr
  _ = (log (t + 1 / 2) - log (t - 1 / 2)) * (t * log t ^ 2) := by ring

/-- For `T ≥ 2`, `∑_{i < m} 1 / ((T + i) log² (T + i)) ≤ 1 / log (T - 1/2)`, uniformly in `m`: the
terms telescope by `inv_mul_log_sq_le_inv_log_sub_inv_log`. -/
theorem sum_range_inv_mul_log_sq_le {T : ℝ} (hT : 2 ≤ T) (m : ℕ) :
    ∑ i ∈ range m, ((T + i) * log (T + i) ^ 2)⁻¹ ≤ (log (T - 1 / 2))⁻¹ := by
  set u : ℕ → ℝ := fun i ↦ (log (T + i - 1 / 2))⁻¹ with hu
  have h_le (i : ℕ) : ((T + i) * log (T + i) ^ 2)⁻¹ ≤ u i - u (i + 1) := by
    have h_succ : u (i + 1) = (log (T + i + 1 / 2))⁻¹ := by
      simp only [hu, Nat.cast_add_one]
      ring_nf
    rw [h_succ]
    exact inv_mul_log_sq_le_inv_log_sub_inv_log (by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
  have h0 : u 0 = (log (T - 1 / 2))⁻¹ := by simp [hu]
  have hm : 0 ≤ u m := inv_nonneg.mpr (log_nonneg (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]))
  refine (sum_le_sum fun i _ ↦ h_le i).trans ?_
  rw [sum_range_sub']
  linarith

/-- `∑_{t < n} 1 / (1 + (t + 1) log² (t + 1)) ≤ 5 / 2`: the sum of the inverses of the exploration
function `f(t) = 1 + t log² t` over the book rounds `t ≥ 1` is at most `5 / 2`, the numerical part
of [LS, Exercise 8.1]. -/
theorem sum_range_inv_one_add_mul_log_sq_le (n : ℕ) :
    ∑ t ∈ range n, (1 + (t + 1) * log (t + 1) ^ 2)⁻¹ ≤ 5 / 2 := by
  set g : ℕ → ℝ := fun t ↦ (1 + (t + 1) * log (t + 1) ^ 2)⁻¹ with hg
  have hg_nonneg t : 0 ≤ g t := by positivity
  -- the terms from `t = 8` on telescope, with sum at most `1 / log (17 / 2)`
  have h_tail (m : ℕ) : ∑ i ∈ range m, g (8 + i) ≤ (log (17 / 2))⁻¹ := by
    refine (sum_le_sum fun i _ ↦ ?_).trans
      ((sum_range_inv_mul_log_sq_le (T := 9) (by norm_num) m).trans_eq (by norm_num))
    have e : ((8 + i : ℕ) : ℝ) + 1 = 9 + i := by
      push_cast
      ring
    have hlog : 0 < log (9 + i) := log_pos (by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
    simp only [hg, e]
    gcongr
    linarith
  -- the first eight terms, with lower bounds on the logarithms
  have h2 : (0.6931 : ℝ) ≤ log 2 := log_two_gt_d9.le.trans' (by norm_num)
  have h3 : (1.0986 : ℝ) ≤ log 3 := log_three_gt_d9.le.trans' (by norm_num)
  have h5 : (1.6094 : ℝ) ≤ log 5 := log_five_gt_d9.le.trans' (by norm_num)
  have h4 : log 4 = 2 * log 2 := log_four_eq
  have h6 : log 6 = log 2 + log 3 := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  have h8 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    norm_num
  have h7 : (1.9455 : ℝ) ≤ log 7 := by
    have h := le_log_one_add_of_nonneg (x := 6⁻¹) (by norm_num)
    have : log 7 = log 6 + log (1 + 6⁻¹) := by
      rw [← log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [this, h6]
    norm_num at h ⊢
    linarith
  have h17 : (2.1399 : ℝ) ≤ log (17 / 2) := by
    have h := le_log_one_add_of_nonneg (x := 16⁻¹) (by norm_num)
    have : log (17 / 2) = log 8 + log (1 + 16⁻¹) := by
      rw [← log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [this, h8]
    norm_num at h ⊢
    linarith
  have k0 : g 0 = 1 := by norm_num [hg]
  have k1 : g 1 ≤ (1 + 2 * 0.6931 ^ 2 : ℝ)⁻¹ := by
    rw [show g 1 = (1 + 2 * log 2 ^ 2)⁻¹ by norm_num [hg]]
    gcongr
  have k2 : g 2 ≤ (1 + 3 * 1.0986 ^ 2 : ℝ)⁻¹ := by
    rw [show g 2 = (1 + 3 * log 3 ^ 2)⁻¹ by norm_num [hg]]
    gcongr
  have k3 : g 3 ≤ (1 + 4 * (2 * 0.6931) ^ 2 : ℝ)⁻¹ := by
    rw [show g 3 = (1 + 4 * (2 * log 2) ^ 2)⁻¹ by norm_num [hg, h4]]
    gcongr
  have k4 : g 4 ≤ (1 + 5 * 1.6094 ^ 2 : ℝ)⁻¹ := by
    rw [show g 4 = (1 + 5 * log 5 ^ 2)⁻¹ by norm_num [hg]]
    gcongr
  have k5 : g 5 ≤ (1 + 6 * (0.6931 + 1.0986) ^ 2 : ℝ)⁻¹ := by
    rw [show g 5 = (1 + 6 * (log 2 + log 3) ^ 2)⁻¹ by norm_num [hg, h6]]
    gcongr
  have k6 : g 6 ≤ (1 + 7 * 1.9455 ^ 2 : ℝ)⁻¹ := by
    rw [show g 6 = (1 + 7 * log 7 ^ 2)⁻¹ by norm_num [hg]]
    gcongr
  have k7 : g 7 ≤ (1 + 8 * (3 * 0.6931) ^ 2 : ℝ)⁻¹ := by
    rw [show g 7 = (1 + 8 * (3 * log 2) ^ 2)⁻¹ by norm_num [hg, h8]]
    gcongr
  have h_head : ∑ t ∈ range 8, g t ≤ 2.0271 := by
    simp only [sum_range_succ, sum_range_zero]
    norm_num at k1 k2 k3 k4 k5 k6 k7
    linarith
  have h_inv17 : (log (17 / 2))⁻¹ ≤ (2.1399 : ℝ)⁻¹ := by gcongr
  calc ∑ t ∈ range n, g t
  _ ≤ ∑ t ∈ range (8 + n), g t :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun t _ _ ↦ hg_nonneg t
  _ = ∑ t ∈ range 8, g t + ∑ i ∈ range n, g (8 + i) := sum_range_add g 8 n
  _ ≤ 2.0271 + (2.1399 : ℝ)⁻¹ := add_le_add h_head ((h_tail n).trans h_inv17)
  _ ≤ 5 / 2 := by norm_num

/-- **[LS, Exercise 8.1]** For `c > 0`,
`∑_{t ≤ n} 1 / f(t) ∑_{s ≤ m} exp (-c s) ≤ 5 / (2 c)` (book indices `t, s ≥ 1`), uniformly in `n`
and `m`, where `f(t) = 1 + t log² t` is the exploration function of [LS, Algorithm 6]. For the
sub-Gaussian rate `c = ε² / (2 σ²)` the bound is `5 σ² / ε²`. -/
theorem sum_range_inv_mul_sum_range_exp_neg_le {c : ℝ} (hc : 0 < c) (n m : ℕ) :
    ∑ t ∈ range n, (1 + (t + 1) * log (t + 1) ^ 2)⁻¹ * ∑ s ∈ range m, exp (-(c * (s + 1))) ≤
      5 / 2 * c⁻¹ := by
  rw [← sum_mul]
  gcongr
  · exact sum_range_inv_one_add_mul_log_sq_le n
  · exact sum_range_exp_neg_mul_le hc m

end Real
