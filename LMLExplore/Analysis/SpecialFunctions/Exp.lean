/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Sums of exponentials and a quadratic bound on `exp (-x)`

The geometric sum `∑_{s ≥ 1} exp (-c s) = 1 / (exp c - 1)` is at most `1 / c` for `c > 0`. This is
the form in which the sums over the sample sizes of sub-Gaussian tail bounds `exp (-s ε² / (2 σ²))`
are bounded, for example in the proof of [LS, Theorem 8.1].

Along a geometric grid of sample sizes `2 ^ j`, the sum `∑_j 2 ^ j exp (-2 ^ j c)` is at most
`3 / (2 c)` for `c > 0`. This bounds the sums produced by the peeling device, which splits the
sample sizes into the blocks `[2 ^ j, 2 ^ (j + 1))`, as in the proof of [LS, Lemma 9.3].

The sample sizes `s` at which a deviation bound gives nothing, because `(s + 1) D ≤ L` for a
divergence `D > 0` and a confidence level `L ≥ 0`, number at most `L / D`. Together with the
geometric sum above, this bounds the sums over the sample sizes in the proof of [LS, Lemma 10.8].

The tail `∑_{s ≥ m} exp (-s d)` of the geometric series is `exp (-m d) / (1 - exp (-d))`, and a
sequence `exp (-f n)` is summable as soon as `f n` grows faster than `log n`, for then
`exp (-f n) ≤ 1 / n²` eventually. With `f n = c m n` for a number `m n` of samples, this sums
tail bounds `exp (-c m n)` over a sequence of experiments whose sample sizes grow faster than
logarithmically.

For `x ≥ 0`, `exp (-x) ≤ 1 - x + x ^ 2 / 2`, the second-order bound that controls the growth of
the potential of exponential weights fed with nonnegative losses. Conversely, discounting the
argument of the exponential turns `1 + x` into an upper bound near `0`: `exp (x / (1 + l)) ≤ 1 + x`
for `0 ≤ x ≤ 2 l` [LS, Lemma 12.5], which controls the exponential moments of the
implicit-exploration estimates of Exp3-IX.

## Main statements

* `Real.sum_range_exp_neg_mul_le`: `∑_{s < m} exp (-c (s + 1)) ≤ 1 / c` for `c > 0`.
* `Real.sum_range_two_pow_mul_exp_neg_le`: `∑_{j < m} 2 ^ j exp (-2 ^ j c) ≤ 3 / (2 c)` for
  `c > 0`.
* `Real.sum_range_ite_add_one_mul_le_le`: `#{s < k | (s + 1) D ≤ L} ≤ L / D` for `D > 0` and
  `L ≥ 0`.
* `Real.hasSum_exp_neg_add_mul`: `∑_{k ≥ 0} exp (-(k + m) d) = exp (-m d) / (1 - exp (-d))` for
  `d > 0`.
* `Real.exp_neg_mul_div_one_sub_exp_neg_nonneg`: the terms `exp (-x d) / (1 - exp (-d))` of these
  tail sums are nonnegative for `d ≥ 0`.
* `Real.summable_exp_neg_of_tendsto_div_log`: `∑ n, exp (-f n) < ∞` if `f n / log n → ∞`.
* `Real.exp_neg_le_one_sub_add_sq_div_two`: `exp (-x) ≤ 1 - x + x ^ 2 / 2` for `x ≥ 0`.
* `Real.exp_div_one_add_le_one_add`: `exp (x / (1 + l)) ≤ 1 + x` for `0 ≤ x ≤ 2 l`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset Filter

namespace Real

/-- For `c > 0`, `∑_{s < m} exp (-c (s + 1)) ≤ 1 / c`, uniformly in `m`. -/
theorem sum_range_exp_neg_mul_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∑ s ∈ range m, exp (-(c * (s + 1))) ≤ c⁻¹ := by
  -- each term is at most `v s - v (s + 1)` for `v s = exp (-c s) / c`, since `1 + c ≤ exp c`
  set v : ℕ → ℝ := fun s ↦ exp (-(c * s)) / c with hv
  have h_le (s : ℕ) : exp (-(c * (s + 1))) ≤ v s - v (s + 1) := by
    have h := add_one_le_exp c
    simp only [hv, Nat.cast_add_one]
    rw [← sub_div, le_div_iff₀ hc, show -(c * (s + 1)) = -(c * s) + -c by ring, exp_add]
    have h1 : exp (-c) * (c + 1) ≤ 1 := by
      calc exp (-c) * (c + 1)
      _ ≤ exp (-c) * exp c := by gcongr
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    nlinarith [mul_le_mul_of_nonneg_left h1 (exp_pos (-(c * s))).le]
  calc ∑ s ∈ range m, exp (-(c * (s + 1)))
  _ ≤ ∑ s ∈ range m, (v s - v (s + 1)) := sum_le_sum fun s _ ↦ h_le s
  _ = v 0 - v m := sum_range_sub' v m
  _ ≤ c⁻¹ := by
    have : 0 ≤ v m := by positivity
    simp only [hv, CharP.cast_eq_zero, mul_zero, neg_zero, exp_zero, one_div] at this ⊢
    linarith

/-- For `c > 0`, `∑_{j < m} 2 ^ j exp (-2 ^ j c) ≤ 3 / (2 c)`, uniformly in `m`. -/
theorem sum_range_two_pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∑ j ∈ range m, 2 ^ j * exp (-(2 ^ j * c)) ≤ 3 / (2 * c) := by
  -- each term is at most `v j - v (j + 1)` for `v j = 3 exp (-2 ^ (j + 1) c / 3) / (2 c)`,
  -- since `y ≤ sinh y` for `y = 2 ^ j c / 3 ≥ 0`
  set v : ℕ → ℝ := fun j ↦ 3 / (2 * c) * exp (-(2 ^ (j + 1) * c / 3)) with hv
  have h_le (j : ℕ) : 2 ^ j * exp (-(2 ^ j * c)) ≤ v j - v (j + 1) := by
    set y : ℝ := 2 ^ j * c / 3 with hy
    have h_sinh : y ≤ sinh y := self_le_sinh_iff.2 (by positivity)
    have h1 : exp (-(2 ^ (j + 1) * c / 3)) = exp (-(2 ^ j * c)) * exp y := by
      rw [← exp_add, hy, pow_succ]
      ring_nf
    have h2 : exp (-(2 ^ (j + 1 + 1) * c / 3)) = exp (-(2 ^ j * c)) * exp (-y) := by
      rw [← exp_add, hy, pow_succ, pow_succ]
      ring_nf
    have h3 : (2 : ℝ) ^ j = 3 * y / c := by
      rw [hy]
      field_simp
    simp only [hv, h1, h2]
    set E := exp (-(2 ^ j * c))
    have hE : 0 < E := exp_pos _
    rw [sinh_eq] at h_sinh
    have h_eq : 3 / (2 * c) * (E * exp y) - 3 / (2 * c) * (E * exp (-y)) - 3 * y / c * E
        = 3 * E * (exp y - exp (-y) - 2 * y) / (2 * c) := by
      field_simp
    have h_nonneg : 0 ≤ 3 * E * (exp y - exp (-y) - 2 * y) / (2 * c) := by
      have : 0 ≤ exp y - exp (-y) - 2 * y := by linarith
      positivity
    rw [h3]
    linarith
  calc ∑ j ∈ range m, 2 ^ j * exp (-(2 ^ j * c))
  _ ≤ ∑ j ∈ range m, (v j - v (j + 1)) := sum_le_sum fun j _ ↦ h_le j
  _ = v 0 - v m := sum_range_sub' v m
  _ ≤ 3 / (2 * c) := by
    have h0 : 0 ≤ v m := by positivity
    have h1 : v 0 ≤ 3 / (2 * c) := by
      simp only [hv]
      refine mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 ?_)
      rw [neg_nonpos]
      positivity
    linarith

/-- The number of `s < k` with `(s + 1) D ≤ L` is at most `L / D`, for `D > 0` and `L ≥ 0`. -/
theorem sum_range_ite_add_one_mul_le_le {D L : ℝ} (hD : 0 < D) (hL : 0 ≤ L) (k : ℕ) :
    ∑ s ∈ range k, (if (s + 1) * D ≤ L then (1 : ℝ) else 0) ≤ L / D := by
  rw [sum_boole]
  refine le_trans ?_ (Nat.floor_le (div_nonneg hL hD.le))
  refine Nat.cast_le.2 ((card_le_card fun s hs ↦ ?_).trans (card_range _).le)
  rw [mem_filter] at hs
  rw [Finset.mem_range, Nat.lt_iff_add_one_le]
  refine Nat.le_floor ?_
  rw [le_div_iff₀ hD]
  exact_mod_cast hs.2

/-- The tail `∑_{s ≥ m} exp (-s d)` of a geometric series: for `d > 0`,
`∑_{k ≥ 0} exp (-(k + m) d) = exp (-m d) / (1 - exp (-d))`. -/
theorem hasSum_exp_neg_add_mul {d : ℝ} (hd : 0 < d) (m : ℕ) :
    HasSum (fun k : ℕ ↦ exp (-((k + m) * d))) (exp (-(m * d)) / (1 - exp (-d))) := by
  have h_eq (k : ℕ) : exp (-((k + m) * d)) = exp (-(m * d)) * exp (-d) ^ k := by
    rw [← exp_nat_mul, ← exp_add]
    ring_nf
  simp_rw [h_eq, div_eq_mul_inv]
  exact (hasSum_geometric_of_lt_one (exp_pos _).le (exp_lt_one_iff.2 (neg_lt_zero.2 hd))).mul_left _

/-- The terms `exp (-x d) / (1 - exp (-d))` of the tail bounds of `hasSum_exp_neg_add_mul` are
nonnegative, for `d ≥ 0`. -/
theorem exp_neg_mul_div_one_sub_exp_neg_nonneg {d : ℝ} (hd : 0 ≤ d) (x : ℝ) :
    0 ≤ exp (-(x * d)) / (1 - exp (-d)) :=
  div_nonneg (exp_pos _).le (sub_nonneg.2 (exp_le_one_iff.2 (neg_nonpos.2 hd)))

/-- If `f n` grows faster than `log n`, that is `f n / log n → ∞`, then `exp (-f n)` is
summable. -/
theorem summable_exp_neg_of_tendsto_div_log {f : ℕ → ℝ}
    (hf : Tendsto (fun n : ℕ ↦ f n / log n) atTop atTop) : Summable fun n ↦ exp (-f n) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ ↦ 1 / (n : ℝ) ^ 2)
    (summable_one_div_nat_pow.2 one_lt_two) ?_
  filter_upwards [hf.eventually_ge_atTop 2, eventually_ge_atTop 2] with n hn hn2
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn2
  rw [le_div_iff₀ (log_pos hn1)] at hn
  rw [norm_of_nonneg (exp_pos _).le, one_div, ← exp_log (zero_lt_one.trans hn1), ← exp_nat_mul,
    ← exp_neg, Nat.cast_ofNat]
  exact exp_le_exp.2 (neg_le_neg hn)

/-- For `x ≥ 0`, `exp (-x) ≤ 1 - x + x ^ 2 / 2`. -/
theorem exp_neg_le_one_sub_add_sq_div_two {x : ℝ} (hx : 0 ≤ x) :
    exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  -- `exp x ≥ 1 + x + x ^ 2 / 2` and `(1 + x + x ^ 2 / 2) (1 - x + x ^ 2 / 2) = 1 + x ^ 4 / 4`
  have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
  calc exp (-x) = (exp x)⁻¹ := exp_neg x
  _ ≤ (1 + x + x ^ 2 / 2)⁻¹ := inv_anti₀ hpos (quadratic_le_exp_of_nonneg hx)
  _ ≤ 1 - x + x ^ 2 / 2 := by
    rw [inv_le_iff_one_le_mul₀' hpos]
    nlinarith [pow_nonneg hx 4]

/-- For `0 ≤ x ≤ 2 l`, `exp (x / (1 + l)) ≤ 1 + x` [LS, Lemma 12.5]. -/
theorem exp_div_one_add_le_one_add {x l : ℝ} (hx : 0 ≤ x) (hxl : x ≤ 2 * l) :
    exp (x / (1 + l)) ≤ 1 + x := by
  -- `x / (1 + l) ≤ 2 x / (x + 2) ≤ log (1 + x)`
  rw [← exp_log (by linarith : 0 < 1 + x), exp_le_exp]
  refine le_trans ?_ (le_log_one_add_of_nonneg hx)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg hx (sub_nonneg.2 hxl)]

end Real
