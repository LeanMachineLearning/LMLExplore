/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Sums of exponentials and quadratic bounds on the exponential

The geometric sum `∑_{s ≥ 1} exp (-c s) = 1 / (exp c - 1)` is at most `1 / c` for `c > 0`. This is
the form in which the sums over the sample sizes of sub-Gaussian tail bounds `exp (-s ε² / (2 σ²))`
are bounded, for example in the proof of [LS, Theorem 8.1]. Weighting the terms by `1 / s` gives
the logarithmic series `∑_{s ≥ 1} exp (-c s) / s = -log (1 - exp (-c))`, at most
`log (1 + 1 / c)`; it bounds the sums over the sample sizes of terms of order
`exp (-s ε² / (2 σ²)) / (s ε² / σ²)` in the analysis of Thompson sampling [LS, Exercise 36.6].

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

Above its affine part, the exponential grows like its second-order term up to a factor that
increases with the argument: `x ↦ (exp x - 1 - x) / x ^ 2` is monotone on `[0, ∞)`, as the series
`∑_j x ^ j / (j + 2)!` with nonnegative coefficients. Hence, for `b > 0`, `l ≥ 0` and `x ≤ b`,
`exp (l x) ≤ 1 + l x + ψ x ^ 2` with `ψ = (exp (l b) - 1 - l b) / b ^ 2`
[BLM13, proof of Theorem 2.9], the one-step bound behind the inequalities of Bennett, Bernstein
and Freedman. Comparing the series
with a geometric one gives `exp x - 1 - x ≤ x ^ 2 / (2 (1 - x / 3))` for `0 ≤ x < 3`, which turns
these into Bernstein's form, and inverts in closed form at Chernoff's choice of parameter.

By the convexity of the exponential, a sum of exponentials is at least its number of terms times
the exponential of the mean of the exponents. This spreads a bound on a sum of divergences
`∑ i D i` across the terms of a sum of Bretagnolle–Huber bounds `∑ i exp (-D i)`, in the minimax
lower bound for linear bandits on the unit ball [LS, Theorem 24.2].

## Main statements

* `Real.sum_range_exp_neg_mul_le`: `∑_{s < m} exp (-c (s + 1)) ≤ 1 / c` for `c > 0`.
* `Real.sum_range_exp_neg_mul_div_le`: `∑_{s < m} exp (-c (s + 1)) / (s + 1) ≤ log (1 + 1 / c)`
  for `c > 0`.
* `Real.sum_range_two_pow_mul_exp_neg_le`: `∑_{j < m} 2 ^ j exp (-2 ^ j c) ≤ 3 / (2 c)` for
  `c > 0`.
* `Real.sum_range_ite_add_one_mul_le_le`: `#{s < k | (s + 1) D ≤ L} ≤ L / D` for `D > 0` and
  `L ≥ 0`.
* `Real.sum_range_ite_mul_le_exp_neg_mul_le`: `∑_{s < n} (1 if s D ≤ L, else exp (-c s))` is at
  most `1 + L / D + 1 / c` for `D, c > 0` and `L ≥ 0`.
* `Real.hasSum_exp_neg_add_mul`: `∑_{k ≥ 0} exp (-(k + m) d) = exp (-m d) / (1 - exp (-d))` for
  `d > 0`.
* `Real.exp_neg_mul_div_one_sub_exp_neg_nonneg`: the terms `exp (-x d) / (1 - exp (-d))` of these
  tail sums are nonnegative for `d ≥ 0`.
* `Real.summable_exp_neg_of_tendsto_div_log`: `∑ n, exp (-f n) < ∞` if `f n / log n → ∞`.
* `Real.exp_neg_le_one_sub_add_sq_div_two`: `exp (-x) ≤ 1 - x + x ^ 2 / 2` for `x ≥ 0`.
* `Real.exp_div_one_add_le_one_add`: `exp (x / (1 + l)) ≤ 1 + x` for `0 ≤ x ≤ 2 l`.
* `Real.hasSum_pow_add_two_div_factorial`: `∑_j x ^ (j + 2) / (j + 2)! = exp x - 1 - x`.
* `Real.exp_sub_one_sub_id_div_sq_nonneg`: `0 ≤ (exp x - 1 - x) / y ^ 2`.
* `Real.monotoneOn_exp_sub_one_sub_id_div_sq`: `x ↦ (exp x - 1 - x) / x ^ 2` is monotone on
  `[0, ∞)`.
* `Real.exp_mul_le_one_add_mul_add_mul_sq`: Bennett's bound
  `exp (l x) ≤ 1 + l x + (exp (l b) - 1 - l b) / b ^ 2 * x ^ 2` for `b > 0`, `l ≥ 0`, `x ≤ b`.
* `Real.exp_sub_one_sub_id_le_sq_div`: `exp x - 1 - x ≤ x ^ 2 / (2 (1 - x / 3))` for `0 ≤ x < 3`.
* `Real.exists_pos_le_mul_sqrt_add_sub_mul_exp_sub_one_sub`: the closed-form inversion of this
  sub-gamma bound, `L ≤ t (√(2 v L) + b L / 3) - v (exp (t b) - 1 - t b) / b ^ 2` for some `t > 0`.
* `Real.exp_neg_le_one_sub_add_sq`: `exp (-x) ≤ 1 - x + x ^ 2` for `x ≥ -1`.
* `Real.card_mul_exp_sum_div_card_le_sum_exp`: `#s exp ((∑ i ∈ s, x i) / #s) ≤ ∑ i ∈ s, exp (x i)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [BLM13] S. Boucheron, G. Lugosi and P. Massart, *Concentration Inequalities*, Oxford University
  Press, 2013.
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

/-- For `c > 0`, `∑_{s < m} exp (-c (s + 1)) / (s + 1) ≤ log (1 + 1 / c)`, uniformly in `m`: the
series is the logarithmic series `-log (1 - exp (-c))`, and `1 - exp (-c) ≥ c / (1 + c)`. -/
theorem sum_range_exp_neg_mul_div_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∑ s ∈ range m, exp (-(c * (s + 1))) / (s + 1) ≤ log (1 + 1 / c) := by
  have hr1 : exp (-c) < 1 := exp_lt_one_iff.2 (by linarith)
  have h := hasSum_pow_div_log_of_abs_lt_one (abs_lt.2 ⟨by linarith [exp_pos (-c)], hr1⟩)
  have hterm (s : ℕ) : exp (-(c * (s + 1))) = exp (-c) ^ (s + 1) := by
    rw [← exp_nat_mul]
    push_cast
    ring_nf
  simp_rw [hterm]
  refine (sum_le_hasSum _ (fun _ _ ↦ by positivity) h).trans ?_
  rw [← log_inv]
  refine log_le_log (inv_pos.2 (by linarith)) ?_
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  -- `exp (-c) (1 + c) ≤ 1` since `1 + c ≤ exp c`
  have h1 : exp (-c) * (1 + c) ≤ 1 := by
    rw [exp_neg, inv_mul_le_iff₀ (exp_pos c), mul_one, add_comm]
    exact add_one_le_exp c
  field_simp
  nlinarith

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

/-- For `D, c > 0` and `L ≥ 0`, `∑_{s < n} (1 if s D ≤ L, else exp (-c s)) ≤ 1 + L / D + 1 / c`,
uniformly in `n`. -/
theorem sum_range_ite_mul_le_exp_neg_mul_le {D L c : ℝ} (hD : 0 < D) (hL : 0 ≤ L) (hc : 0 < c)
    (n : ℕ) :
    ∑ s ∈ range n, (if s * D ≤ L then 1 else exp (-(c * s))) ≤ 1 + L / D + c⁻¹ := by
  rcases n with _ | k
  · simp only [range_zero, sum_empty]
    positivity
  -- the term of `s = 0` is `1`, at most `L / D` other terms are `1`, and the others are bounded by
  -- the geometric series `∑_{s ≥ 1} exp (-c s) ≤ 1 / c`
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, hL, ite_true, Nat.cast_add_one]
  calc ∑ s ∈ range k, (if (s + 1) * D ≤ L then 1 else exp (-(c * (s + 1)))) + 1
  _ ≤ ∑ s ∈ range k, ((if (s + 1) * D ≤ L then (1 : ℝ) else 0) + exp (-(c * (s + 1)))) + 1 := by
    gcongr with s
    split_ifs <;> simp [exp_nonneg]
  _ ≤ L / D + c⁻¹ + 1 := by
    rw [sum_add_distrib]
    gcongr
    · exact sum_range_ite_add_one_mul_le_le hD hL k
    · exact sum_range_exp_neg_mul_le hc k
  _ = 1 + L / D + c⁻¹ := by ring

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

/-- The tail of the exponential series after its affine part: `exp x - 1 - x` is the sum of
`x ^ (j + 2) / (j + 2)!`. -/
theorem hasSum_pow_add_two_div_factorial (x : ℝ) :
    HasSum (fun j : ℕ ↦ x ^ (j + 2) / (j + 2).factorial) (exp x - 1 - x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rw [← exp_eq_exp_ℝ] at h
  rw [← hasSum_nat_add_iff' 2] at h
  simpa [sum_range_succ, sub_sub] using h

/-- The tail `exp x - 1 - x` of the exponential is nonnegative, so its quotient by a square is
nonnegative. -/
theorem exp_sub_one_sub_id_div_sq_nonneg (x y : ℝ) : 0 ≤ (exp x - 1 - x) / y ^ 2 :=
  div_nonneg (by linarith [add_one_le_exp x]) (sq_nonneg y)

/-- The function `x ↦ (exp x - 1 - x) / x ^ 2` is monotone on `[0, ∞)`. -/
theorem monotoneOn_exp_sub_one_sub_id_div_sq :
    MonotoneOn (fun x ↦ (exp x - 1 - x) / x ^ 2) (Set.Ici 0) := by
  intro u hu v hv huv
  simp only [Set.mem_Ici] at hu hv
  have hseries (x : ℝ) (hx : 0 < x) :
      HasSum (fun j : ℕ ↦ x ^ j / (j + 2).factorial) ((exp x - 1 - x) / x ^ 2) := by
    convert (hasSum_pow_add_two_div_factorial x).div_const (x ^ 2) using 1
    ext j
    field_simp
    ring
  rcases hu.eq_or_lt with rfl | hu'
  · simp only [zero_pow two_ne_zero, div_zero]
    exact exp_sub_one_sub_id_div_sq_nonneg v v
  · refine hasSum_le (fun j ↦ ?_) (hseries u hu') (hseries v (hu'.trans_le huv))
    gcongr

/-- For `0 ≤ x < 3`, `exp x - 1 - x ≤ x ^ 2 / (2 * (1 - x / 3))`, the bound on the exponential
behind Bernstein's inequality. -/
theorem exp_sub_one_sub_id_le_sq_div {x : ℝ} (hx : 0 ≤ x) (hx3 : x < 3) :
    exp x - 1 - x ≤ x ^ 2 / (2 * (1 - x / 3)) := by
  have hgeom : HasSum (fun j : ℕ ↦ x ^ 2 / 2 * (x / 3) ^ j) (x ^ 2 / 2 * (1 - x / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
  have hfact (j : ℕ) : (2 * 3 ^ j : ℝ) ≤ (j + 2).factorial := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      nlinarith
  calc exp x - 1 - x ≤ x ^ 2 / 2 * (1 - x / 3)⁻¹ := by
        refine hasSum_le (fun j ↦ ?_) (hasSum_pow_add_two_div_factorial x) hgeom
        rw [show x ^ 2 / 2 * (x / 3) ^ j = x ^ (j + 2) / (2 * 3 ^ j) by rw [div_pow, pow_add]; ring]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (hfact j)
    _ = x ^ 2 / (2 * (1 - x / 3)) := by
        have : 1 - x / 3 ≠ 0 := by linarith
        field_simp

/-- **Inversion of the sub-gamma bound**, Chernoff's choice of parameter in Bernstein's
inequality [BLM13, Theorem 2.10]: for `b, v, L > 0`, some `t > 0` has
`L ≤ t (√(2 v L) + b L / 3) - v ψ_b(t)`, with `ψ_b(t) = (exp (t b) - 1 - t b) / b ^ 2`. It is
`t = r / (v + b r / 3)` with `r = √(2 v L)`, at which the bound
`ψ_b(t) ≤ t ^ 2 / (2 (1 - t b / 3))` of `exp_sub_one_sub_id_le_sq_div` makes the right-hand
side at least `L`. -/
theorem exists_pos_le_mul_sqrt_add_sub_mul_exp_sub_one_sub {b v L : ℝ} (hb : 0 < b)
    (hv : 0 < v) (hL : 0 < L) :
    ∃ t, 0 < t ∧
      L ≤ t * (√(2 * v * L) + b * L / 3) - v * ((exp (t * b) - 1 - t * b) / b ^ 2) := by
  set r := √(2 * v * L)
  have hr : r ^ 2 = 2 * v * L := sq_sqrt (by positivity)
  have hr0 : 0 < r := sqrt_pos.2 (by positivity)
  obtain ⟨s, hs⟩ : ∃ s, s = v + b * r / 3 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  refine ⟨r / s, by positivity, ?_⟩
  have htb : r / s * b < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hs0]
    nlinarith
  have hψ : (exp (r / s * b) - 1 - r / s * b) / b ^ 2 ≤
      (r / s) ^ 2 / (2 * (1 - r / s * b / 3)) := by
    calc (exp (r / s * b) - 1 - r / s * b) / b ^ 2
        ≤ (r / s * b) ^ 2 / (2 * (1 - r / s * b / 3)) / b ^ 2 := by
          gcongr
          exact exp_sub_one_sub_id_le_sq_div (by positivity) htb
      _ = (r / s) ^ 2 / (2 * (1 - r / s * b / 3)) := by field_simp
  have h1 : 1 - r / s * b / 3 = v / s := by
    field_simp
    linear_combination 3 * hs
  have hval : r / s * (r + b * L / 3) - v * ((r / s) ^ 2 / (2 * (1 - r / s * b / 3))) = L := by
    have hv' : v ≠ 0 := hv.ne'
    rw [h1]
    field_simp
    linear_combination 3 * hr - 6 * L * hs
  linarith [mul_le_mul_of_nonneg_left hψ hv.le]

/-- **Bennett's bound on the exponential.** For `b > 0`, `l ≥ 0` and `x ≤ b`,
`exp (l x) ≤ 1 + l x + ψ x ^ 2` with `ψ = (exp (l b) - 1 - l b) / b ^ 2`. -/
theorem exp_mul_le_one_add_mul_add_mul_sq {b l x : ℝ} (hb : 0 < b) (hl : 0 ≤ l) (hx : x ≤ b) :
    exp (l * x) ≤ 1 + l * x + (exp (l * b) - 1 - l * b) / b ^ 2 * x ^ 2 := by
  rcases hl.eq_or_lt with rfl | hl
  · simp
  -- in the variables `u = l x ≤ v = l b`, the last term is `φ v * u ^ 2`, with
  -- `φ y = (exp y - 1 - y) / y ^ 2`
  have hv : 0 < l * b := mul_pos hl hb
  have hcoef : (exp (l * b) - 1 - l * b) / b ^ 2 * x ^ 2 =
      (exp (l * b) - 1 - l * b) / (l * b) ^ 2 * (l * x) ^ 2 := by
    field_simp
  rw [hcoef]
  rcases le_or_gt (l * x) 0 with hu | hu
  · -- `exp u ≤ 1 + u + u ^ 2 / 2` for `u ≤ 0`, and `φ v ≥ 1 / 2`
    have h₁ := exp_neg_le_one_sub_add_sq_div_two (neg_nonneg.2 hu)
    rw [neg_neg, neg_sq, sub_neg_eq_add] at h₁
    have h₂ : 1 / 2 ≤ (exp (l * b) - 1 - l * b) / (l * b) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith [quadratic_le_exp_of_nonneg hv.le]
    nlinarith [sq_nonneg (l * x)]
  · have h := monotoneOn_exp_sub_one_sub_id_div_sq (Set.mem_Ici.2 hu.le) (Set.mem_Ici.2 hv.le)
      (mul_le_mul_of_nonneg_left hx hl.le)
    simp only at h
    have h' : exp (l * x) - 1 - l * x = (exp (l * x) - 1 - l * x) / (l * x) ^ 2 * (l * x) ^ 2 :=
      (div_mul_cancel₀ _ (pow_ne_zero 2 hu.ne')).symm
    nlinarith [sq_nonneg (l * x)]

/-- For `x ≥ -1`, `exp (-x) ≤ 1 - x + x ^ 2`: Bennett's bound `exp u ≤ 1 + u + (e - 2) u ^ 2` for
`u ≤ 1`, with `e - 2 ≤ 1`. -/
theorem exp_neg_le_one_sub_add_sq {x : ℝ} (hx : -1 ≤ x) : exp (-x) ≤ 1 - x + x ^ 2 := by
  have h := exp_mul_le_one_add_mul_add_mul_sq one_pos zero_le_one (show -x ≤ 1 by linarith)
  simp only [one_mul, one_pow, div_one] at h
  have he : exp 1 - 1 - 1 ≤ 1 := by linarith [exp_one_lt_three]
  nlinarith [sq_nonneg x]

/-- **Jensen's inequality for the exponential** with uniform weights: a sum of exponentials is at
least its number of terms times the exponential of the mean of the exponents. -/
theorem card_mul_exp_sum_div_card_le_sum_exp {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    #s * exp ((∑ i ∈ s, x i) / #s) ≤ ∑ i ∈ s, exp (x i) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hcard : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  have h := convexOn_exp.map_sum_le (t := s) (w := fun _ ↦ 1 / (#s : ℝ)) (p := x)
    (fun _ _ ↦ by positivity) (by rw [sum_const, nsmul_eq_mul]; field_simp)
    (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul] at h
  rw [← mul_sum, ← mul_sum, one_div_mul_eq_div, one_div_mul_eq_div] at h
  calc (#s : ℝ) * exp ((∑ i ∈ s, x i) / #s) ≤ #s * ((∑ i ∈ s, exp (x i)) / #s) := by gcongr
    _ = ∑ i ∈ s, exp (x i) := by field_simp

end Real
