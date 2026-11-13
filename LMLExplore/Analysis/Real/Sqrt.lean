/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Square roots of quotients, increments of the square root and sums of inverse square roots

## Main statements

* `Real.mul_sqrt_div_eq_sqrt_mul`: `x * √(y / x) = √(y * x)` for `x ≥ 0`. It converts a confidence
  width `√(c / s)` for an empirical mean of `s` samples into the width `√(c s)` for their sum.
* `Real.div_sqrt_add_sqrt_mul_div_two`: `a / η + η b / 2 = √(2 b a)` for `η = √(2 a / b)` and
  `b ≥ 0`. It is the tuning of the learning rate `η` in regret bounds of the form
  `log k / η + η n / 2`, as for exponential weights, Exp3 and Exp4.
* `Real.sqrt_mul_sqrt_add_one_le`: `√x √(x + 1) ≤ x + 1 / 2` for `x ≥ 0`, the inequality between
  the geometric and arithmetic means of `x` and `x + 1`.
* `Real.one_div_two_mul_sqrt_add_one_le_sqrt_add_one_sub_sqrt`,
  `Real.sqrt_add_one_sub_sqrt_le_one_div_two_mul_sqrt`: the increments of the square root satisfy
  `1 / (2 √(x + 1)) ≤ √(x + 1) - √x ≤ 1 / (2 √x)`. They compare sums `∑_{s < n} 1 / (2 √s)` with
  `√n`, as for the exploration rates of C-tracking.
* `Real.sqrt_add_one_sub_sqrt_le_one_div_sqrt_add_one`: `√(x + 1) - √x ≤ 1 / √(x + 1)` for
  `x ≥ 0`, an upper bound on the increments that also holds at `x = 0`. It bounds the increments
  `√(t + 2) - √(t + 1)` of the Tsallis-INF learning rates by `1 / √(t + 2)`.
* `Real.hasDerivAt_neg_inv_two_mul_sqrt`: `x ↦ -(2 √x)⁻¹`, the derivative of `x ↦ -√x`, has
  derivative `(4 x √x)⁻¹` at `x > 0`. It gives the second derivative of the ½-Tsallis potential.
* `Real.tendsto_one_add_sqrt_div_atTop`: `(1 + √x) / x → 0` as `x → ∞`, so that a tracking error
  of order `1 + √n` after `n` rounds, as for C-tracking, is `o(n)`.
* `Real.le_add_sqrt_of_sq_le`: the root of a quadratic inequality, `x² ≤ b x + c` with `b, c ≥ 0`
  forces `x ≤ b + √c`. It solves for `√τ` inequalities of the form `τ ≤ b √τ + c`, as in the
  self-bounding inequality `Real.le_of_le_sqrt_mul_add`.
* `Real.sum_range_inv_sqrt_add_one_le`: `∑_{j < n} 1 / √(j + 1) ≤ 2 √n`.
* `Real.sum_range_inv_sqrt_max_one_le`: `∑_{j < n} 1 / √(max 1 j) ≤ 2 √n + 1`, the same sum with
  the index clipped at `1`.
* `Real.sum_div_sqrt_max_one_le`: the doubling bound of Jaksch, Ortner and Auer
  [JOA10, Lemma 19]. If `0 ≤ z k ≤ max 1 (Z k)` for every `k < n`, where `Z k = ∑_{i < k} z i`,
  then `∑_{k < n} z k / √(max 1 (Z k)) ≤ (√2 + 1) √(Z n)`. It sums confidence widths over the
  epochs of algorithms that restart an epoch when some count doubles, as UCRL2.

## References

* [JOA10] T. Jaksch, R. Ortner and P. Auer, *Near-optimal regret bounds for reinforcement
  learning*, Journal of Machine Learning Research 11 (2010).
-/

public section

open Filter Topology

namespace Real

/-- For `x ≥ 0`, `x * √(y / x) = √(y * x)`. -/
theorem mul_sqrt_div_eq_sqrt_mul (y : ℝ) {x : ℝ} (hx : 0 ≤ x) : x * √(y / x) = √(y * x) := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  calc x * √(y / x)
  _ = √(x ^ 2) * √(y / x) := by rw [sqrt_sq hx.le]
  _ = √(y * x) := by
    rw [← sqrt_mul (sq_nonneg _)]
    congr 1
    field_simp

/-- For `b ≥ 0` and `η = √(2 a / b)`, `a / η + η b / 2 = √(2 b a)`: this learning rate balances the
two terms of a regret bound `a / η + η b / 2`. -/
theorem div_sqrt_add_sqrt_mul_div_two (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    a / √(2 * a / b) + √(2 * a / b) * b / 2 = √(2 * b * a) := by
  -- for `a ≤ 0`, both sides vanish
  rcases le_or_gt a 0 with ha | ha
  · have h2a : 2 * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos zero_le_two ha
    rw [sqrt_eq_zero'.2 (div_nonpos_of_nonpos_of_nonneg h2a hb),
      sqrt_eq_zero'.2 (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg zero_le_two hb) ha)]
    simp
  rcases hb.eq_or_lt with rfl | hb
  · simp
  have hη : 0 < √(2 * a / b) := sqrt_pos.2 (by positivity)
  have hsq : √(2 * a / b) ^ 2 = 2 * a / b := sq_sqrt (by positivity)
  -- `a / η = η b / 2` and `√(2 b a) = b η`
  have h : a / √(2 * a / b) = √(2 * a / b) * b / 2 := by
    rw [div_eq_iff hη.ne', show √(2 * a / b) * b / 2 * √(2 * a / b) =
      √(2 * a / b) ^ 2 * b / 2 by ring, hsq]
    field_simp
  rw [h, mul_right_comm 2 b a, ← mul_sqrt_div_eq_sqrt_mul _ hb.le]
  ring

/-- The inequality between the geometric and arithmetic means of `x` and `x + 1`:
`√x √(x + 1) ≤ x + 1 / 2` for `x ≥ 0`. -/
theorem sqrt_mul_sqrt_add_one_le {x : ℝ} (hx : 0 ≤ x) : √x * √(x + 1) ≤ x + 1 / 2 := by
  have ha := sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hb := sq_sqrt hx
  nlinarith [sq_nonneg (√(x + 1) - √x)]

/-- A lower bound on the increments of the square root: `1 / (2 √(x + 1)) ≤ √(x + 1) - √x` for
`x ≥ 0`. -/
theorem one_div_two_mul_sqrt_add_one_le_sqrt_add_one_sub_sqrt {x : ℝ} (hx : 0 ≤ x) :
    1 / (2 * √(x + 1)) ≤ √(x + 1) - √x := by
  have ha := sq_sqrt (show 0 ≤ x + 1 by linarith)
  have ha0 : 0 < √(x + 1) := sqrt_pos.2 (by linarith)
  have hab := sqrt_mul_sqrt_add_one_le hx
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- An upper bound on the increments of the square root: `√(x + 1) - √x ≤ 1 / (2 √x)` for
`x > 0`. -/
theorem sqrt_add_one_sub_sqrt_le_one_div_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    √(x + 1) - √x ≤ 1 / (2 * √x) := by
  have hb := sq_sqrt hx.le
  have hb0 : 0 < √x := sqrt_pos.2 hx
  have hab := sqrt_mul_sqrt_add_one_le hx.le
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- An upper bound on the increments of the square root that also holds at `0`:
`√(x + 1) - √x ≤ 1 / √(x + 1)` for `x ≥ 0`. -/
theorem sqrt_add_one_sub_sqrt_le_one_div_sqrt_add_one {x : ℝ} (hx : 0 ≤ x) :
    √(x + 1) - √x ≤ 1 / √(x + 1) := by
  have ha := sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hb := sq_sqrt hx
  have ha0 : 0 < √(x + 1) := sqrt_pos.2 (by linarith)
  have hab : √x ≤ √(x + 1) := sqrt_le_sqrt (by linarith)
  rw [le_div_iff₀ ha0]
  nlinarith [mul_le_mul_of_nonneg_left hab (sqrt_nonneg x)]

/-- `x ↦ -(2 √x)⁻¹` has derivative `(4 x √x)⁻¹` at `x > 0`. -/
theorem hasDerivAt_neg_inv_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y ↦ -(2 * √y)⁻¹) (4 * x * √x)⁻¹ x := by
  have hs : 0 < √x := sqrt_pos.2 hx
  have h1 : HasDerivAt (fun y ↦ 2 * √y) (2 * (1 / (2 * √x))) x :=
    HasDerivAt.const_mul 2 (hasDerivAt_sqrt hx.ne')
  have h := HasDerivAt.neg (HasDerivAt.inv h1 (by positivity))
  convert h using 1
  rw [mul_pow, sq_sqrt hx.le]
  field_simp
  ring

/-- `(1 + √x) / x → 0` as `x → ∞`. -/
theorem tendsto_one_add_sqrt_div_atTop : Tendsto (fun x : ℝ ↦ (1 + √x) / x) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.add (tendsto_inv_atTop_zero.comp tendsto_sqrt_atTop)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards with x
  rw [add_div, sqrt_div_self', one_div, Function.comp_apply, one_div]

/-- The root of a quadratic inequality: `x² ≤ b x + c` with `b, c ≥ 0` forces `x ≤ b + √c`.

Adapted from the formalization in the paper project RemyDegenne/Essakine2026Tight (same author),
file `ForLMLExplore/Analysis/Real/Sqrt.lean`. -/
theorem le_add_sqrt_of_sq_le {x b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (h : x ^ 2 ≤ b * x + c) :
    x ≤ b + √c := by
  by_contra! hlt
  have hs := sq_sqrt hc
  have hs0 := sqrt_nonneg c
  -- `(x - √c) (x - b - √c) > 0` and `√c (2 x - b - 2 √c) ≥ 0` add up to `x² - b x > c`
  nlinarith [mul_pos (show 0 < x - √c by linarith) (show 0 < x - b - √c by linarith),
    mul_nonneg hs0 (show 0 ≤ 2 * x - b - 2 * √c by linarith)]

/-- `∑_{j < n} 1 / √(j + 1) ≤ 2 √n`. -/
theorem sum_range_inv_sqrt_add_one_le (n : ℕ) :
    ∑ j ∈ Finset.range n, (√((j : ℝ) + 1))⁻¹ ≤ 2 * √n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := one_div_two_mul_sqrt_add_one_le_sqrt_add_one_sub_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have h2 : (√((n : ℝ) + 1))⁻¹ = 2 * (1 / (2 * √((n : ℝ) + 1))) := by ring
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith

/-- `∑_{j < n} 1 / √(max 1 j) ≤ 2 √n + 1`, the sum of inverse square roots with the index clipped
at `1`. -/
theorem sum_range_inv_sqrt_max_one_le (n : ℕ) :
    ∑ j ∈ Finset.range n, (√(max 1 (j : ℝ)))⁻¹ ≤ 2 * √n + 1 := by
  rcases n with _ | n
  · simp
  rw [LMLExplore.sum_range_succ_comp_max_one (fun x : ℝ ↦ (√x)⁻¹), sqrt_one, inv_one]
  have := sum_range_inv_sqrt_add_one_le n
  have : √(n : ℝ) ≤ √((n + 1 : ℕ) : ℝ) := sqrt_le_sqrt (by simp)
  linarith

/-- One step of the doubling bound: for `0 ≤ Z`, `0 ≤ z` and `z ≤ max 1 Z`,
`z / √(max 1 Z) ≤ (√2 + 1) (√(Z + z) - √Z)`. -/
private theorem div_sqrt_max_one_le_mul_sqrt_add_sub_sqrt {Z z : ℝ} (hZ : 0 ≤ Z) (hz : 0 ≤ z)
    (hzZ : z ≤ max 1 Z) : z / √(max 1 Z) ≤ (√2 + 1) * (√(Z + z) - √Z) := by
  have hM : 0 < √(max 1 Z) := sqrt_pos.2 (lt_max_of_lt_left one_pos)
  have hd : 0 ≤ √(Z + z) - √Z := sub_nonneg.2 (sqrt_le_sqrt (by linarith))
  -- `√(Z + z) + √Z ≤ √(2 M) + √M` for `M = max 1 Z`, since `Z ≤ M` and `z ≤ M`
  have h1 : √(Z + z) ≤ √2 * √(max 1 Z) := by
    rw [← sqrt_mul zero_le_two]
    exact sqrt_le_sqrt (by linarith [le_max_right 1 Z])
  have h2 : √Z ≤ √(max 1 Z) := sqrt_le_sqrt (le_max_right _ _)
  have ha := sq_sqrt (show 0 ≤ Z + z by linarith)
  have hb := sq_sqrt hZ
  rw [div_le_iff₀ hM]
  calc z = (√(Z + z) - √Z) * (√(Z + z) + √Z) := by nlinarith
    _ ≤ (√(Z + z) - √Z) * ((√2 + 1) * √(max 1 Z)) := by gcongr; linarith
    _ = (√2 + 1) * (√(Z + z) - √Z) * √(max 1 Z) := by ring

/-- **The doubling bound** [JOA10, Lemma 19]: if `0 ≤ z k ≤ max 1 (Z k)` for every `k < n`, where
`Z k = ∑_{i < k} z i`, then `∑_{k < n} z k / √(max 1 (Z k)) ≤ (√2 + 1) √(Z n)`. -/
theorem sum_div_sqrt_max_one_le {z : ℕ → ℝ} {n : ℕ} (hz : ∀ k < n, 0 ≤ z k)
    (hzZ : ∀ k < n, z k ≤ max 1 (∑ i ∈ Finset.range k, z i)) :
    ∑ k ∈ Finset.range n, z k / √(max 1 (∑ i ∈ Finset.range k, z i)) ≤
      (√2 + 1) * √(∑ k ∈ Finset.range n, z k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hZ : 0 ≤ ∑ i ∈ Finset.range n, z i :=
      Finset.sum_nonneg fun i hi ↦ hz i (by simp at hi; omega)
    have hstep := div_sqrt_max_one_le_mul_sqrt_add_sub_sqrt hZ (hz n n.lt_succ_self)
      (hzZ n n.lt_succ_self)
    have ih' := ih (fun k hk ↦ hz k (by omega)) (fun k hk ↦ hzZ k (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

end Real
