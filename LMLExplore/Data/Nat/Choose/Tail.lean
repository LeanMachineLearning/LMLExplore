/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
import TauCeti.Analysis.SpecialFunctions.Log.Factorial

/-!
# Lower bounds on the upper tail of the binomial coefficients

For `X` binomial with parameters `n` and `1 / 2`, `P(X ≥ k) = (∑ i ∈ Icc k n, n.choose i) / 2 ^ n`.
This file bounds this upper tail below, for `n / 2 ≤ k ≤ n`, by its exponential rate
`exp (-n d(k / n, 1 / 2))` times a polynomial factor, where `d` is the binary relative entropy
`klBerReal` [Ora, Lemmas A.15 and A.17]:
`P(X ≥ k) ≥ (1 / 3) (√n / (2 k - n + √n)) exp (-n d(k / n, 1 / 2))`.
For `n` even and `k = n / 2 + q`, the factor is `1 / (3 (2 q / √n + 1))`. Lower bounds on the
regret of online learning and on the wealth of coin-betting algorithms use it to show that a sign
sequence with a large sum `∑ t, ε t ≥ 2 k - n` is not too rare [Ora, Theorem 5.5].

* `Nat.mul_choose_le_mul_sum_Icc_choose`: the sum of the binomial coefficients `n.choose i`,
  `k ≤ i ≤ n`, is at least `n.choose k * k / D` for an explicit `D` [Ora, Lemma A.15], proved by
  backward induction on `k`. The quantity `D` is the positive root of
  `x ^ 2 + (n + 2 - 2 k) x - 2 k = 0`, which makes the induction step an equality.
* `Nat.mul_choose_le_add_sqrt_mul_sum_Icc_choose`: its simpler form with `D ≤ 2 k - n + √n` for
  `n ≤ 2 k` [Ora, Remark A.16].
* `Nat.two_pow_mul_exp_neg_mul_klBerReal_mul_sqrt_div_le_choose`: Stirling's lower bound
  `n.choose k ≥ 2 ^ n exp (-n d(k / n, 1 / 2)) √(2 π n / (k (n - k))) / e ^ 2`, positive for
  `0 < k < n`.
* `Nat.exp_neg_mul_klBerReal_le_sum_Icc_choose_div_two_pow`: the lower bound on the tail
  [Ora, Lemma A.17].

## Implementation notes

[Ora] bounds the factorials through Robbins' form of Stirling's formula. The upper bound
`m! ≤ e √m (m / e) ^ m` used here, from the monotonicity of Stirling's sequence (Tau Ceti's
`Real.log_factorial_le`), is slightly better than Robbins' `e ^ (1 / 12) √(2 π m) (m / e) ^ m`, and
the constant `1 / 3` follows from `e ^ 4 ≤ 18 π`. The statement holds for all `n / 2 ≤ k ≤ n`,
which for `n` even contains the range `q ≤ n / 2` of [Ora].

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset Real InformationTheory
open scoped Nat

namespace Nat

variable {n k : ℕ}

section SumChoose

/-- The quantity `D(n, k)` of the bound `k * n.choose k ≤ D(n, k) * ∑ i ∈ Icc k n, n.choose i`:
the positive root of `x ^ 2 + (n + 2 - 2 k) x - 2 k = 0`. -/
private noncomputable def tailDenom (n k : ℝ) : ℝ :=
  (2 * k - n - 2 + √(4 * k ^ 2 - 4 * k * n + (n + 2) ^ 2)) / 2

private lemma sq_sqrt_tailDenom {n : ℝ} (hn : 0 ≤ n) (k : ℝ) :
    √(4 * k ^ 2 - 4 * k * n + (n + 2) ^ 2) ^ 2 = (2 * k - n) ^ 2 + 4 * n + 4 := by
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg (2 * k - n)])]
  ring

/-- `D(n, k)` solves `x ^ 2 + (n + 2 - 2 k) x - 2 k = 0`. -/
private lemma tailDenom_quadratic {n : ℝ} (hn : 0 ≤ n) (k : ℝ) :
    tailDenom n k ^ 2 + (n + 2 - 2 * k) * tailDenom n k - 2 * k = 0 := by
  have h := sq_sqrt_tailDenom hn k
  unfold tailDenom
  nlinarith

private lemma tailDenom_nonneg {n k : ℝ} (hn : 0 ≤ n) (hk : 0 ≤ k) : 0 ≤ tailDenom n k := by
  have h := sq_sqrt_tailDenom hn k
  have hs := Real.sqrt_nonneg (4 * k ^ 2 - 4 * k * n + (n + 2) ^ 2)
  unfold tailDenom
  -- the square root is at least `|2 k - n - 2|`, as its square exceeds `(2 k - n - 2) ^ 2` by `8 k`
  nlinarith [Real.abs_le_sqrt (x := 2 * k - n - 2) (y := 4 * k ^ 2 - 4 * k * n + (n + 2) ^ 2)
    (by nlinarith), le_abs_self (2 * k - n - 2), neg_abs_le (2 * k - n - 2)]

/-- `D(n, k + 1) ≤ D(n, k) + 2`. -/
private lemma tailDenom_add_one_le {n : ℝ} (hn : 0 ≤ n) (k : ℝ) :
    tailDenom n (k + 1) ≤ tailDenom n k + 2 := by
  have h₀ := sq_sqrt_tailDenom hn k
  have h₁ := sq_sqrt_tailDenom hn (k + 1)
  set s₀ := √(4 * k ^ 2 - 4 * k * n + (n + 2) ^ 2)
  set s₁ := √(4 * (k + 1) ^ 2 - 4 * (k + 1) * n + (n + 2) ^ 2)
  have hs₀ : 0 ≤ s₀ := Real.sqrt_nonneg _
  have hs₁ : 0 ≤ s₁ := Real.sqrt_nonneg _
  -- `2 k - n ≤ s₀`, as `s₀ ^ 2 ≥ (2 k - n) ^ 2`
  have hle : 2 * k - n ≤ s₀ := by
    have h := Real.abs_le_sqrt (x := 2 * k - n) (y := 4 * k ^ 2 - 4 * k * n + (n + 2) ^ 2)
      (by nlinarith)
    exact (le_abs_self _).trans h
  have : s₁ ≤ s₀ + 2 := by nlinarith
  unfold tailDenom
  linarith

private lemma tailDenom_self (n : ℝ) (hn : 0 ≤ n) : tailDenom n n = n := by
  have : 4 * n ^ 2 - 4 * n * n + (n + 2) ^ 2 = (n + 2) ^ 2 := by ring
  rw [tailDenom, this, Real.sqrt_sq (by linarith)]
  ring

/-- The sum `∑ i ∈ Icc k n, n.choose i`, written with real coefficients, splits off its first
term. -/
private lemma sum_Icc_choose_eq_add (hk : k < n) :
    ∑ i ∈ Icc k n, (n.choose i : ℝ) = n.choose k + ∑ i ∈ Icc (k + 1) n, (n.choose i : ℝ) := by
  rw [← insert_Icc_add_one_left_eq_Icc hk.le, sum_insert (by simp)]

private lemma mul_choose_le_tailDenom_mul (hk : k ≤ n) :
    (k : ℝ) * n.choose k ≤ tailDenom n k * ∑ i ∈ Icc k n, (n.choose i : ℝ) := by
  induction hk using Nat.decreasingInduction with
  | self => simp [tailDenom_self _ (Nat.cast_nonneg n)]
  | of_succ k hk ih =>
    set C : ℝ := (n.choose k : ℝ)
    set S : ℝ := ∑ i ∈ Icc (k + 1) n, (n.choose i : ℝ)
    set D := tailDenom n k
    have hC : 0 ≤ C := Nat.cast_nonneg _
    have hS : 0 ≤ S := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
    have hD : 0 ≤ D := tailDenom_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg k)
    -- `(k + 1) * n.choose (k + 1) = (n - k) * n.choose k`
    have hchoose : ((k + 1 : ℕ) : ℝ) * n.choose (k + 1) = (n - k) * C := by
      have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_succ_right_eq n k)
      push_cast [Nat.cast_sub hk.le] at h
      simp only [C]
      push_cast
      linarith
    -- the induction hypothesis, with `D(n, k + 1) ≤ D(n, k) + 2`
    have ih' : (n - k) * C ≤ (D + 2) * S := by
      rw [← hchoose]
      refine ih.trans (mul_le_mul_of_nonneg_right ?_ hS)
      push_cast
      exact tailDenom_add_one_le (Nat.cast_nonneg n) _
    have hnk : (k : ℝ) < n := by exact_mod_cast hk
    have hquad := tailDenom_quadratic (Nat.cast_nonneg (α := ℝ) n) k
    rw [sum_Icc_choose_eq_add hk]
    -- multiplied by `D + 2`, the goal is `ih'` times `D` plus `C` times the quadratic equation
    refine le_of_mul_le_mul_left ?_ (by linarith : (0 : ℝ) < D + 2)
    nlinarith [mul_le_mul_of_nonneg_left ih' hD, congrArg (C * ·) hquad]

/-- **A lower bound on the tail of the binomial coefficients** [Ora, Lemma A.15]:
`∑ i ∈ Icc k n, n.choose i ≥ n.choose k * k / D`, where
`D = (2 k - n - 2 + √(4 k ^ 2 - 4 k n + (n + 2) ^ 2)) / 2` is the positive root of
`x ^ 2 + (n + 2 - 2 k) x - 2 k = 0`. [Ora] writes `D = 2 k + φ(k, n)` and states the bound for
`n / 2 ≤ k ≤ n`; for `k > n` both sides vanish. -/
theorem mul_choose_le_mul_sum_Icc_choose (n k : ℕ) :
    (k : ℝ) * n.choose k ≤ (2 * k - n - 2 + √(4 * k ^ 2 - 4 * k * n + (n + 2) ^ 2)) / 2 *
      ∑ i ∈ Icc k n, (n.choose i : ℝ) := by
  rcases le_or_gt k n with hk | hk
  · exact mul_choose_le_tailDenom_mul hk
  · simp [Nat.choose_eq_zero_of_lt hk, Icc_eq_empty_of_lt hk]

/-- **A lower bound on the tail of the binomial coefficients**, simplified [Ora, Remark A.16]: for
`n / 2 ≤ k`, `∑ i ∈ Icc k n, n.choose i ≥ n.choose k * k / (2 k - n + √n)`. -/
theorem mul_choose_le_add_sqrt_mul_sum_Icc_choose (hnk : n ≤ 2 * k) :
    (k : ℝ) * n.choose k ≤ (2 * k - n + √n) * ∑ i ∈ Icc k n, (n.choose i : ℝ) := by
  refine (mul_choose_le_mul_sum_Icc_choose n k).trans
    (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _))
  have hb : (0 : ℝ) ≤ 2 * k - n := by
    have : (n : ℝ) ≤ 2 * k := by exact_mod_cast hnk
    linarith
  have hr := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hr0 := Real.sqrt_nonneg (n : ℝ)
  -- the square root in `D` is at most `(2 k - n) + 2 √n + 2`
  have hs : √(4 * (k : ℝ) ^ 2 - 4 * k * n + (n + 2) ^ 2) ≤ 2 * k - n + 2 * √n + 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg hb hr0]
  linarith

end SumChoose

section Stirling

/-- **Stirling's lower bound on binomial coefficients**:
`n.choose k ≥ 2 ^ n exp (-n d(k / n, 1 / 2)) √(2 π n / (k (n - k))) / e ^ 2`, where `d` is the
binary relative entropy. The bound is positive only for `0 < k < n`. -/
theorem two_pow_mul_exp_neg_mul_klBerReal_mul_sqrt_div_le_choose (n k : ℕ) :
    2 ^ n * exp (-(n * klBerReal (k / n) (1 / 2))) * √(2 * π * n / (k * (n - k))) / exp 2 ≤
      n.choose k := by
  -- outside `0 < k < n`, the square root vanishes
  by_cases hkn : 0 < k ∧ k < n
  swap
  · have : 2 * π * n / (k * (n - k)) ≤ 0 := by
      refine div_nonpos_of_nonneg_of_nonpos (by positivity) ?_
      rcases Nat.eq_zero_or_pos k with rfl | hk₀
      · simp
      · have : (n : ℝ) ≤ k := by exact_mod_cast not_lt.1 fun h ↦ hkn ⟨hk₀, h⟩
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    rw [Real.sqrt_eq_zero'.2 this, mul_zero, zero_div]
    exact Nat.cast_nonneg _
  obtain ⟨hk₀, hk⟩ := hkn
  have hn : 0 < n := hk₀.trans hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk₀
  have hnkR : (0 : ℝ) < n - k := by
    have : (k : ℝ) < n := by exact_mod_cast hk
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk.le
  -- `log n! = Real.log (n.choose k) + log k! + Real.log (n - k)!`
  have hfact : Real.log (n.choose k : ℝ) + Real.log (k ! : ℝ) + Real.log ((n - k : ℕ)! : ℝ) =
      Real.log (n ! : ℝ) := by
    rw [← Real.log_mul hC.ne' (by positivity), ← Real.log_mul (by positivity) (by positivity)]
    exact_mod_cast congrArg (fun m : ℕ ↦ Real.log (m : ℝ))
      (Nat.choose_mul_factorial_mul_factorial hk.le)
  have hnk_cast : ((n - k : ℕ) : ℝ) = n - k := Nat.cast_sub hk.le
  have hup₁ := Real.log_factorial_le k
  have hup₂ := Real.log_factorial_le (n - k)
  have hlow := Stirling.le_log_factorial_stirling hn.ne'
  rw [hnk_cast] at hup₂
  have hx : Real.log (2 * π * n / (k * (n - k))) =
      Real.log (2 * π) + Real.log n - Real.log k - Real.log (n - k) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hnR.ne',
      Real.log_mul hkR.ne' hnkR.ne']
    ring
  have hkl : (n : ℝ) * klBerReal (k / n) (1 / 2) =
      n * Real.log 2 + k * Real.log k + (n - k) * Real.log (n - k) - n * Real.log n := by
    rw [LMLExplore.mul_klBerReal_div_one_div_two, Real.log_div (by positivity) hnR.ne',
      Real.log_div (by positivity) hnR.ne', Real.log_mul two_ne_zero hkR.ne',
      Real.log_mul two_ne_zero hnkR.ne']
    ring
  -- the left-hand side is `exp (n log 2 - n d(k / n, 1 / 2) + log (2 π n / (k (n - k))) / 2 - 2)`
  have hlhs : 2 ^ n * exp (-(n * klBerReal (k / n) (1 / 2))) * √(2 * π * n / (k * (n - k))) /
      exp 2 = exp (n * Real.log 2 + -(n * klBerReal (k / n) (1 / 2)) +
        Real.log (2 * π * n / (k * (n - k))) / 2 - 2) := by
    rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_natCast_mul, Real.exp_log two_pos,
      ← Real.log_sqrt (by positivity), Real.exp_log (Real.sqrt_pos.2 (by positivity))]
  rw [hlhs, ← Real.exp_log hC, Real.exp_le_exp, hx, hkl]
  linarith

end Stirling

/-- `e ^ 2 ≤ 3 √(2 π)`, that is `e ^ 4 ≤ 18 π`: the constant `1 / 3` of [Ora, Lemma A.17]. -/
private lemma exp_two_le_three_mul_sqrt_two_pi : exp 2 ≤ 3 * √(2 * π) := by
  have h4 : exp 2 ^ 2 ≤ 18 * π := by
    have : exp 2 ^ 2 = exp 1 ^ 4 := by
      rw [← Real.exp_natCast_mul, ← Real.exp_natCast_mul]
      norm_num
    rw [this]
    have := exp_one_lt_d9
    have := pi_gt_d2
    have : exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
    nlinarith
  have : exp 2 / 3 ≤ √(2 * π) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **A lower bound on the upper tail of the binomial law of parameter `1 / 2`**
[Ora, Lemma A.17]: for `n / 2 ≤ k ≤ n`,
`(∑ i ∈ Icc k n, n.choose i) / 2 ^ n ≥ (1 / 3) (√n / (2 k - n + √n)) exp (-n d(k / n, 1 / 2))`,
where `d` is the binary relative entropy. The left-hand side is `P(X ≥ k)` for `X` binomial with
parameters `n` and `1 / 2`. For `n` even and `k = n / 2 + q`, the polynomial factor is
`1 / (3 (2 q / √n + 1))`, as in [Ora]. -/
theorem exp_neg_mul_klBerReal_le_sum_Icc_choose_div_two_pow (hnk : n ≤ 2 * k) (hk : k ≤ n) :
    1 / 3 * (√n / (2 * k - n + √n)) * exp (-(n * klBerReal (k / n) (1 / 2))) ≤
      (∑ i ∈ Icc k n, (n.choose i : ℝ)) / 2 ^ n := by
  have hb : (0 : ℝ) ≤ 2 * k - n := by
    have : (n : ℝ) ≤ 2 * k := by exact_mod_cast hnk
    linarith
  rcases hk.eq_or_lt with rfl | hk'
  · -- `k = n`: the tail is `1 / 2 ^ n` and `d(1, 1 / 2) = log 2`
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have hkR : (k : ℝ) ≠ 0 := by positivity
    have hexp : exp (-(k * klBerReal ((k : ℝ) / k) (1 / 2))) = 1 / 2 ^ k := by
      have hkl : klBerReal 1 (1 / 2) = Real.log 2 := by simp [klBerReal_apply]
      rw [div_self hkR, hkl, exp_neg, Real.exp_natCast_mul, Real.exp_log two_pos, one_div]
    rw [hexp, Icc_self, sum_singleton, Nat.choose_self, Nat.cast_one]
    have h3 : 1 / 3 * (√k / (2 * k - k + √k)) ≤ 1 := by
      have : √(k : ℝ) / (2 * k - k + √k) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      linarith
    calc 1 / 3 * (√k / (2 * k - k + √k)) * (1 / 2 ^ k) ≤ 1 * (1 / 2 ^ k) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 1 / 2 ^ k := one_mul _
  -- `k < n`, so `0 < n - k ≤ k`
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hk0.trans hk'
  have hnkR : (0 : ℝ) < n - k := by
    have : (k : ℝ) < n := by exact_mod_cast hk'
    linarith
  have hnkk : (n : ℝ) - k ≤ k := by linarith
  set E := exp (-(n * klBerReal (k / n) (1 / 2)))
  set S := ∑ i ∈ Icc k n, (n.choose i : ℝ)
  set r := √(2 * π * n / (k * (n - k)))
  have hB : 0 < 2 * k - n + √(n : ℝ) := by positivity
  have h₁ := mul_choose_le_add_sqrt_mul_sum_Icc_choose hnk
  have h₂ := two_pow_mul_exp_neg_mul_klBerReal_mul_sqrt_div_le_choose n k
  -- `√n / 3 ≤ k √(2 π n / (k (n - k))) / e ^ 2`, from `k / (n - k) ≥ 1` and `e ^ 4 ≤ 18 π`
  have h₃ : √(n : ℝ) / 3 ≤ k * r / exp 2 := by
    have hkr : √(2 * π * n) ≤ k * r := by
      rw [show (k : ℝ) * r = √(k ^ 2 * (2 * π * n / (k * (n - k)))) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hkR.le]]
      refine Real.sqrt_le_sqrt ?_
      rw [show (k : ℝ) ^ 2 * (2 * π * n / (k * (n - k))) = 2 * π * n * (k / (n - k)) by
        field_simp]
      exact le_mul_of_one_le_right (by positivity) ((one_le_div hnkR).2 hnkk)
    rw [le_div_iff₀ (exp_pos 2)]
    calc √(n : ℝ) / 3 * exp 2 ≤ √n / 3 * (3 * √(2 * π)) := by
          gcongr
          exact exp_two_le_three_mul_sqrt_two_pi
      _ = √(2 * π * n) := by rw [Real.sqrt_mul (by positivity) (n : ℝ)]; ring
      _ ≤ k * r := hkr
  -- combine: `√n / 3 * (2 ^ n * E) ≤ k * n.choose k ≤ (2 k - n + √n) * S`
  have key : √(n : ℝ) / 3 * (2 ^ n * E) ≤ (2 * k - n + √n) * S :=
    calc √(n : ℝ) / 3 * (2 ^ n * E) ≤ k * r / exp 2 * (2 ^ n * E) := by gcongr
      _ = k * (2 ^ n * E * r / exp 2) := by ring
      _ ≤ k * n.choose k := by gcongr
      _ ≤ (2 * k - n + √n) * S := h₁
  rw [le_div_iff₀ (by positivity),
    show 1 / 3 * (√(n : ℝ) / (2 * k - n + √n)) * E * 2 ^ n =
      √(n : ℝ) / 3 * (2 ^ n * E) / (2 * k - n + √n) by ring, div_le_iff₀ hB]
  linarith

end Nat
