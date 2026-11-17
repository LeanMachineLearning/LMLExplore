/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.SpecialFunctions.Lambert
public import LMLExplore.OnlineLearning.CoinBetting
import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
import LMLExplore.OnlineLearning.Learner.Operations
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The lower bound of unconstrained online linear optimization

On `ℝ` with linear losses `x ↦ g t * x`, `|g t| ≤ L`, a learner whose regret against `0` is at most
a constant `ε > 0` is a bettor with initial wealth `ε` that never goes into debt. Such a bettor
cannot get rich on all biased sequences of coins (`OnlineLearner.exists_wealth_run_le_of_even`),
so its regret against some comparator of norm `U` is large. This file proves the resulting lower
bound [Ora, Theorem 5.8]: some losses force a regret of at least
`U L √n (√(2 W) - 1) - 2 U L + ε` against `U` or `-U`, where `W` is the Lambert function at
`√(e n) U L / (8 ε)` (`OnlineLearner.exists_mul_sqrt_two_mul_lambertW_le_regret_run`), or at
`√n U L / (5 ε)` in the form of [Ora]
(`OnlineLearner.exists_mul_sqrt_two_mul_lambertW_div_five_le_regret_run`).

For regret bounds `ε n` against `0` bounded away from `0` and `∞`, the hypotheses on `W` hold for
all large `n` (`eventually_one_le_lambertW_and_le`), and the lower bound is asymptotic to
`U L √(n log n)` (`tendsto_mul_sqrt_two_mul_lambertW_div_sqrt_mul_log`). A learner that has a
constant regret against `0` therefore has a regret of order `U L √(n log n)` against comparators
of norm `U`, a factor `√(log n)` above the minimax rate `U L √n` of a known comparator norm.

The proof chooses the bias `2 q` of the coins, `q = ⌊√n √(2 W - 1) / 2⌋`, to maximize the bound,
and bounds the binary relative entropy near `1 / 2` by `LMLExplore.klBerReal_one_div_two_add_le`.

## Main statements

* `LMLExplore.OnlineLearning.OnlineLearner.exists_mul_sqrt_two_mul_lambertW_le_regret_run`,
  `LMLExplore.OnlineLearning.OnlineLearner.exists_mul_sqrt_two_mul_lambertW_div_five_le_regret_run`:
  the lower bound at a fixed even horizon.
* `LMLExplore.OnlineLearning.eventually_one_le_lambertW_and_le`: its hypotheses hold eventually.
* `LMLExplore.OnlineLearning.tendsto_mul_sqrt_two_mul_lambertW_div_sqrt_mul_log`: the lower bound
  is asymptotic to `U L √(n log n)`.
* `OnlineLearner.HasRegretBound.eventually_exists_mul_sqrt_two_mul_lambertW_le_regret_run`: the
  lower bound for a learner with a regret guarantee, at all large even horizons.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset Real InformationTheory Filter Topology

namespace LMLExplore.OnlineLearning

/-- For `A ≥ 1`, `√(2 A) - 1 ≤ √(2 A - 1) * (1 - 1 / (2 A))`. -/
private lemma sqrt_two_mul_sub_one_le {A : ℝ} (hA : 1 ≤ A) :
    √(2 * A) - 1 ≤ √(2 * A - 1) * (1 - 1 / (2 * A)) := by
  set r := √(2 * A - 1)
  have hr : 1 ≤ r := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hr2 : r ^ 2 = 2 * A - 1 := Real.sq_sqrt (by linarith)
  have h2A : 2 * A = r ^ 2 + 1 := by linarith
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [h2A, sub_le_iff_le_add, show r * (1 - 1 / (r ^ 2 + 1)) = r ^ 3 / (r ^ 2 + 1) by
    field_simp; ring]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [div_add_one (by positivity), div_pow, le_div_iff₀ (by positivity)]
  have hr1 : 0 ≤ r - 1 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hr0.le hr0.le) (mul_nonneg hr1 (sq_nonneg r))]

/-- For `N ≥ 4`, `1 ≤ y` with `y ^ 2 ≤ √N` and `0 ≤ q ≤ √N y / 2`, the bound
`3 ε / 2 * (2 q / √N + 1) * exp (N d(1 / 2 + q / N, 1 / 2))` on the wealth of a bettor on the
sequences of bias `2 q` is at most `4 ε y exp (y ^ 2 / 2)`. -/
private lemma wealth_bound_le {N ε y q : ℝ} (hN : 4 ≤ N) (hε : 0 ≤ ε) (hy1 : 1 ≤ y)
    (hyN : y ^ 2 ≤ √N) (hq0 : 0 ≤ q) (hq : q ≤ √N * y / 2) :
    3 * ε / 2 * (2 * q / √N + 1) * exp (N * klBerReal (1 / 2 + q / N) (1 / 2)) ≤
      4 * ε * y * exp (y ^ 2 / 2) := by
  have hN0 : 0 < N := by linarith
  have hsqrt : 2 ≤ √N := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]]
    exact Real.sqrt_le_sqrt hN
  have hsq : √N ^ 2 = N := Real.sq_sqrt hN0.le
  -- `q ^ 2 ≤ N y ^ 2 / 4 ≤ N √N / 4`
  have hq2 : q ^ 2 ≤ N * y ^ 2 / 4 := by
    calc q ^ 2 ≤ (√N * y / 2) ^ 2 := pow_le_pow_left₀ hq0 hq 2
      _ = N * y ^ 2 / 4 := by rw [div_pow, mul_pow, hsq]; ring
  have h2N : 2 * √N ≤ N := by nlinarith
  have h8 : 8 * (q / N) ^ 2 ≤ 1 := by
    rw [div_pow, ← mul_div_assoc, div_le_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hyN hN0.le]
  have h4 : q ^ 4 ≤ N ^ 3 / 16 := by
    calc q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ ≤ (N * √N / 4) ^ 2 := pow_le_pow_left₀ (sq_nonneg q) (by nlinarith) 2
      _ = N ^ 3 / 16 := by rw [div_pow, mul_pow, hsq]; ring
  -- `N d(1 / 2 + q / N, 1 / 2) ≤ 2 q ^ 2 / N + 8 q ^ 4 / (3 N ^ 3) ≤ y ^ 2 / 2 + 1 / 6`
  have hkl : N * klBerReal (1 / 2 + q / N) (1 / 2) ≤ y ^ 2 / 2 + 1 / 6 := by
    calc N * klBerReal (1 / 2 + q / N) (1 / 2) ≤ N * (2 * (q / N) ^ 2 + 8 / 3 * (q / N) ^ 4) :=
          mul_le_mul_of_nonneg_left (LMLExplore.klBerReal_one_div_two_add_le h8) hN0.le
      _ = 2 * q ^ 2 / N + 8 / 3 * (q ^ 4 / N ^ 3) := by field_simp
      _ ≤ 2 * (N * y ^ 2 / 4) / N + 8 / 3 * (N ^ 3 / 16 / N ^ 3) := by gcongr
      _ = y ^ 2 / 2 + 1 / 6 := by field_simp; ring
  -- `exp (1 / 6) ≤ 4 / 3` and `2 q / √N + 1 ≤ 2 y`
  have hexp : exp (1 / 6) ≤ 4 / 3 := by
    have := exp_bound_div_one_sub_of_interval' (x := 1 / 6) (by norm_num) (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 6) = 6 / 5 by norm_num]
  have hfac : 2 * q / √N + 1 ≤ 2 * y := by
    rw [div_add_one (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  calc 3 * ε / 2 * (2 * q / √N + 1) * exp (N * klBerReal (1 / 2 + q / N) (1 / 2))
      ≤ 3 * ε / 2 * (2 * y) * (exp (1 / 6) * exp (y ^ 2 / 2)) := by
        rw [← exp_add, add_comm (1 / 6)]
        gcongr
    _ ≤ 3 * ε / 2 * (2 * y) * (4 / 3 * exp (y ^ 2 / 2)) := by gcongr
    _ = 4 * ε * y * exp (y ^ 2 / 2) := by ring

/-- The last step of the lower bound: for `W ≥ 1`, `y = √(2 W - 1)` and `W E = √N U L / (8 ε)`,
a wealth `w ≤ 4 ε y E` on a sequence with `|∑ t, c t| ≥ S ≥ √N y - 2` leaves a regret
`ε - w + L U S ≥ U L √N (√(2 W) - 1) - 2 U L + ε`. -/
private lemma mul_sqrt_two_mul_sub_one_le {N W E ε U L S w : ℝ} (hW₁ : 1 ≤ W)
    (hε : 0 < ε) (hU : 0 < U) (hL : 0 < L) (hWE : W * E = √N * U * L / (8 * ε))
    (hS : √N * √(2 * W - 1) - 2 ≤ S) (hw : w ≤ 4 * ε * √(2 * W - 1) * E) :
    U * L * √N * (√(2 * W) - 1) - 2 * U * L + ε ≤ ε - w + L * U * S := by
  have hW0 : W ≠ 0 := (zero_lt_one.trans_le hW₁).ne'
  have hεE : 4 * ε * √(2 * W - 1) * E = U * L * √N * √(2 * W - 1) * (1 / (2 * W)) := by
    rw [show E = √N * U * L / (8 * ε) / W by rw [← hWE]; field_simp]
    field_simp
    ring
  have hfin := sqrt_two_mul_sub_one_le hW₁
  have hUL : 0 ≤ U * L * √N := by positivity
  calc U * L * √N * (√(2 * W) - 1) - 2 * U * L + ε
      ≤ U * L * √N * (√(2 * W - 1) * (1 - 1 / (2 * W))) - 2 * U * L + ε := by gcongr
    _ = ε - U * L * √N * √(2 * W - 1) * (1 / (2 * W)) + L * U * (√N * √(2 * W - 1) - 2) := by
        ring
    _ ≤ ε - w + L * U * S := by
        rw [← hεE]
        gcongr

/-- The bias of the lower bound: for `n` even and `1 ≤ W ≤ √n / 2`, the integer part `q` of
`√n √(2 W - 1) / 2` satisfies `0 < q ≤ n / 2`. -/
private lemma exists_bias {n : ℕ} (hn : Even n) {W : ℝ} (hW₁ : 1 ≤ W) (hW₂ : W ≤ √n / 2) :
    ∃ q : ℕ, 0 < q ∧ q ≤ n / 2 ∧ (q : ℝ) ≤ √n * √(2 * W - 1) / 2 ∧
      √n * √(2 * W - 1) / 2 - 1 < q := by
  set y := √(2 * W - 1)
  have hsqN : √(n : ℝ) * √n = n := Real.mul_self_sqrt n.cast_nonneg
  have hy2 : y ^ 2 = 2 * W - 1 := Real.sq_sqrt (by linarith)
  have hy1 : 1 ≤ y := by nlinarith [Real.sqrt_nonneg (2 * W - 1)]
  have hyN : y ≤ √n := by nlinarith
  have hQ1 : 1 ≤ √n * y / 2 := by nlinarith
  have hQn : √n * y / 2 ≤ n / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hyN (Real.sqrt_nonneg (n : ℝ))]
  refine ⟨⌊√n * y / 2⌋₊, Nat.one_le_floor_iff _ |>.2 hQ1, ?_, Nat.floor_le (by positivity),
    Nat.sub_one_lt_floor _⟩
  obtain ⟨m, rfl⟩ := hn
  have : (⌊√(m + m : ℕ) * y / 2⌋₊ : ℝ) ≤ m := by
    refine (Nat.floor_le (by positivity)).trans (hQn.trans_eq ?_)
    push_cast
    ring
  rw [show (m + m) / 2 = m by omega]
  exact_mod_cast this

namespace OnlineLearner

variable {C : Type*}

/-- The learner `A` on `ℝ` against the slopes `-L * g t`, seen as a bettor on the coins `g t`: it
bets `L` times the plays of `A`. -/
private lemma run_reduce_neg_mul (A : OnlineLearner C ℝ ℝ) (L : ℝ) (c : ℕ → C) (g : ℕ → ℝ)
    (t : ℕ) : (A.reduce (fun x ↦ L * x) fun _ b ↦ -L * b).run c g t =
      L * A.run c (fun s ↦ -L * g s) t := by
  rw [run_reduce, ← A.closedLoopFeedback_unique (g := fun s ↦ -L * g s) fun _ ↦ rfl]

/-- The regret against `u` of the plays of `A` for the slopes `-L * g t` is the loss of wealth of
the bettor of `run_reduce_neg_mul` on the coins `g t` plus `L u ∑ t < n, g t`. -/
private lemma regret_neg_mul_eq (A : OnlineLearner C ℝ ℝ) (L ε u : ℝ) (c : ℕ → C) (g : ℕ → ℝ)
    (n : ℕ) : regret (fun t x ↦ -L * g t * x) (A.run c fun s ↦ -L * g s) u n =
      ε - wealth ε g ((A.reduce (fun x ↦ L * x) fun _ b ↦ -L * b).run c g) n +
        L * u * ∑ t ∈ range n, g t := by
  simp only [regret_def, wealth_def, run_reduce_neg_mul, mul_sum]
  rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← sum_neg_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun t _ ↦ by ring

/-- **The lower bound of unconstrained online linear optimization** [Ora, Theorem 5.8]. Let `n`
be even, `L, ε, U > 0`, and `W = lambertW (√(e n) U L / (8 ε))` with `1 ≤ W ≤ √n / 2`. If the
learner `A` on `ℝ` has regret at most `ε` against `0` after `n` rounds for all linear losses
`x ↦ g t * x` with `|g t| ≤ L`, then for some such losses its regret against `U` or `-U` is at
least `U L √n (√(2 W) - 1) - 2 U L + ε`. -/
theorem exists_mul_sqrt_two_mul_lambertW_le_regret_run (A : OnlineLearner C ℝ ℝ) (c : ℕ → C)
    {n : ℕ} (hn : Even n) {L ε U : ℝ} (hL : 0 < L) (hε : 0 < ε) (hU : 0 < U)
    (hA : ∀ g : ℕ → ℝ, (∀ t < n, |g t| ≤ L) → regret (fun t x ↦ g t * x) (A.run c g) 0 n ≤ ε)
    (hW₁ : 1 ≤ lambertW (√(exp 1 * n) * U * L / (8 * ε)))
    (hW₂ : lambertW (√(exp 1 * n) * U * L / (8 * ε)) ≤ √n / 2) :
    ∃ g : ℕ → ℝ, (∀ t < n, |g t| ≤ L) ∧ ∃ u ∈ ({U, -U} : Set ℝ),
      U * L * √n * (√(2 * lambertW (√(exp 1 * n) * U * L / (8 * ε))) - 1) - 2 * U * L + ε ≤
        regret (fun t x ↦ g t * x) (A.run c g) u n := by
  set W := lambertW (√(exp 1 * n) * U * L / (8 * ε)) with hW
  set B := A.reduce (fun x ↦ L * x) fun _ b ↦ -L * b
  have hsqrt : 2 ≤ √(n : ℝ) := by linarith
  have hsqN : √(n : ℝ) * √n = n := Real.mul_self_sqrt n.cast_nonneg
  have hN : (4 : ℝ) ≤ n := by nlinarith
  -- the bias: `2 q / √n` is about `y = √(2 W - 1)`
  set y := √(2 * W - 1)
  have hy2 : y ^ 2 = 2 * W - 1 := Real.sq_sqrt (by linarith)
  have hy1 : 1 ≤ y := by nlinarith [Real.sqrt_nonneg (2 * W - 1)]
  have hyn : y ^ 2 ≤ √n := by linarith
  obtain ⟨q, hq0, hqn, hqQ, hQq⟩ := exists_bias hn hW₁ hW₂
  -- the bettor `B` keeps a nonnegative wealth on all sign sequences
  have hB (g : ℕ → ℝ) (hg : ∀ t < n, g t = 1 ∨ g t = -1) : 0 ≤ wealth ε g (B.run c g) n := by
    have h := hA (fun t ↦ -L * g t) fun t ht ↦ by
      rcases hg t ht with h | h <;> simp [h, abs_of_pos hL]
    have := regret_neg_mul_eq A L ε 0 c g n
    simp only [mul_zero, zero_mul, add_zero] at this
    linarith
  obtain ⟨g, hg, hsum, hwealth⟩ := B.exists_wealth_run_le_of_even c hn hq0 hqn hB
  refine ⟨fun t ↦ -L * g t, fun t ht ↦ by rcases hg t ht with h | h <;> simp [h, abs_of_pos hL],
    if 0 ≤ ∑ t ∈ range n, g t then U else -U, by split_ifs <;> simp, ?_⟩
  -- the regret against `U sign (∑ t, c t)` is `ε - wealth + L U |∑ t, c t|`
  have hLu : L * (if 0 ≤ ∑ t ∈ range n, g t then U else -U) * ∑ t ∈ range n, g t =
      L * U * |∑ t ∈ range n, g t| := by
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]
      ring
  rw [regret_neg_mul_eq A L ε, hLu]
  -- `W * exp (y ^ 2 / 2) = √n U L / (8 ε)`, by definition of `W`
  have hWE : W * exp (y ^ 2 / 2) = √n * U * L / (8 * ε) := by
    have h := lambertW_mul_exp_lambertW (x := √(exp 1 * n) * U * L / (8 * ε))
      ((neg_nonpos.2 (exp_pos _).le).trans (by positivity))
    rw [← hW, Real.sqrt_mul (exp_pos 1).le, ← exp_half] at h
    rw [show y ^ 2 / 2 = W - 1 / 2 by rw [hy2]; ring, exp_sub, ← mul_div_assoc, h]
    field_simp
  exact mul_sqrt_two_mul_sub_one_le hW₁ hε hU hL hWE (by linarith)
    (hwealth.trans (wealth_bound_le hN hε.le hy1 hyn q.cast_nonneg hqQ))

/-- **The lower bound of unconstrained online linear optimization**, in the form of
[Ora, Theorem 5.8]: under the hypotheses of `exists_mul_sqrt_two_mul_lambertW_le_regret_run`, for
some losses `x ↦ g t * x` with `|g t| ≤ L` the regret of `A` against `U` or `-U` is at least
`U L √n (√(2 lambertW (√n U L / (5 ε))) - 1) - 2 U L + ε`. -/
theorem exists_mul_sqrt_two_mul_lambertW_div_five_le_regret_run (A : OnlineLearner C ℝ ℝ)
    (c : ℕ → C) {n : ℕ} (hn : Even n) {L ε U : ℝ} (hL : 0 < L) (hε : 0 < ε) (hU : 0 < U)
    (hA : ∀ g : ℕ → ℝ, (∀ t < n, |g t| ≤ L) → regret (fun t x ↦ g t * x) (A.run c g) 0 n ≤ ε)
    (hW₁ : 1 ≤ lambertW (√(exp 1 * n) * U * L / (8 * ε)))
    (hW₂ : lambertW (√(exp 1 * n) * U * L / (8 * ε)) ≤ √n / 2) :
    ∃ g : ℕ → ℝ, (∀ t < n, |g t| ≤ L) ∧ ∃ u ∈ ({U, -U} : Set ℝ),
      U * L * √n * (√(2 * lambertW (√n * U * L / (5 * ε))) - 1) - 2 * U * L + ε ≤
        regret (fun t x ↦ g t * x) (A.run c g) u n := by
  obtain ⟨g, hg, u, hu, h⟩ :=
    A.exists_mul_sqrt_two_mul_lambertW_le_regret_run c hn hL hε hU hA hW₁ hW₂
  refine ⟨g, hg, u, hu, le_trans ?_ h⟩
  -- `1 / 5 ≤ √e / 8`, since `64 / 25 ≤ e`
  have he : (1 : ℝ) / 5 ≤ √(exp 1) / 8 := by
    have : (8 / 5 : ℝ) ≤ √(exp 1) := Real.le_sqrt_of_sq_le (by linarith [exp_one_gt_d9])
    linarith
  have hle : √n * U * L / (5 * ε) ≤ √(exp 1 * n) * U * L / (8 * ε) := by
    rw [Real.sqrt_mul (exp_pos 1).le]
    have h5 : √n * U * L / (5 * ε) = (1 / 5) * (√n * U * L / ε) := by field_simp
    have h8 : √(exp 1) * √n * U * L / (8 * ε) = (√(exp 1) / 8) * (√n * U * L / ε) := by
      field_simp
    rw [h5, h8]
    gcongr
  gcongr
  exact monotone_lambertW hle

end OnlineLearner

section Asymptotics

variable {L U K₁ K₂ : ℝ} {ε : ℕ → ℝ}

/-- For losses of size `L > 0`, a comparator norm `U > 0` and regret bounds `ε n` against `0`
bounded away from `0` and `∞`, the hypotheses `1 ≤ W ≤ √n / 2` on
`W = lambertW (√(e n) U L / (8 ε n))` of `exists_mul_sqrt_two_mul_lambertW_le_regret_run` hold for
all large `n`. -/
theorem eventually_one_le_lambertW_and_le (hL : 0 < L) (hU : 0 < U) (hK₁ : 0 < K₁)
    (hε₁ : ∀ n, K₁ ≤ ε n) (hε₂ : ∀ n, ε n ≤ K₂) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ lambertW (√(exp 1 * n) * U * L / (8 * ε n)) ∧
      lambertW (√(exp 1 * n) * U * L / (8 * ε n)) ≤ √n / 2 := by
  have hK₂ : 0 < K₂ := hK₁.trans_le ((hε₁ 0).trans (hε₂ 0))
  have hε (n : ℕ) : 0 < ε n := hK₁.trans_le (hε₁ n)
  -- the argument of `lambertW` is between `a₁ √n` and `a₂ √n`
  set a₁ := √(exp 1) * U * L / (8 * K₂)
  set a₂ := √(exp 1) * U * L / (8 * K₁)
  have hx (n : ℕ) : √(exp 1 * n) * U * L / (8 * ε n) = √n * (√(exp 1) * U * L / (8 * ε n)) := by
    rw [Real.sqrt_mul (exp_pos 1).le]
    ring
  have hlow (n : ℕ) : √n * a₁ ≤ √(exp 1 * n) * U * L / (8 * ε n) := by
    rw [hx]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
      (by linarith [hε n]) (by linarith [hε₂ n])) (Real.sqrt_nonneg _)
  have hup (n : ℕ) : √(exp 1 * n) * U * L / (8 * ε n) ≤ √n * a₂ := by
    rw [hx]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
      (by linarith) (by linarith [hε₁ n])) (Real.sqrt_nonneg _)
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have ha₁ : 0 < a₁ := by positivity
  filter_upwards [(hsqrt.atTop_mul_const ha₁).eventually_ge_atTop (exp 1),
    hsqrt.eventually_ge_atTop (4 * a₂)] with n h₁ h₂
  refine ⟨one_le_lambertW_iff.2 (h₁.trans (hlow n)), ?_⟩
  -- `lambertW x ≤ √x ≤ √(√n a₂) ≤ √n / 2`
  have hx0 : 0 ≤ √(exp 1 * n) * U * L / (8 * ε n) := by
    have := hε n
    positivity
  refine (lambertW_le_sqrt hx0).trans (Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩)
  rw [div_pow, Real.sq_sqrt n.cast_nonneg]
  calc √(exp 1 * n) * U * L / (8 * ε n) ≤ √n * a₂ := hup n
    _ ≤ √n * (√n / 4) := by gcongr; linarith
    _ = n / 2 ^ 2 := by rw [← mul_div_assoc, Real.mul_self_sqrt n.cast_nonneg]; norm_num

/-- For `ε n` bounded away from `0` and `∞`, `lambertW (√n U L / (5 ε n))` is asymptotic to
`log n / 2`: `2 lambertW (√n U L / (5 ε n)) / log n → 1`. -/
private lemma tendsto_two_mul_lambertW_div_log (hL : 0 < L) (hU : 0 < U) (hK₁ : 0 < K₁)
    (hε₁ : ∀ n, K₁ ≤ ε n) (hε₂ : ∀ n, ε n ≤ K₂) :
    Tendsto (fun n : ℕ ↦ 2 * lambertW (√n * U * L / (5 * ε n)) / log n) atTop (𝓝 1) := by
  have hK₂ : 0 < K₂ := hK₁.trans_le ((hε₁ 0).trans (hε₂ 0))
  have hε (n : ℕ) : 0 < ε n := hK₁.trans_le (hε₁ n)
  have hℓ : Tendsto (fun n : ℕ ↦ log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the argument is `√n * c n` with `c n ∈ [U L / (5 K₂), U L / (5 K₁)]`
  set c : ℕ → ℝ := fun n ↦ U * L / (5 * ε n)
  have hb (n : ℕ) : √n * U * L / (5 * ε n) = √n * c n := by simp only [c]; ring
  have hc₁ (n : ℕ) : U * L / (5 * K₂) ≤ c n :=
    div_le_div_of_nonneg_left (by positivity) (by linarith [hε n]) (by linarith [hε₂ n])
  have hc₂ (n : ℕ) : c n ≤ U * L / (5 * K₁) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith [hε₁ n])
  have hc0 (n : ℕ) : 0 < c n := (by positivity : (0 : ℝ) < U * L / (5 * K₂)).trans_le (hc₁ n)
  have hbtop : Tendsto (fun n : ℕ ↦ √n * c n) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ mul_le_mul_of_nonneg_left (hc₁ n) (Real.sqrt_nonneg _))
      ((tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const (by positivity))
  -- `log (√n c n) / log n = 1 / 2 + log (c n) / log n → 1 / 2`, as `log (c n)` is bounded
  set M := |log (U * L / (5 * K₂))| + |log (U * L / (5 * K₁))|
  have hlogc : Tendsto (fun n ↦ log (c n) / log n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := M)).div_atTop hℓ)
    filter_upwards [hℓ.eventually_gt_atTop 0] with n hn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
    gcongr
    have h₁ := log_le_log (by positivity) (hc₁ n)
    have h₂ := log_le_log (hc0 n) (hc₂ n)
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (log (U * L / (5 * K₂))), le_abs_self
      (log (U * L / (5 * K₁))), abs_nonneg (log (U * L / (5 * K₂))),
      abs_nonneg (log (U * L / (5 * K₁)))]
  have hlogb : Tendsto (fun n : ℕ ↦ log (√n * c n) / log n) atTop (𝓝 (1 / 2)) := by
    have h : Tendsto (fun n ↦ 1 / 2 + log (c n) / log n) atTop (𝓝 (1 / 2)) := by
      simpa using tendsto_const_nhds.add hlogc
    refine h.congr' ?_
    filter_upwards [hℓ.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hn hn0
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn0
    rw [log_mul (Real.sqrt_pos.2 hn0).ne' (hc0 n).ne', log_sqrt hn0.le]
    field_simp
  -- `lambertW x / log x → 1` gives the limit
  have h := ((tendsto_lambertW_div_log.comp hbtop).mul hlogb).const_mul 2
  norm_num at h
  refine h.congr' ?_
  filter_upwards [hbtop.eventually_gt_atTop 1, hℓ.eventually_gt_atTop 0] with n h₁ h₂
  have : log (√n * c n) ≠ 0 := (log_pos h₁).ne'
  simp only [hb]
  field_simp

/-- **The lower bound of unconstrained online linear optimization grows as `√(n log n)`**
[Ora, Theorem 5.8]: for losses of size `L > 0`, a comparator norm `U > 0` and regret bounds
`ε n` against `0` bounded away from `0` and `∞`, the lower bound
`U L √n (√(2 lambertW (√n U L / (5 ε n))) - 1) - 2 U L + ε n` of
`exists_mul_sqrt_two_mul_lambertW_div_five_le_regret_run` is asymptotic to `U L √(n log n)`. -/
theorem tendsto_mul_sqrt_two_mul_lambertW_div_sqrt_mul_log (hL : 0 < L) (hU : 0 < U)
    (hK₁ : 0 < K₁) (hε₁ : ∀ n, K₁ ≤ ε n) (hε₂ : ∀ n, ε n ≤ K₂) :
    Tendsto (fun n : ℕ ↦ (U * L * √n * (√(2 * lambertW (√n * U * L / (5 * ε n))) - 1) -
      2 * U * L + ε n) / (U * L * √(n * log n))) atTop (𝓝 1) := by
  have hℓ : Tendsto (fun n : ℕ ↦ log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsℓ : Tendsto (fun n : ℕ ↦ √(log n)) atTop atTop := tendsto_sqrt_atTop.comp hℓ
  have hX : Tendsto (fun n : ℕ ↦ U * L * (√n * √(log n))) atTop atTop :=
    ((tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_atTop₀ hsℓ).const_mul_atTop
      (by positivity)
  -- the expression is `√(2 W / log n) - 1 / √(log n) + (ε n - 2 U L) / (U L √n √(log n))`
  have h₁ := (tendsto_two_mul_lambertW_div_log hL hU hK₁ hε₁ hε₂).sqrt
  have h₂ : Tendsto (fun n : ℕ ↦ 1 / √(log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsℓ
  have h₃ : Tendsto (fun n ↦ (ε n - 2 * U * L) / (U * L * (√n * √(log n)))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := K₂ + 2 * U * L)).div_atTop hX)
    filter_upwards [hX.eventually_gt_atTop 0] with n hn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
    gcongr
    rw [abs_le]
    constructor <;> linarith [hε₁ n, hε₂ n, mul_pos hU hL]
  have h := (h₁.sub h₂).add h₃
  rw [Real.sqrt_one, sub_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [hℓ.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hn hn0
  have hn0' : (0 : ℝ) < n := Nat.cast_pos.2 hn0
  have hs : 0 < √(log n) := Real.sqrt_pos.2 hn
  have hs' : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0'
  rw [Real.sqrt_div' _ hn.le, Real.sqrt_mul hn0'.le]
  field_simp
  ring

/-- **The `√(n log n)` lower bound of unconstrained online linear optimization**
[Ora, Theorem 5.8]. Let the learner `A` on `ℝ` have regret at most `ε n` against `0` after `n`
rounds for all linear losses `x ↦ g t * x` with `|g t| ≤ L`, where `ε n` is bounded away from `0`
and `∞`. Then for every `U > 0` and all large even `n`, some such losses force a regret against `U`
or `-U` of at least `R n = U L √n (√(2 lambertW (√n U L / (5 ε n))) - 1) - 2 U L + ε n`, and
`R n / (U L √(n log n)) → 1` (`tendsto_mul_sqrt_two_mul_lambertW_div_sqrt_mul_log`). -/
theorem OnlineLearner.HasRegretBound.eventually_exists_mul_sqrt_two_mul_lambertW_le_regret_run
    {C : Type*} {A : OnlineLearner C ℝ ℝ}
    (hA : A.HasRegretBound (fun g x ↦ g * x) (fun _ g ↦ |g| ≤ L) {0} fun n _ _ _ ↦ ε n)
    (hL : 0 < L) (hU : 0 < U) (hK₁ : 0 < K₁) (hε₁ : ∀ n, K₁ ≤ ε n) (hε₂ : ∀ n, ε n ≤ K₂)
    (c : ℕ → C) :
    ∀ᶠ n : ℕ in atTop, Even n → ∃ g : ℕ → ℝ, (∀ t < n, |g t| ≤ L) ∧ ∃ u ∈ ({U, -U} : Set ℝ),
      U * L * √n * (√(2 * lambertW (√n * U * L / (5 * ε n))) - 1) - 2 * U * L + ε n ≤
        regret (fun t x ↦ g t * x) (A.run c g) u n := by
  filter_upwards [eventually_one_le_lambertW_and_le hL hU hK₁ hε₁ hε₂] with n hn heven
  exact A.exists_mul_sqrt_two_mul_lambertW_div_five_le_regret_run c heven hL
    (hK₁.trans_le (hε₁ n)) hU (fun g hg ↦ hA.regret_le hg rfl) hn.1 hn.2

end Asymptotics

end LMLExplore.OnlineLearning
