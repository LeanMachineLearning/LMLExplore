/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.CoinBetting
public import LMLExplore.OnlineLearning.Learner.Operations
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import LMLExplore.Algebra.BigOperators.Intervals
import LMLExplore.Algebra.Order.Field.Basic
import LMLExplore.Analysis.Normed.Group.Basic
import LMLExplore.Analysis.SpecialFunctions.Gamma.Inequalities
import LMLExplore.Analysis.SpecialFunctions.Log.Basic
import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Krichevsky–Trofimov bettor

The **Krichevsky–Trofimov (KT) bettor** [Ora, Algorithm 13.1] plays the coin-betting game of
`LMLExplore.OnlineLearning.CoinBetting` by betting at round `t` the fraction
`β t = (∑ s < t, c s) / (t + 1)` of its current wealth: the running mean of the past coins, shrunk
towards `0`. It has no parameter besides its initial wealth `ε`. Through the regret–reward duality
`regret_mul_le_of_mul_exp_sq_div_le_wealth` [Ora, Theorem 13.5], which rests on the conjugate
bound `Real.mul_sub_mul_exp_sq_div_le` [Ora, Lemma 13.6],
it is a **parameter-free** algorithm for one-dimensional online linear
optimization [Ora, Algorithm 13.2]: for losses `g t` with `|g t| ≤ L`, its regret against every
`u ∈ ℝ` is at most `|u| L √(2 n log (e |u| n / ε + 1)) + ε L`, with no learning rate to tune and no
bound on `|u|` to know.

The analysis [Ora, Theorem 13.4] goes through the **potential**
`ktPotential t x = 2 ^ t Γ((t + 1 + x) / 2) Γ((t + 1 - x) / 2) / (π t!)` of the number `t` of
rounds and of the sum `x` of the coins.

* For coins in `{-1, 1}`, the potential satisfies the recursion
  `ktPotential (t + 1) (x ± 1) = (1 ± x / (t + 1)) ktPotential t x` [Ora, Problem 13.1]
  (`ktPotential_succ_add_one`, `ktPotential_succ_sub_one`), from `Γ(y + 1) = y Γ(y)` and the
  symmetry `ktPotential t (-x) = ktPotential t x` (`ktPotential_neg`).
* For coins in `[-1, 1]`, the recursion becomes an inequality (`ktPotential_succ_add_le`), by
  Wendel's inequality `Γ(y + s) ≤ y ^ s Γ(y)` and the weighted inequality of arithmetic and
  geometric means. [Ora] proves it by the log-convexity of `Γ` in `c`; both are the same Hölder
  inequality.
* Hence the wealth of the KT bettor is at least `ε ktPotential n (∑ t < n, c t)`
  (`mul_ktPotential_le_wealth`).
* By the vertex lemma `Real.mul_log_add_mul_log_sub_log_Gamma_add_half_le` and
  `Real.sqrt_pi_mul_Gamma_add_one_le` [Ora, Lemmas A.12 and A.13],
  `ktPotential n x ≥ exp (n d(1 / 2 + x / (2 n), 1 / 2) - log n / 2 - 1)`, where `d` is the binary
  relative entropy (`exp_mul_klBerReal_sub_le_ktPotential`), and by Pinsker's inequality
  `ktPotential n x ≥ exp (x ^ 2 / (2 n) - log n / 2 - 1)` (`exp_sq_div_sub_le_ktPotential`).

The main consequences are:
* the wealth bound of [Ora, Theorem 13.4] for coins in `[-1, 1]`
  (`mul_exp_sq_div_sub_le_wealth`);
* for coins in `{-1, 1}`, the KT bettor earns at least `1 / (e √n)` times the wealth of every
  constant fraction [Ora, Theorem 13.2] (`mul_prod_one_add_mul_le_mul_wealth`);
* the parameter-free regret bound of one-dimensional online linear optimization
  (`krichevskyTrofimov_regret_le`), for the learner `OnlineLearner.krichevskyTrofimovOCO`
  (`OnlineLearner.hasRegretBound_krichevskyTrofimovOCO`), and with the horizon replaced by the
  number of rounds of nonzero losses when the rounds of zero losses are skipped
  (`OnlineLearner.hasRegretBound_skipZero_krichevskyTrofimovOCO`) [Ora, §13.2.1].

For coins in `[-1, 1]`, the bets of the KT bettor at round `t` are measurable functions of the
coins (`OnlineLearner.measurable_run_krichevskyTrofimov`) of absolute value at most `ε 2 ^ t`
(`OnlineLearner.abs_run_krichevskyTrofimov_le`), as the reduction of prediction with expert advice
to coin betting needs (`LMLExplore.OnlineLearning.ExpertsBetting`).

## Main definitions

* `LMLExplore.OnlineLearning.ktPotential t x`: the potential of the KT bettor.
* `LMLExplore.OnlineLearning.OnlineLearner.krichevskyTrofimov ε`: the KT bettor from the initial
  wealth `ε` [Ora, Algorithm 13.1].
* `LMLExplore.OnlineLearning.OnlineLearner.krichevskyTrofimovOCO L ε`: the KT algorithm for
  one-dimensional online linear optimization with losses bounded by `L` [Ora, Algorithm 13.2].

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Chapter 13.
* R. Krichevsky and V. Trofimov, *The performance of universal encoding*, IEEE Trans. Inform.
  Theory 27 (1981).
* F. Orabona and D. Pál, *Coin betting and parameter-free online learning*, NeurIPS 2016.
-/

public section

open Finset Real InformationTheory

namespace LMLExplore.OnlineLearning

section Potential

variable {t : ℕ} {x c : ℝ}

/-- The **potential of the Krichevsky–Trofimov bettor** [Ora, Theorem 13.4]:
`ktPotential t x = 2 ^ t Γ((t + 1 + x) / 2) Γ((t + 1 - x) / 2) / (π t!)`. After `t` rounds with
coins in `[-1, 1]` summing to `x`, the wealth of the KT bettor from the initial wealth `ε ≥ 0` is
at least `ε * ktPotential t x` (`mul_ktPotential_le_wealth`). -/
noncomputable def ktPotential (t : ℕ) (x : ℝ) : ℝ :=
  2 ^ t * Gamma ((t + 1 + x) / 2) * Gamma ((t + 1 - x) / 2) / (π * t.factorial)

lemma ktPotential_def (t : ℕ) (x : ℝ) :
    ktPotential t x =
      2 ^ t * Gamma ((t + 1 + x) / 2) * Gamma ((t + 1 - x) / 2) / (π * t.factorial) := (rfl)

/-- Before the first round, the potential is `1`, since `Γ(1 / 2) = √π`. -/
@[simp]
lemma ktPotential_zero_zero : ktPotential 0 0 = 1 := by
  have h : ((0 : ℕ) + 1 + 0 : ℝ) / 2 = 1 / 2 := by norm_num
  have h' : ((0 : ℕ) + 1 - 0 : ℝ) / 2 = 1 / 2 := by norm_num
  rw [ktPotential_def, h, h', Gamma_one_half_eq, pow_zero, one_mul, mul_self_sqrt pi_pos.le,
    Nat.factorial_zero, Nat.cast_one, mul_one, div_self pi_ne_zero]

/-- The potential is positive on `(-(t + 1), t + 1)`. -/
lemma ktPotential_pos (hx : |x| < t + 1) : 0 < ktPotential t x := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.1 hx
  have h₁ := Gamma_pos_of_pos (show 0 < ((t : ℝ) + 1 + x) / 2 by linarith)
  have h₂ := Gamma_pos_of_pos (show 0 < ((t : ℝ) + 1 - x) / 2 by linarith)
  rw [ktPotential_def]
  have := pi_pos
  positivity

/-- The potential is symmetric: heads and tails play the same role. -/
lemma ktPotential_neg (t : ℕ) (x : ℝ) : ktPotential t (-x) = ktPotential t x := by
  rw [ktPotential_def, ktPotential_def, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

/-- The logarithm of the potential on `(-(t + 1), t + 1)`. -/
lemma log_ktPotential (hx : |x| < t + 1) :
    log (ktPotential t x) = t * log 2 + log (Gamma ((t + 1 + x) / 2)) +
      log (Gamma ((t + 1 - x) / 2)) - log π - log t.factorial := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.1 hx
  have h₁ := Gamma_pos_of_pos (show 0 < ((t : ℝ) + 1 + x) / 2 by linarith)
  have h₂ := Gamma_pos_of_pos (show 0 < ((t : ℝ) + 1 - x) / 2 by linarith)
  have := pi_pos
  rw [ktPotential_def, log_div (by positivity) (by positivity), log_mul (by positivity) h₂.ne',
    log_mul (by positivity) h₁.ne', log_pow, log_mul pi_pos.ne' (by positivity)]
  ring

/-- **The recursion of the potential for a head** [Ora, Problem 13.1]: the coin `1` multiplies the
potential by `1 + x / (t + 1)`. -/
lemma ktPotential_succ_add_one (hx : (t : ℝ) + 1 + x ≠ 0) :
    ktPotential (t + 1) (x + 1) = (1 + x / (t + 1)) * ktPotential t x := by
  have e₁ : (((t + 1 : ℕ) : ℝ) + 1 + (x + 1)) / 2 = (t + 1 + x) / 2 + 1 := by push_cast; ring
  have e₂ : (((t + 1 : ℕ) : ℝ) + 1 - (x + 1)) / 2 = (t + 1 - x) / 2 := by push_cast; ring
  have ht : (t : ℝ) + 1 ≠ 0 := by positivity
  rw [ktPotential_def, ktPotential_def, e₁, e₂, Gamma_add_one (div_ne_zero hx two_ne_zero),
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  have := pi_pos.ne'
  have := (Nat.cast_pos.2 (Nat.factorial_pos t) : (0 : ℝ) < t.factorial).ne'
  field_simp

/-- **The recursion of the potential for a tail** [Ora, Problem 13.1]: the coin `-1` multiplies
the potential by `1 - x / (t + 1)`. It is the recursion for a head at `-x`, by the symmetry
`ktPotential_neg`. -/
lemma ktPotential_succ_sub_one (hx : (t : ℝ) + 1 - x ≠ 0) :
    ktPotential (t + 1) (x - 1) = (1 - x / (t + 1)) * ktPotential t x := by
  have h := ktPotential_succ_add_one (t := t) (x := -x) (by rwa [← sub_eq_add_neg])
  rwa [neg_add_eq_sub, ← neg_sub, ktPotential_neg, ktPotential_neg, neg_div,
    ← sub_eq_add_neg] at h

/-- **The potential inequality of the Krichevsky–Trofimov bettor** [Ora, (13.1)]: for
`|x| < t + 1` and a coin `c ∈ [-1, 1]`,
`ktPotential (t + 1) (x + c) ≤ (1 + c x / (t + 1)) ktPotential t x`. With
`P = (t + 1 + x) / 2` and `Q = (t + 1 - x) / 2`, the arguments of `Γ` at `x + c` are `P + a` and
`Q + b` for the weights `a = (1 + c) / 2` and `b = (1 - c) / 2`. Wendel's inequality bounds
`Γ(P + a) Γ(Q + b)` by `P ^ a Q ^ b Γ(P) Γ(Q)`, and
`P ^ a Q ^ b ≤ a P + b Q = (t + 1 + c x) / 2`. -/
theorem ktPotential_succ_add_le (hx : |x| < t + 1) (hc : |c| ≤ 1) :
    ktPotential (t + 1) (x + c) ≤ (1 + c * x / (t + 1)) * ktPotential t x := by
  obtain ⟨hx₁, hx₂⟩ := abs_lt.1 hx
  obtain ⟨hc₁, hc₂⟩ := abs_le.1 hc
  set P : ℝ := (t + 1 + x) / 2 with hP_def
  set Q : ℝ := (t + 1 - x) / 2 with hQ_def
  have hP : 0 < P := by linarith
  have hQ : 0 < Q := by linarith
  have hu := Gamma_add_le_rpow_mul_Gamma hP (s := (1 + c) / 2) (by linarith) (by linarith)
  have hv := Gamma_add_le_rpow_mul_Gamma hQ (s := (1 - c) / 2) (by linarith) (by linarith)
  have hmean := geom_mean_le_arith_mean2_weighted (w₁ := (1 + c) / 2) (w₂ := (1 - c) / 2)
    (by linarith) (by linarith) hP.le hQ.le (by ring)
  have hGP := Gamma_pos_of_pos hP
  have hGQ := Gamma_pos_of_pos hQ
  have key : Gamma (P + (1 + c) / 2) * Gamma (Q + (1 - c) / 2) ≤
      (t + 1 + c * x) / 2 * (Gamma P * Gamma Q) :=
    calc Gamma (P + (1 + c) / 2) * Gamma (Q + (1 - c) / 2)
        ≤ (P ^ ((1 + c) / 2) * Gamma P) * (Q ^ ((1 - c) / 2) * Gamma Q) :=
          mul_le_mul hu hv (Gamma_pos_of_pos (by linarith)).le (by positivity)
      _ = P ^ ((1 + c) / 2) * Q ^ ((1 - c) / 2) * (Gamma P * Gamma Q) := by ring
      _ ≤ ((1 + c) / 2 * P + (1 - c) / 2 * Q) * (Gamma P * Gamma Q) :=
          mul_le_mul_of_nonneg_right hmean (by positivity)
      _ = (t + 1 + c * x) / 2 * (Gamma P * Gamma Q) := by rw [hP_def, hQ_def]; ring
  have e₁ : (((t + 1 : ℕ) : ℝ) + 1 + (x + c)) / 2 = P + (1 + c) / 2 := by push_cast; ring
  have e₂ : (((t + 1 : ℕ) : ℝ) + 1 - (x + c)) / 2 = Q + (1 - c) / 2 := by push_cast; ring
  have hfact : (0 : ℝ) < t.factorial := Nat.cast_pos.2 (Nat.factorial_pos t)
  have hK : 0 ≤ 2 ^ t * 2 / (π * ((t + 1) * t.factorial)) := by
    have := pi_pos
    positivity
  rw [ktPotential_def, ktPotential_def, e₁, e₂, ← hP_def, ← hQ_def, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_succ, pow_succ]
  calc 2 ^ t * 2 * Gamma (P + (1 + c) / 2) * Gamma (Q + (1 - c) / 2) /
        (π * ((t + 1) * t.factorial))
      = 2 ^ t * 2 / (π * ((t + 1) * t.factorial)) *
          (Gamma (P + (1 + c) / 2) * Gamma (Q + (1 - c) / 2)) := by ring
    _ ≤ 2 ^ t * 2 / (π * ((t + 1) * t.factorial)) *
          ((t + 1 + c * x) / 2 * (Gamma P * Gamma Q)) := mul_le_mul_of_nonneg_left key hK
    _ = (1 + c * x / (t + 1)) * (2 ^ t * Gamma P * Gamma Q / (π * t.factorial)) := by
      have := pi_pos.ne'
      field_simp

/-- **The lower bound on the potential through the binary relative entropy** [Ora, proof of
Theorem 13.4]: for `t ≥ 1` and `|x| ≤ t`,
`exp (t d(1 / 2 + x / (2 t), 1 / 2) - log t / 2 - 1) ≤ ktPotential t x`, where `d` is the binary
relative entropy. This combines the vertex lemma
`Real.mul_log_add_mul_log_sub_log_Gamma_add_half_le` at `((t + x) / 2, (t - x) / 2)` [Ora,
Lemma A.13] with the logarithmic form
`Real.log_pi_div_two_add_log_Gamma_add_one_sub_log_Gamma_add_half_le` of [Ora, Lemma A.12]. -/
theorem exp_mul_klBerReal_sub_le_ktPotential (ht : 1 ≤ t) (hx : |x| ≤ t) :
    exp (t * klBerReal (1 / 2 + x / (2 * t)) (1 / 2) - log t / 2 - 1) ≤ ktPotential t x := by
  obtain ⟨hx₁, hx₂⟩ := abs_le.1 hx
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  set a : ℝ := (t + x) / 2 with ha_def
  set b : ℝ := (t - x) / 2 with hb_def
  have ha : 0 ≤ a := by linarith
  have hb : 0 ≤ b := by linarith
  have hab : a + b = t := by rw [ha_def, hb_def]; ring
  have hlt : |x| < t + 1 := by rw [abs_lt]; constructor <;> linarith
  have hpos : 0 < ktPotential t x := ktPotential_pos hlt
  -- the logarithm of the potential
  have hlog := log_ktPotential hlt
  rw [show ((t : ℝ) + 1 + x) / 2 = a + 1 / 2 by rw [ha_def]; ring,
    show ((t : ℝ) + 1 - x) / 2 = b + 1 / 2 by rw [hb_def]; ring] at hlog
  -- the vertex lemma and Lemma A.12
  have hvertex := Real.mul_log_add_mul_log_sub_log_Gamma_add_half_le ha hb
  rw [hab, Gamma_one_half_eq, log_sqrt pi_pos.le] at hvertex
  have hA := Real.log_pi_div_two_add_log_Gamma_add_one_sub_log_Gamma_add_half_le htR
  rw [Gamma_nat_eq_factorial] at hA
  have hp : 1 / 2 + x / (2 * t) = a / t := by rw [ha_def]; field_simp
  -- `y log (2 y / t) = y log 2 + y log y - y log t` for `y ≥ 0`, with `0 log 0 = 0`
  have hexpand {y : ℝ} (hy : 0 ≤ y) : y * log (2 * y / t) = y * log 2 + y * log y - y * log t := by
    rcases hy.eq_or_lt with rfl | hy
    · simp
    rw [log_div (by positivity) htpos.ne', log_mul two_ne_zero hy.ne']
    ring
  have hb' : (t : ℝ) - a = b := by linarith
  have h2 : a * log 2 + b * log 2 = t * log 2 := by rw [← add_mul, hab]
  have h3 : a * log t + b * log t = t * log t := by rw [← add_mul, hab]
  rw [hp, mul_klBerReal_div_one_div_two, hb', hexpand ha, hexpand hb, ← exp_log hpos, hlog]
  exact exp_le_exp.2 (by linarith)

/-- **The Gaussian lower bound on the potential** [Ora, proof of Theorem 13.4]: for `t ≥ 1` and
`|x| ≤ t`, `exp (x ^ 2 / (2 t) - log t / 2 - 1) ≤ ktPotential t x`. It follows from
`exp_mul_klBerReal_sub_le_ktPotential` by Pinsker's inequality. -/
theorem exp_sq_div_sub_le_ktPotential (ht : 1 ≤ t) (hx : |x| ≤ t) :
    exp (x ^ 2 / (2 * t) - log t / 2 - 1) ≤ ktPotential t x := by
  obtain ⟨hx₁, hx₂⟩ := abs_le.1 hx
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  refine (exp_le_exp.2 ?_).trans (exp_mul_klBerReal_sub_le_ktPotential ht hx)
  have hp : 1 / 2 + x / (2 * t) ∈ Set.Icc (0 : ℝ) 1 := by
    have e : 1 / 2 + x / (2 * t) = (t + x) / (2 * t) := by field_simp
    rw [e]
    exact ⟨div_nonneg (by linarith) (by positivity), (div_le_one (by positivity)).2 (by linarith)⟩
  have hpinsker := two_mul_sq_le_klBerReal (q := 1 / 2) hp ⟨by norm_num, by norm_num⟩
    (klBer_ne_top ⟨by norm_num, by norm_num⟩)
  have e : x ^ 2 / (2 * t) = t * (2 * (1 / 2 + x / (2 * t) - 1 / 2) ^ 2) := by
    field_simp
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hpinsker htpos.le]

end Potential

section Wealth

variable {ε : ℝ} {c x : ℕ → ℝ} {n : ℕ}

/-- **The wealth of the Krichevsky–Trofimov bettor is at least its potential** [Ora, proof of
Theorem 13.4]: if the bets `x` are the KT bets `x t = (∑ s < t, c s) / (t + 1) * W t` on coins
in `[-1, 1]` from the initial wealth `ε ≥ 0`, then `ε * ktPotential n (∑ t < n, c t)` is at most
the wealth after `n` rounds. By induction on `n`, from the potential inequality
`ktPotential_succ_add_le`. -/
theorem mul_ktPotential_le_wealth (hε : 0 ≤ ε) (hc : ∀ t < n, |c t| ≤ 1)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, c s) / (t + 1) * wealth ε c x t) :
    ε * ktPotential n (∑ t ∈ range n, c t) ≤ wealth ε c x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (fun t ht ↦ hc t (by omega)) fun t ht ↦ hx t (by omega)
    have hS : |∑ t ∈ range n, c t| ≤ n := abs_sum_le_of_abs_le_one fun t ht ↦ hc t (by omega)
    have hcn := hc n n.lt_succ_self
    set S := ∑ t ∈ range n, c t
    -- the factor `1 + c n * S / (n + 1)` of the round is nonnegative
    have hfac : 0 ≤ 1 + c n * S / (n + 1) := by
      have h1 : |c n * S| ≤ n := by
        rw [abs_mul]
        nlinarith [abs_nonneg (c n), abs_nonneg S]
      have e : 1 + c n * S / (n + 1) = (n + 1 + c n * S) / (n + 1) := by field_simp
      rw [e]
      exact div_nonneg (by linarith [neg_abs_le (c n * S)]) (by positivity)
    rw [wealth_add_one, hx n n.lt_succ_self, sum_range_succ]
    calc ε * ktPotential (n + 1) (S + c n)
        ≤ ε * ((1 + c n * S / (n + 1)) * ktPotential n S) :=
          mul_le_mul_of_nonneg_left (ktPotential_succ_add_le (by linarith) hcn) hε
      _ = (1 + c n * S / (n + 1)) * (ε * ktPotential n S) := by ring
      _ ≤ (1 + c n * S / (n + 1)) * wealth ε c x n := mul_le_mul_of_nonneg_left ih hfac
      _ = wealth ε c x n + c n * (S / (n + 1) * wealth ε c x n) := by ring

/-- **The wealth bound of the Krichevsky–Trofimov bettor** [Ora, Theorem 13.4]: for coins in
`[-1, 1]`, the KT bets from the initial wealth `ε ≥ 0` have, after `n ≥ 1` rounds, a wealth at
least `ε exp ((∑ t < n, c t) ^ 2 / (2 n) - log n / 2 - 1)`. -/
theorem mul_exp_sq_div_sub_le_wealth (hε : 0 ≤ ε) (hn : 1 ≤ n) (hc : ∀ t < n, |c t| ≤ 1)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, c s) / (t + 1) * wealth ε c x t) :
    ε * exp ((∑ t ∈ range n, c t) ^ 2 / (2 * n) - log n / 2 - 1) ≤ wealth ε c x n :=
  (mul_le_mul_of_nonneg_left (exp_sq_div_sub_le_ktPotential hn (abs_sum_le_of_abs_le_one hc))
    hε).trans
    (mul_ktPotential_le_wealth hε hc hx)

/-- **The Krichevsky–Trofimov bettor against constant fractions** [Ora, Theorem 13.2]: for coins
in `{-1, 1}` and every constant fraction `β ∈ [-1, 1]`, the wealth `ε ∏ t < n, (1 + β c t)` of
the constant fraction is at most `e √n` times the wealth of the KT bets after `n ≥ 1` rounds.
Equivalently, the logarithm of the wealth of the KT bettor is at least the logarithm of the wealth
of the best constant fraction minus `log n / 2 + 1`. -/
theorem mul_prod_one_add_mul_le_mul_wealth (hε : 0 ≤ ε) (hn : 1 ≤ n)
    (hc : ∀ t < n, c t = 1 ∨ c t = -1)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, c s) / (t + 1) * wealth ε c x t) {β : ℝ}
    (hβ : |β| ≤ 1) :
    ε * ∏ t ∈ range n, (1 + β * c t) ≤ exp 1 * √n * wealth ε c x n := by
  have hc' : ∀ t < n, |c t| ≤ 1 := fun t ht ↦ by rcases hc t ht with h | h <;> simp [h]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set S := ∑ t ∈ range n, c t
  set K := n * klBerReal (1 / 2 + S / (2 * n)) (1 / 2)
  have hsqrt : √(n : ℝ) = exp (log n / 2) := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hnpos]
    ring_nf
  have hK : exp K = exp 1 * √n * exp (K - log n / 2 - 1) := by
    rw [hsqrt, ← exp_add, ← exp_add]
    ring_nf
  calc ε * ∏ t ∈ range n, (1 + β * c t) ≤ ε * exp K :=
        mul_le_mul_of_nonneg_left (prod_one_add_mul_le_exp hc hβ) hε
    _ = exp 1 * √n * (ε * exp (K - log n / 2 - 1)) := by rw [hK]; ring
    _ ≤ exp 1 * √n * (ε * ktPotential n S) := by
        gcongr
        exact exp_mul_klBerReal_sub_le_ktPotential hn (abs_sum_le_of_abs_le_one hc')
    _ ≤ exp 1 * √n * wealth ε c x n := by
        gcongr
        exact mul_ktPotential_le_wealth hε hc' hx

end Wealth

section Regret

variable {ε L : ℝ} {g x : ℕ → ℝ} {n : ℕ}

/-- **The regret of the Krichevsky–Trofimov algorithm** for one-dimensional online linear
optimization [Ora, §13.2]. Let `|g t| ≤ L` for the rounds `t < n`, and let `x` be the KT bets
from the initial wealth `ε > 0` on the coins `-g t / L`. Then for every `u ∈ ℝ`,
`∑ t < n, g t (x t - u) ≤ |u| L √(2 n log (e |u| n / ε + 1)) + ε L`.
It is the regret–reward duality `regret_mul_le_of_mul_exp_sq_div_le_wealth` [Ora, Theorem 13.5]
for the wealth bound `mul_exp_sq_div_sub_le_wealth`. -/
theorem krichevskyTrofimov_regret_le (hε : 0 < ε) (hL : 0 < L) (hg : ∀ t < n, |g t| ≤ L)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, -g s / L) / (t + 1) * wealth ε (fun s ↦ -g s / L) x t)
    (u : ℝ) :
    regret (fun t y ↦ g t * y) x u n ≤ |u| * L * √(2 * n * log (exp 1 * |u| * n / ε + 1)) +
      ε * L := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [regret_zero]
    positivity
  set c : ℕ → ℝ := fun s ↦ -g s / L
  have hc : ∀ t < n, |c t| ≤ 1 := fun t ht ↦ by
    simpa only [c, neg_div, abs_neg] using abs_div_le_one_of_abs_le (hg t ht)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set S := ∑ t ∈ range n, c t with hS
  set β := ε * exp (-(log n / 2) - 1) with hβ_def
  have hβ : 0 < β := by positivity
  -- the wealth is at least `β * exp (S ^ 2 / (2 n))`
  have hW : β * exp (S ^ 2 / (2 * n)) ≤ wealth ε c x n := by
    refine le_of_eq_of_le ?_ (mul_exp_sq_div_sub_le_wealth hε.le hn hc hx)
    rw [hβ_def, mul_assoc, ← exp_add, hS]
    ring_nf
  have hdual := regret_mul_le_of_mul_exp_sq_div_le_wealth hL hnR hβ hW u
  -- `n * u ^ 2 / β ^ 2 = (e |u| n / ε) ^ 2`
  have hβsq : (n : ℝ) * u ^ 2 / β ^ 2 = (exp 1 * |u| * n / ε) ^ 2 := by
    rw [hβ_def, mul_pow, ← exp_natCast_mul]
    have : ((2 : ℕ) : ℝ) * (-(log n / 2) - 1) = -log n - 2 := by push_cast; ring
    rw [this, exp_sub, exp_neg, exp_log hnR, div_pow, mul_pow, mul_pow, sq_abs,
      show exp 2 = exp 1 ^ 2 by rw [← exp_natCast_mul]; norm_num]
    field_simp
  rw [hβsq] at hdual
  -- `log (1 + z ^ 2) ≤ 2 log (z + 1)` for `z = e |u| n / ε ≥ 0`
  have hlog := Real.log_one_add_sq_le_two_mul_log_add_one
    (show 0 ≤ exp 1 * |u| * n / ε by positivity)
  have hsqrt : √(n * log (1 + (exp 1 * |u| * n / ε) ^ 2)) ≤
      √(2 * n * log (exp 1 * |u| * n / ε + 1)) := by
    refine sqrt_le_sqrt ?_
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (abs_nonneg u) hL.le)]

end Regret

namespace OnlineLearner

variable {C : Type*}

/-- The **Krichevsky–Trofimov bettor** [Ora, Algorithm 13.1] from the initial wealth `ε`: a bettor
whose feedback is the coins, and which bets at round `t` the fraction `(∑ s < t, c s) / (t + 1)`
of its wealth (`run_krichevskyTrofimov`). -/
noncomputable def krichevskyTrofimov (ε : ℝ) : OnlineLearner C ℝ ℝ :=
  fractionBettor (fun t c ↦ (∑ s ∈ range t, c s) / (t + 1)) ε

/-- **The bets of the Krichevsky–Trofimov bettor**: at round `t`, it bets the fraction
`(∑ s < t, c s) / (t + 1)` of its wealth on the coins `c`. -/
theorem run_krichevskyTrofimov (ε : ℝ) (d : ℕ → C) (c : ℕ → ℝ) (t : ℕ) :
    (krichevskyTrofimov ε).run d c t =
      (∑ s ∈ range t, c s) / (t + 1) * wealth ε c ((krichevskyTrofimov ε).run d c) t :=
  run_fractionBettor (fun _ _ _ ↦ apply_sum_range_congr fun t (S : ℝ) ↦ S / (t + 1)) ε d c t

/-- The **Krichevsky–Trofimov algorithm for one-dimensional online linear optimization**
[Ora, Algorithm 13.2] with losses bounded by `L`, from the initial wealth `ε`: on the linear
losses `g t`, it plays the bets of the KT bettor on the coins `-g t / L`
(`run_krichevskyTrofimovOCO`). -/
noncomputable def krichevskyTrofimovOCO (L ε : ℝ) : OnlineLearner C ℝ ℝ :=
  fractionBettorOCO (fun t c ↦ (∑ s ∈ range t, c s) / (t + 1)) L ε

/-- The plays of the Krichevsky–Trofimov algorithm are the bets of the KT bettor on the coins
`-g t / L`. -/
theorem run_krichevskyTrofimovOCO (L ε : ℝ) (d : ℕ → C) (g : ℕ → ℝ) (t : ℕ) :
    (krichevskyTrofimovOCO L ε).run d g t =
      (krichevskyTrofimov ε).run d (fun s ↦ -g s / L) t :=
  run_fractionBettorOCO _ L ε d g t

variable {ε L : ℝ}

/-- **The parameter-free regret bound of the Krichevsky–Trofimov algorithm** [Ora, §13.2]: for
`ε, L > 0`, on linear losses `g t` with `|g t| ≤ L`, the regret against every `u ∈ ℝ` after `n`
rounds is at most `|u| L √(2 n log (e |u| n / ε + 1)) + ε L`. -/
theorem hasRegretBound_krichevskyTrofimovOCO (hε : 0 < ε) (hL : 0 < L) :
    (krichevskyTrofimovOCO (C := C) L ε).HasRegretBound (fun g x ↦ g * x) (fun _ g ↦ |g| ≤ L)
      Set.univ fun n _ _ u ↦ |u| * L * √(2 * n * log (exp 1 * |u| * n / ε + 1)) + ε * L :=
  hasRegretBound_iff.2 fun d g _ hg u _ ↦ krichevskyTrofimov_regret_le hε hL hg
    (fun t _ ↦ run_fractionBettorOCO_eq_mul_wealth
      (fun _ _ _ ↦ apply_sum_range_congr fun t (S : ℝ) ↦ S / (t + 1)) L ε d g t) u

/-- **The Krichevsky–Trofimov algorithm skipping the rounds of zero loss** [Ora, §13.2.1]: run
on the rounds with `g t ≠ 0` only, its regret bound holds with the horizon `n` replaced by the
number `Nat.count (g · ≠ 0) n` of these rounds. -/
theorem hasRegretBound_skipZero_krichevskyTrofimovOCO (hε : 0 < ε) (hL : 0 < L) :
    (krichevskyTrofimovOCO (C := C) L ε).skipZero.HasRegretBound (fun g x ↦ g * x)
      (fun _ g ↦ |g| ≤ L) Set.univ fun n _ g u ↦
        |u| * L * √(2 * Nat.count (g · ≠ 0) n *
          log (exp 1 * |u| * Nat.count (g · ≠ 0) n / ε + 1)) + ε * L :=
  (hasRegretBound_krichevskyTrofimovOCO hε hL).skipZero fun _ ↦ zero_mul _

/-- The bets of the Krichevsky–Trofimov bettor are measurable functions of the coins. -/
lemma measurable_run_krichevskyTrofimov (ε : ℝ) (d : ℕ → C) (t : ℕ) :
    Measurable fun c : ℕ → ℝ ↦ (krichevskyTrofimov ε).run d c t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    simp_rw [run_krichevskyTrofimov ε d _ t, wealth_def]
    refine ((Finset.measurable_sum _ fun s _ ↦ measurable_pi_apply s).div_const _).mul
      (measurable_const.add (Finset.measurable_sum _ fun s hs ↦
        (measurable_pi_apply s).mul (ih s (mem_range.1 hs))))

/-- For coins in `[-1, 1]`, the Krichevsky–Trofimov bettor from the initial wealth `ε ≥ 0` bets
at most `ε 2 ^ t` in absolute value at round `t`. -/
lemma abs_run_krichevskyTrofimov_le (hε : 0 ≤ ε) (d : ℕ → C) {c : ℕ → ℝ} {t : ℕ}
    (hc : ∀ s < t, |c s| ≤ 1) : |(krichevskyTrofimov ε).run d c t| ≤ ε * 2 ^ t := by
  set β : ℕ → ℝ := fun s ↦ (∑ r ∈ range s, c r) / (s + 1)
  have hβ (s : ℕ) (hs : s ≤ t) : |β s| ≤ 1 := by
    have hsum : |∑ r ∈ range s, c r| ≤ s := by
      simpa using norm_sum_le_card_mul (range s) (L := 1) fun r hr ↦
        (Real.norm_eq_abs _).trans_le (hc r ((mem_range.1 hr).trans_le hs))
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < s + 1), div_le_one (by positivity)]
    linarith
  have hrun (s : ℕ) : (krichevskyTrofimov ε).run d c s =
      β s * wealth ε c ((krichevskyTrofimov ε).run d c) s := run_krichevskyTrofimov ε d c s
  have hfac (s : ℕ) (hs : s < t) : 0 ≤ 1 + β s * c s ∧ 1 + β s * c s ≤ 2 := by
    have : |β s * c s| ≤ 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg (β s), abs_nonneg (c s), hβ s hs.le, hc s hs]
    constructor <;> linarith [abs_le.1 this]
  have hW : wealth ε c ((krichevskyTrofimov ε).run d c) t ≤ ε * 2 ^ t := by
    rw [wealth_eq_mul_prod fun s _ ↦ hrun s]
    refine mul_le_mul_of_nonneg_left ?_ hε
    calc ∏ s ∈ range t, (1 + β s * c s) ≤ ∏ _s ∈ range t, (2 : ℝ) :=
          prod_le_prod₀ (fun s hs ↦ (hfac s (mem_range.1 hs)).1)
            fun s hs ↦ (hfac s (mem_range.1 hs)).2
      _ = 2 ^ t := by rw [prod_const, card_range]
  have hW0 : 0 ≤ wealth ε c ((krichevskyTrofimov ε).run d c) t :=
    wealth_nonneg hε (fun s _ ↦ hrun s) (fun s hs ↦ hβ s hs.le) hc
  rw [hrun, abs_mul, abs_of_nonneg hW0]
  calc |β t| * wealth ε c ((krichevskyTrofimov ε).run d c) t
      ≤ 1 * wealth ε c ((krichevskyTrofimov ε).run d c) t :=
        mul_le_mul_of_nonneg_right (hβ t le_rfl) hW0
    _ ≤ ε * 2 ^ t := by rw [one_mul]; exact hW

end OnlineLearner

end LMLExplore.OnlineLearning
