/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.Learner.Basic
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli
import LMLExplore.Analysis.Normed.Module.RademacherSum
import LMLExplore.Data.Nat.Choose.Tail
import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# The coin-betting game

In the **coin-betting game** [Ora, §5.3], a bettor starts with an initial wealth `ε` and, at each
round `t`, bets `x t ∈ ℝ` on the outcome `c t ∈ [-1, 1]` of a coin, at even odds: the sign of
`x t` is the side it bets on and `|x t|` the amount. Its wealth after `t` rounds is
`wealth ε c x t = ε + ∑ s < t, c s * x s`. A bettor is an online learner `OnlineLearner C ℝ ℝ` whose
plays are its bets and whose feedback is the coins. As for all online games, nothing is assumed on
how the coins are chosen.

Many bettors bet a signed fraction `β t ∈ [-1, 1]` of their current wealth, `x t = β t * W t`; their
wealth is then `ε * ∏ t < n, (1 + β t * c t)` (`wealth_eq_mul_prod`), and stays nonnegative
(`wealth_nonneg`). This file proves the facts about the game that relate it to online linear
optimization.

* **Online linear optimization is betting.** For the linear losses `g t = -L c t` on `ℝ`, the
  regret against `0` of the bets is `L * (ε - wealth ε c x n)` (`regret_neg_mul_eq_mul_sub_wealth`):
  a small regret against `0` is a large wealth.
* **The best constant fraction** [Ora, Remark 5.6]. For coins in `{-1, 1}`, the wealth
  `ε * ∏ t < n, (1 + β * c t)` of the best constant fraction `β ∈ [-1, 1]` is
  `ε * exp (n * d(1 / 2 + (∑ t < n, c t) / (2 n), 1 / 2))`, where `d` is the binary relative
  entropy, attained at `β = (∑ t < n, c t) / n` (`isGreatest_prod_one_add_mul`).
* **Learners with a bounded regret against `0` are bettors** [Ora, Theorem 5.7]. In a real normed
  space, if a learner has regret at most `B n` against `0` after `n` rounds for all linear losses
  of dual norm at most `L`, then `L * ‖x t‖ ≤ B (t + 1) - ∑ s < t, y s (x s)`
  (`OnlineLearner.HasRegretBound.mul_norm_run_le`); for `B` nondecreasing it plays a vector
  fraction `β t` with `‖β t‖ ≤ 1 / L` of the "wealth" `B n - ∑ s < t, y s (x s)`
  (`OnlineLearner.HasRegretBound.exists_norm_le_run_eq_smul`).
* **No bettor gets rich on all biased sequences** [Ora, Theorem 5.5]. For `n / 2 < k ≤ n`, every
  bettor whose wealth stays nonnegative on all sequences of coins in `{-1, 1}` has, on some such
  sequence with `|∑ t < n, c t| ≥ 2 k - n`, wealth at most
  `3 ε / 2 * ((2 k - n) / √n + 1) * exp (n * d(k / n, 1 / 2))`
  (`OnlineLearner.exists_wealth_run_le`). Up to the polynomial factor, this is the wealth of the
  best constant fraction on these sequences. For `n` even and `k = n / 2 + q`, it is the form
  `3 ε / 2 * (2 q / √n + 1) * exp (n * d(1 / 2 + q / n, 1 / 2))` of [Ora]
  (`OnlineLearner.exists_wealth_run_le_of_even`).

The proof of the last bound is the probabilistic method: for independent Rademacher coins, the
bets are predictable, so the mean wealth is `ε`. The wealth is nonnegative, so it is at most
`ε / P(|∑ t < n, c t| ≥ 2 k - n)` for some sequence in this event, and the binomial tail
`Nat.exp_neg_mul_klBerReal_le_sum_Icc_choose_div_two_pow` [Ora, Lemma A.17] bounds this
probability below. The coins are averaged uniformly over the sign cube `Fin n → ℤˣ`, as in
`LMLExplore.OnlineLearning.LowerBound`.

## Main definitions

* `LMLExplore.OnlineLearning.wealth ε c x t`: the wealth after `t` rounds.

## Main statements

* `LMLExplore.OnlineLearning.wealth_eq_mul_prod`: the wealth of a bettor that bets fractions of
  its wealth.
* `LMLExplore.OnlineLearning.regret_neg_mul_eq_mul_sub_wealth`: online linear optimization on `ℝ`
  is betting.
* `LMLExplore.OnlineLearning.isGreatest_prod_one_add_mul`: the wealth of the best constant
  fraction.
* `LMLExplore.OnlineLearning.OnlineLearner.HasRegretBound.mul_norm_run_le`,
  `LMLExplore.OnlineLearning.OnlineLearner.HasRegretBound.exists_norm_le_run_eq_smul`: learners
  with a bounded regret against `0` bet fractions of their wealth.
* `LMLExplore.OnlineLearning.OnlineLearner.exists_wealth_run_le`,
  `LMLExplore.OnlineLearning.OnlineLearner.exists_wealth_run_le_of_even`: the upper bound on the
  wealth of bettors on biased sequences.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset Real InformationTheory
open scoped BigOperators

namespace LMLExplore.OnlineLearning

section Wealth

variable {ε : ℝ} {c x β : ℕ → ℝ} {n t : ℕ}

/-- The **wealth** after `t` rounds of the coin-betting game, from the initial wealth `ε`, the
coins `c` and the bets `x`: `ε + ∑ s < t, c s * x s`. -/
noncomputable def wealth (ε : ℝ) (c x : ℕ → ℝ) (t : ℕ) : ℝ :=
  ε + ∑ s ∈ range t, c s * x s

lemma wealth_def (ε : ℝ) (c x : ℕ → ℝ) (t : ℕ) :
    wealth ε c x t = ε + ∑ s ∈ range t, c s * x s := (rfl)

@[simp]
lemma wealth_zero (ε : ℝ) (c x : ℕ → ℝ) : wealth ε c x 0 = ε := by
  simp [wealth_def]

/-- Each round adds the gain `c t * x t` to the wealth. -/
lemma wealth_add_one (ε : ℝ) (c x : ℕ → ℝ) (t : ℕ) :
    wealth ε c x (t + 1) = wealth ε c x t + c t * x t := by
  rw [wealth_def, wealth_def, sum_range_succ, add_assoc]

/-- The wealth after `t` rounds depends only on the coins and the bets of the rounds `s < t`. -/
lemma wealth_congr {c' x' : ℕ → ℝ} (hc : ∀ s < t, c s = c' s) (hx : ∀ s < t, x s = x' s) :
    wealth ε c x t = wealth ε c' x' t := by
  rw [wealth_def, wealth_def]
  exact congrArg (ε + ·) (sum_congr rfl fun s hs ↦ by
    rw [hc s (mem_range.1 hs), hx s (mem_range.1 hs)])

/-- **The wealth of a bettor that bets fractions of its wealth**: if `x t = β t * wealth ε c x t`
for the rounds `t < n`, then `wealth ε c x n = ε * ∏ t < n, (1 + β t * c t)`. -/
theorem wealth_eq_mul_prod (hx : ∀ t < n, x t = β t * wealth ε c x t) :
    wealth ε c x n = ε * ∏ t ∈ range n, (1 + β t * c t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [wealth_add_one, hx n n.lt_succ_self, ih fun t ht ↦ hx t (ht.trans n.lt_succ_self),
      prod_range_succ]
    ring

/-- A bettor that bets fractions `β t ∈ [-1, 1]` of its wealth on coins `c t ∈ [-1, 1]` from a
nonnegative initial wealth never goes into debt. -/
theorem wealth_nonneg (hε : 0 ≤ ε) (hx : ∀ t < n, x t = β t * wealth ε c x t)
    (hβ : ∀ t < n, |β t| ≤ 1) (hc : ∀ t < n, |c t| ≤ 1) : 0 ≤ wealth ε c x n := by
  rw [wealth_eq_mul_prod hx]
  refine mul_nonneg hε (prod_nonneg fun t ht ↦ ?_)
  have ht := mem_range.1 ht
  have : |β t * c t| ≤ 1 := by
    rw [abs_mul]
    calc |β t| * |c t| ≤ 1 * 1 := mul_le_mul (hβ t ht) (hc t ht) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  linarith [neg_abs_le (β t * c t)]

/-- **One-dimensional online linear optimization is betting**: for the linear losses
`y ↦ -L * c t * y` on `ℝ`, the regret against `0` of the plays `x` is `L` times the loss
`ε - wealth ε c x n` of the bettor that bets `x`, for every initial wealth `ε`. -/
theorem regret_neg_mul_eq_mul_sub_wealth (L ε : ℝ) (c x : ℕ → ℝ) (n : ℕ) :
    regret (fun t y ↦ -L * c t * y) x 0 n = L * (ε - wealth ε c x n) := by
  have h (t : ℕ) : -L * c t * x t - -L * c t * 0 = -(L * (c t * x t)) := by ring
  simp_rw [regret_def, wealth_def, h]
  rw [sum_neg_distrib, ← mul_sum]
  ring

end Wealth

section ConstantFraction

variable {c : ℕ → ℝ} {n : ℕ}

/-- `a ^ j = exp (j log a)`, for `a > 0` or `j = 0`. -/
private lemma pow_eq_exp_mul_log {a : ℝ} {j : ℕ} (h : j = 0 ∨ 0 < a) :
    a ^ j = exp (j * log a) := by
  rcases h with rfl | ha
  · simp
  · rw [exp_nat_mul, exp_log ha]

/-- For a nonnegative `a`, positive unless `k = 0`, `k log a - k log (2 k / n) ≤ a n / 2 - k`,
from `log y ≤ y - 1` at `y = a n / (2 k)`. -/
private lemma mul_log_sub_mul_log_le {a k N : ℝ} (ha : 0 ≤ a) (hka : k = 0 ∨ 0 < a) (hk : 0 ≤ k)
    (hN : 0 < N) : k * log a - k * log (2 * k / N) ≤ a * N / 2 - k := by
  rcases hk.eq_or_lt with rfl | hk
  · simp only [zero_mul, sub_zero]
    positivity
  have ha := hka.resolve_left hk.ne'
  have h := log_le_sub_one_of_pos (by positivity : 0 < a * N / (2 * k))
  rw [log_div (by positivity) (by positivity), log_mul ha.ne' hN.ne'] at h
  rw [log_div (by positivity) hN.ne']
  have : k * (a * N / (2 * k) - 1) = a * N / 2 - k := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h hk.le]

/-- `(1 + β) ^ k (1 - β) ^ (n - k) ≤ exp (n d(k / n, 1 / 2))` for `β ∈ [-1, 1]`. -/
private lemma one_add_pow_mul_one_sub_pow_le {β : ℝ} (hβ : |β| ≤ 1) {k : ℕ} (hk : k ≤ n) :
    (1 + β) ^ k * (1 - β) ^ (n - k) ≤ exp (n * klBerReal (k / n) (1 / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp_all
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h₁ : 0 ≤ 1 + β := by linarith [neg_abs_le β]
  have h₂ : 0 ≤ 1 - β := by linarith [le_abs_self β]
  -- if a base with a positive exponent vanishes, the product vanishes
  by_cases h0 : (k ≠ 0 ∧ 1 + β = 0) ∨ (n - k ≠ 0 ∧ 1 - β = 0)
  · rcases h0 with ⟨hk0, h⟩ | ⟨hk0, h⟩
    · rw [h, zero_pow hk0, zero_mul]
      positivity
    · rw [h, zero_pow hk0, mul_zero]
      positivity
  -- otherwise both powers are exponentials, and the bound is `log y ≤ y - 1` twice
  have hk₁ : k = 0 ∨ 0 < 1 + β := by
    by_cases hk0 : k = 0
    · exact .inl hk0
    · exact .inr (lt_of_le_of_ne h₁ fun h ↦ h0 (.inl ⟨hk0, h.symm⟩))
  have hk₂ : n - k = 0 ∨ 0 < 1 - β := by
    by_cases hk0 : n - k = 0
    · exact .inl hk0
    · exact .inr (lt_of_le_of_ne h₂ fun h ↦ h0 (.inr ⟨hk0, h.symm⟩))
  rw [pow_eq_exp_mul_log hk₁, pow_eq_exp_mul_log hk₂, ← exp_add, exp_le_exp,
    mul_klBerReal_div_one_div_two hnR.ne', Nat.cast_sub hk]
  have e₁ := mul_log_sub_mul_log_le h₁ (hk₁.imp_left fun h ↦ by simp [h]) (Nat.cast_nonneg k) hnR
  have e₂ := mul_log_sub_mul_log_le h₂
    (hk₂.imp_left fun h ↦ by rw [← Nat.cast_sub hk, h, Nat.cast_zero]) (sub_nonneg.2 hkR) hnR
  linarith

/-- For coins in `{-1, 1}`, `∏ t < n, (1 + β * c t) = (1 + β) ^ k * (1 - β) ^ (n - k)` and
`∑ t < n, c t = 2 k - n`, where `k` is the number of heads `c t = 1`. -/
private lemma prod_one_add_mul_eq (hc : ∀ t < n, c t = 1 ∨ c t = -1) (β : ℝ) :
    ∏ t ∈ range n, (1 + β * c t) =
        (1 + β) ^ #{t ∈ range n | c t = 1} * (1 - β) ^ (n - #{t ∈ range n | c t = 1}) ∧
      ∑ t ∈ range n, c t = 2 * #{t ∈ range n | c t = 1} - n := by
  have hcard := card_filter_add_card_filter_not (s := range n) (fun t ↦ c t = 1)
  rw [card_range] at hcard
  have hneg : ∀ t ∈ {t ∈ range n | ¬c t = 1}, c t = -1 := fun t ht ↦ by
    rw [mem_filter, mem_range] at ht
    exact (hc t ht.1).resolve_left ht.2
  have hpos : ∀ t ∈ {t ∈ range n | c t = 1}, c t = 1 := fun t ht ↦ (mem_filter.1 ht).2
  have hsub : n - #{t ∈ range n | c t = 1} = #{t ∈ range n | ¬c t = 1} := by omega
  constructor
  · have e₁ : ∏ t ∈ {t ∈ range n | c t = 1}, (1 + β * c t) =
        (1 + β) ^ #{t ∈ range n | c t = 1} := by
      rw [prod_congr rfl fun t ht ↦ by rw [hpos t ht, mul_one], prod_const]
    have e₂ : ∏ t ∈ {t ∈ range n | ¬c t = 1}, (1 + β * c t) =
        (1 - β) ^ #{t ∈ range n | ¬c t = 1} := by
      rw [prod_congr rfl fun t ht ↦ by rw [hneg t ht, mul_neg_one, ← sub_eq_add_neg], prod_const]
    rw [← prod_filter_mul_prod_filter_not (range n) (fun t ↦ c t = 1), e₁, e₂, hsub]
  · have hcardR : (n : ℝ) = #{t ∈ range n | c t = 1} + #{t ∈ range n | ¬c t = 1} := by
      exact_mod_cast hcard.symm
    rw [← sum_filter_add_sum_filter_not (range n) (fun t ↦ c t = 1), sum_congr rfl hpos,
      sum_congr rfl hneg, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, hcardR]
    ring

/-- For coins in `{-1, 1}`, the fraction `(∑ t < n, c t) / n` is in `[-1, 1]`. -/
lemma abs_sum_div_le_one (hc : ∀ t < n, c t = 1 ∨ c t = -1) :
    |(∑ t ∈ range n, c t) / n| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [abs_div, Nat.abs_cast, div_le_one (by exact_mod_cast hn)]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  calc ∑ t ∈ range n, |c t| = ∑ t ∈ range n, (1 : ℝ) :=
        sum_congr rfl fun t ht ↦ by rcases hc t (mem_range.1 ht) with h | h <;> simp [h]
    _ = n := by simp

/-- The frequency of heads `k / n` is `1 / 2 + (∑ t < n, c t) / (2 n)`. -/
private lemma one_div_two_add_sum_div (hc : ∀ t < n, c t = 1 ∨ c t = -1) (hn : 0 < n) :
    1 / 2 + (∑ t ∈ range n, c t) / (2 * n) = #{t ∈ range n | c t = 1} / n := by
  have hnR : (n : ℝ) ≠ 0 := by positivity
  rw [(prod_one_add_mul_eq hc 0).2]
  field_simp
  ring

/-- **The wealth of a constant fraction is at most `exp (n d(1 / 2 + S / (2 n), 1 / 2))`**, where
`S = ∑ t < n, c t` [Ora, Remark 5.6]: for coins in `{-1, 1}` and every fraction `β ∈ [-1, 1]`,
`∏ t < n, (1 + β * c t) ≤ exp (n * d(1 / 2 + S / (2 n), 1 / 2))`. -/
theorem prod_one_add_mul_le_exp (hc : ∀ t < n, c t = 1 ∨ c t = -1) {β : ℝ} (hβ : |β| ≤ 1) :
    ∏ t ∈ range n, (1 + β * c t) ≤
      exp (n * klBerReal (1 / 2 + (∑ t ∈ range n, c t) / (2 * n)) (1 / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [one_div_two_add_sum_div hc hn, (prod_one_add_mul_eq hc β).1]
  exact one_add_pow_mul_one_sub_pow_le hβ (card_filter_le _ _ |>.trans_eq (card_range n))

/-- **The best constant fraction** [Ora, Remark 5.6]: for coins in `{-1, 1}`, the fraction
`β = S / n`, with `S = ∑ t < n, c t`, has `∏ t < n, (1 + β * c t) = exp (n d(1 / 2 + S / (2 n),
1 / 2))`. -/
theorem prod_one_add_sum_div_mul_eq_exp (hc : ∀ t < n, c t = 1 ∨ c t = -1) :
    ∏ t ∈ range n, (1 + (∑ s ∈ range n, c s) / n * c t) =
      exp (n * klBerReal (1 / 2 + (∑ t ∈ range n, c t) / (2 * n)) (1 / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hprod, hsum⟩ := prod_one_add_mul_eq hc ((∑ s ∈ range n, c s) / n)
  have hk : #{t ∈ range n | c t = 1} ≤ n := card_filter_le _ _ |>.trans_eq (card_range n)
  rw [one_div_two_add_sum_div hc hn, hprod, hsum, mul_klBerReal_div_one_div_two hnR.ne',
    exp_add]
  generalize #{t ∈ range n | c t = 1} = k at hk ⊢
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have e₁ : 1 + (2 * (k : ℝ) - n) / n = 2 * k / n := by field_simp; ring
  have e₂ : 1 - (2 * (k : ℝ) - n) / n = 2 * (n - k) / n := by field_simp; ring
  rw [e₁, e₂]
  have h₁ : (2 * k / n : ℝ) ^ k = exp (k * log (2 * k / n)) := by
    refine pow_eq_exp_mul_log ?_
    rcases Nat.eq_zero_or_pos k with h | h
    · exact .inl h
    · exact .inr (by positivity)
  have h₂ : (2 * (n - k) / n : ℝ) ^ (n - k) =
      exp (((n - k : ℕ) : ℝ) * log (2 * (n - k) / n)) := by
    refine pow_eq_exp_mul_log ?_
    rcases Nat.eq_zero_or_pos (n - k) with h | h
    · exact .inl h
    · have : (k : ℝ) < n := by exact_mod_cast Nat.lt_of_sub_pos h
      exact .inr (div_pos (by linarith) hnR)
  rw [h₁, h₂, Nat.cast_sub hk]

/-- **The wealth of the best constant fraction** [Ora, Remark 5.6]: for coins in `{-1, 1}`, with
`S = ∑ t < n, c t`, the largest value of `∏ t < n, (1 + β * c t)` over the fractions
`β ∈ [-1, 1]` is `exp (n d(1 / 2 + S / (2 n), 1 / 2))`, attained at `β = S / n`. The wealth of the
best constant fraction from the initial wealth `ε` is `ε` times this value. -/
theorem isGreatest_prod_one_add_mul (hc : ∀ t < n, c t = 1 ∨ c t = -1) :
    IsGreatest ((fun β ↦ ∏ t ∈ range n, (1 + β * c t)) '' Set.Icc (-1) 1)
      (exp (n * klBerReal (1 / 2 + (∑ t ∈ range n, c t) / (2 * n)) (1 / 2))) := by
  refine ⟨⟨(∑ s ∈ range n, c s) / n, abs_le.1 (abs_sum_div_le_one hc),
    prod_one_add_sum_div_mul_eq_exp hc⟩, ?_⟩
  rintro _ ⟨β, hβ, rfl⟩
  exact prod_one_add_mul_le_exp hc (abs_le.2 hβ)

end ConstantFraction

namespace OnlineLearner

section Fraction

variable {C E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : OnlineLearner C (E →L[ℝ] ℝ) E} {L : ℝ} {B : ℕ → ℝ}

/-- **A learner with a bounded regret against `0` bets a part of its wealth** [Ora, Theorem 5.7].
If the regret against `0` after `n` rounds of the learner `A` is at most `B n` for all linear
losses of dual norm at most `L`, then each play satisfies
`L * ‖x t‖ ≤ B (t + 1) - ∑ s < t, y s (x s)`: the loss `y t = L z`, for a functional `z` of norm
at most `1` with `z (x t) = ‖x t‖`, would otherwise break the bound after `t + 1` rounds. -/
theorem HasRegretBound.mul_norm_run_le
    (hA : A.HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) {0} fun n _ _ _ ↦ B n)
    (hL : 0 ≤ L) (c : ℕ → C) {y : ℕ → E →L[ℝ] ℝ} {t : ℕ} (hy : ∀ s < t, ‖y s‖ ≤ L) :
    L * ‖A.run c y t‖ ≤ B (t + 1) - ∑ s ∈ range t, y s (A.run c y s) := by
  classical
  obtain ⟨z, hz1, hz⟩ := exists_dual_vector'' ℝ (A.run c y t)
  replace hz : z (A.run c y t) = ‖A.run c y t‖ := hz
  set y' := Function.update y t (L • z)
  have hy't : y' t = L • z := Function.update_self _ _ _
  have hy's : ∀ s ≠ t, y' s = y s := fun s hs ↦ Function.update_of_ne hs _ _
  -- the plays of the rounds `s ≤ t` are the same against `y` and `y'`
  have hrun : ∀ s ≤ t, A.run c y' s = A.run c y s := fun s hs ↦
    A.run_congr_feedback c fun r hr ↦ hy's r (by omega)
  have hadm : ∀ s < t + 1, ‖y' s‖ ≤ L := fun s hs ↦ by
    rcases (Nat.lt_succ_iff.1 hs).eq_or_lt with rfl | hs
    · rw [hy't, norm_smul, Real.norm_of_nonneg hL]
      exact mul_le_of_le_one_right hL hz1
    · rw [hy's s hs.ne]
      exact hy s hs
  have h := hA.regret_le (c := c) (g := y') hadm (Set.mem_singleton 0)
  rw [regret_def, sum_range_succ, hrun t le_rfl, hy't] at h
  rw [sum_congr rfl fun s hs ↦ by
    rw [hrun s (mem_range.1 hs).le, hy's s (mem_range.1 hs).ne]] at h
  simp only [map_zero, sub_zero, FunLike.coe_smul, Pi.smul_apply, hz, smul_eq_mul] at h
  linarith

/-- **A learner with a bounded regret against `0` bets fractions of its wealth**
[Ora, Theorem 5.7]. If the regret against `0` after `n` rounds of the learner `A` is at most
`B n` for all linear losses of dual norm at most `L > 0`, then against such losses each play `x t`
with `B (t + 1) ≤ B n` is a vector fraction `β` with `‖β‖ ≤ 1 / L` of the wealth
`B n - ∑ s < t, y s (x s)`. For `B` nondecreasing, as in [Ora], this holds for all `t < n`. -/
theorem HasRegretBound.exists_norm_le_run_eq_smul
    (hA : A.HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) {0} fun n _ _ _ ↦ B n)
    (hL : 0 < L) (c : ℕ → C) {y : ℕ → E →L[ℝ] ℝ} {n t : ℕ} (hB : B (t + 1) ≤ B n)
    (hy : ∀ s < t, ‖y s‖ ≤ L) :
    ∃ β : E, ‖β‖ ≤ 1 / L ∧
      A.run c y t = (B n - ∑ s ∈ range t, y s (A.run c y s)) • β := by
  set W := B n - ∑ s ∈ range t, y s (A.run c y s)
  have hW : L * ‖A.run c y t‖ ≤ W :=
    (hA.mul_norm_run_le hL.le c hy).trans (by simp only [W]; linarith)
  rcases (mul_nonneg hL.le (norm_nonneg _) |>.trans hW).eq_or_lt with h0 | hpos
  · refine ⟨0, by simp [hL.le], ?_⟩
    rw [smul_zero, ← norm_eq_zero]
    nlinarith [norm_nonneg (A.run c y t)]
  · refine ⟨W⁻¹ • A.run c y t, ?_, by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]⟩
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos, mul_one_div,
      le_div_iff₀ hL]
    linarith

end Fraction

section Bettor

variable {C : Type*}

/-- The coins `σ t` of the rounds `t < n` for the signs `σ`, and `0` after. -/
private noncomputable def signCoins {n : ℕ} (σ : Fin n → ℤˣ) (t : ℕ) : ℝ :=
  if h : t < n then ((σ ⟨t, h⟩ : ℤ) : ℝ) else 0

private lemma signCoins_mem {n : ℕ} (σ : Fin n → ℤˣ) {t : ℕ} (ht : t < n) :
    signCoins σ t = 1 ∨ signCoins σ t = -1 := by
  simp only [signCoins, ht, ↓reduceDIte]
  rcases Int.units_eq_one_or (σ ⟨t, ht⟩) with h | h <;> simp [h]

private lemma sum_signCoins {n : ℕ} (σ : Fin n → ℤˣ) :
    ∑ t ∈ range n, signCoins σ t = ∑ t, ((σ t : ℤ) : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun t _ ↦ by simp [signCoins]

/-- **No bettor gets rich on all biased sequences** [Ora, Theorem 5.5]. Let `n / 2 < k ≤ n`. For
every bettor `A` whose wealth from `ε` after `n` rounds is nonnegative on all sequences of coins
in `{-1, 1}`, there is such a sequence with `|∑ t < n, c t| ≥ 2 k - n` on which its wealth is
at most `3 ε / 2 * ((2 k - n) / √n + 1) * exp (n * d(k / n, 1 / 2))`, where `d` is the binary
relative entropy. -/
theorem exists_wealth_run_le (A : OnlineLearner C ℝ ℝ) (c : ℕ → C) {ε : ℝ} {n k : ℕ}
    (hnk : n < 2 * k) (hk : k ≤ n)
    (hA : ∀ g : ℕ → ℝ, (∀ t < n, g t = 1 ∨ g t = -1) → 0 ≤ wealth ε g (A.run c g) n) :
    ∃ g : ℕ → ℝ, (∀ t < n, g t = 1 ∨ g t = -1) ∧ 2 * k - n ≤ |∑ t ∈ range n, g t| ∧
      wealth ε g (A.run c g) n ≤
        3 * ε / 2 * ((2 * k - n) / √n + 1) * exp (n * klBerReal (k / n) (1 / 2)) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < 2 * k - n := by
    have : (n : ℝ) < 2 * k := by exact_mod_cast hnk
    linarith
  -- the wealth on the coins of the signs `σ`
  set W : (Fin n → ℤˣ) → ℝ := fun σ ↦ wealth ε (signCoins σ) (A.run c (signCoins σ)) n
  have hW0 (σ : Fin n → ℤˣ) : 0 ≤ W σ := hA _ fun t ht ↦ signCoins_mem σ ht
  -- the bets are predictable, so the wealth has mean `ε`
  have hmean : ∑ σ, W σ = 2 ^ n * ε := by
    have hpred : 𝔼 σ : Fin n → ℤˣ, ∑ t, ((σ t : ℤ) : ℝ) * A.run c (signCoins σ) t = 0 :=
      expect_sum_units_apply_mul_eq_zero fun σ σ' t h ↦ by
        refine A.run_congr_feedback c fun s hs ↦ ?_
        have hsn : s < n := hs.trans t.isLt
        simp only [signCoins, hsn, ↓reduceDIte]
        rw [h ⟨s, hsn⟩ (Fin.lt_def.2 hs)]
    have hW (σ : Fin n → ℤˣ) :
        W σ = ε + ∑ t, ((σ t : ℤ) : ℝ) * A.run c (signCoins σ) t := by
      simp only [W, wealth_def, ← Fin.sum_univ_eq_sum_range]
      exact congrArg (ε + ·) (sum_congr rfl fun t _ ↦ by simp [signCoins])
    rw [Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at hpred
    simp only [hW, sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_units_int,
      Fintype.card_fin, nsmul_eq_mul]
    rcases hpred with h | h
    · rw [h]
      push_cast
      ring
    · simp at h
  -- in particular the initial wealth is nonnegative
  have hε : 0 ≤ ε := by
    have h := sum_nonneg fun σ (_ : σ ∈ univ) ↦ hW0 σ
    rw [hmean] at h
    exact nonneg_of_mul_nonneg_right h (by positivity : (0 : ℝ) < 2 ^ n)
  -- the event `|∑ t, σ t| ≥ 2 k - n` and its size
  set G := univ.filter fun σ : Fin n → ℤˣ ↦ (2 * k - n : ℝ) ≤ |∑ t, ((σ t : ℤ) : ℝ)|
  set T := ∑ i ∈ Icc k n, (n.choose i : ℝ)
  have hG : (#G : ℝ) = 2 * T := by
    have h := card_filter_le_abs_sum_units (ι := Fin n) hd
    have h₂ := card_filter_le_sum_units (ι := Fin n) k
    rw [Fintype.card_fin] at h₂
    rw [h₂] at h
    simp only [G, T] at h ⊢
    rw [h]
    push_cast
    ring
  have htail := Nat.exp_neg_mul_klBerReal_le_sum_Icc_choose_div_two_pow hnk.le hk
  have hT : 0 < T := by
    refine lt_of_lt_of_le ?_ ((le_div_iff₀ (by positivity)).1 htail)
    positivity
  have hGne : G.Nonempty := by
    rw [← card_pos]
    exact_mod_cast (by rw [hG]; positivity : (0 : ℝ) < #G)
  -- some sign sequence of the event has wealth at most `2 ^ n ε / #G`
  have hsum : ∑ σ ∈ G, W σ ≤ ∑ σ ∈ G, 2 ^ n * ε / #G := by
    rw [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (by rw [hG]; positivity), ← hmean]
    exact sum_le_univ_sum_of_nonneg hW0
  obtain ⟨σ, hσG, hσ⟩ := exists_le_of_sum_le hGne hsum
  refine ⟨signCoins σ, fun t ht ↦ signCoins_mem σ ht, ?_, hσ.trans ?_⟩
  · rw [sum_signCoins]
    exact (mem_filter.1 hσG).2
  -- `2 ^ n ε / (2 T) ≤ 3 ε / 2 * ((2 k - n) / √n + 1) * exp (n d(k / n, 1 / 2))` by the tail bound
  rw [hG]
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 hnR
  have hfac : (2 * k - n) / √n + 1 = (2 * k - n + √n) / √n := by field_simp
  rw [hfac, div_le_iff₀ (by positivity)]
  rw [le_div_iff₀ (by positivity), exp_neg] at htail
  have hE := exp_pos (n * klBerReal (k / n) (1 / 2))
  set E := exp (n * klBerReal (k / n) (1 / 2))
  have key : 2 ^ n * √(n : ℝ) ≤ 3 * (2 * k - n + √n) * E * T := by
    have h := htail
    field_simp at h
    nlinarith
  calc 2 ^ n * ε = ε * 2 ^ n := mul_comm _ _
    _ ≤ ε * (3 * (2 * k - n + √n) * E * T / √n) := by
        gcongr
        rw [le_div_iff₀ hsq]
        exact key
    _ = 3 * ε / 2 * ((2 * k - n + √n) / √n) * E * (2 * T) := by
        field_simp

/-- **No bettor gets rich on all biased sequences**, in the form of [Ora, Theorem 5.5]: for `n`
even and an integer `0 < q ≤ n / 2`, every bettor `A` whose wealth from `ε` after `n` rounds is
nonnegative on all sequences of coins in `{-1, 1}` has, on some such sequence with
`|∑ t < n, c t| ≥ 2 q`, wealth at most
`3 ε / 2 * (2 q / √n + 1) * exp (n * d(1 / 2 + q / n, 1 / 2))`. -/
theorem exists_wealth_run_le_of_even (A : OnlineLearner C ℝ ℝ) (c : ℕ → C) {ε : ℝ} {n q : ℕ}
    (hn : Even n) (hq : 0 < q) (hqn : q ≤ n / 2)
    (hA : ∀ g : ℕ → ℝ, (∀ t < n, g t = 1 ∨ g t = -1) → 0 ≤ wealth ε g (A.run c g) n) :
    ∃ g : ℕ → ℝ, (∀ t < n, g t = 1 ∨ g t = -1) ∧ 2 * q ≤ |∑ t ∈ range n, g t| ∧
      wealth ε g (A.run c g) n ≤
        3 * ε / 2 * (2 * q / √n + 1) * exp (n * klBerReal (1 / 2 + q / n) (1 / 2)) := by
  obtain ⟨m, rfl⟩ := hn
  have hqm : q ≤ m := by omega
  obtain ⟨g, hg, hsum, hW⟩ := A.exists_wealth_run_le c (k := m + q) (by omega) (by omega) hA
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := by omega
    positivity
  have h₁ : (2 * ((m + q : ℕ) : ℝ) - ((m + m : ℕ) : ℝ)) = 2 * q := by push_cast; ring
  have h₂ : ((m + q : ℕ) : ℝ) / ((m + m : ℕ) : ℝ) = 1 / 2 + q / ((m + m : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [h₁] at hsum hW
  rw [h₂] at hW
  exact ⟨g, hg, hsum, hW⟩

end Bettor

end OnlineLearner

end LMLExplore.OnlineLearning
