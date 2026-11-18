/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.Learner.Operations
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Statlib.ForMathlib.InformationTheory.KullbackLeibler.Bernoulli
import LMLExplore.Analysis.Normed.Group.Basic
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
  For general comparators `u`, the regret on the losses `y ↦ g t * y` is expressed through the
  wealth of the bets on the coins `-g t / L` (`regret_mul_eq_mul_sub_wealth_add_mul`).
* **Bettors with a fraction rule.** A rule `frac t c` depending only on the past coins defines the
  bettor `OnlineLearner.fractionBettor frac ε`, which bets the fraction `frac t c` of its wealth
  (`OnlineLearner.run_fractionBettor`), and its reduction `OnlineLearner.fractionBettorOCO` to
  one-dimensional online linear optimization. The Krichevsky–Trofimov bettor and the
  constant-fraction bettor are such bettors.
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
* `LMLExplore.OnlineLearning.OnlineLearner.fractionBettor frac ε`,
  `LMLExplore.OnlineLearning.OnlineLearner.fractionBettorOCO frac L ε`: the bettor with the
  fraction rule `frac`, and its reduction to one-dimensional online linear optimization.

## Main statements

* `LMLExplore.OnlineLearning.wealth_eq_mul_prod`: the wealth of a bettor that bets fractions of
  its wealth.
* `LMLExplore.OnlineLearning.regret_neg_mul_eq_mul_sub_wealth`,
  `LMLExplore.OnlineLearning.regret_mul_eq_mul_sub_wealth_add_mul`: online linear optimization on
  `ℝ` is betting.
* `LMLExplore.OnlineLearning.OnlineLearner.run_fractionBettor`,
  `LMLExplore.OnlineLearning.OnlineLearner.run_fractionBettorOCO_eq_mul_wealth`: the bets of the
  bettor with a fraction rule.
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

/-- **One-dimensional online linear optimization is betting**, against every comparator: for
`L ≠ 0`, the regret against `u` of the plays `x` on the linear losses `y ↦ g t * y` is
`L * (ε - W) + L * (S * u)`, where `W` is the wealth of the bets `x` on the coins `-g t / L` from
the initial wealth `ε` and `S` is the sum of these coins. -/
theorem regret_mul_eq_mul_sub_wealth_add_mul (ε : ℝ) {L : ℝ} (hL : L ≠ 0) (g x : ℕ → ℝ) (u : ℝ)
    (n : ℕ) :
    regret (fun t y ↦ g t * y) x u n =
      L * (ε - wealth ε (fun s ↦ -g s / L) x n) + L * ((∑ t ∈ range n, -g t / L) * u) := by
  have hℓ : (fun t y ↦ g t * y) = fun t y ↦ -L * (-g t / L) * y := by
    funext t y
    field_simp
  have hu : ∑ t ∈ range n, -L * (-g t / L) * u = -(L * ((∑ t ∈ range n, -g t / L) * u)) := by
    rw [sum_mul, mul_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun t _ ↦ by ring
  rw [hℓ, ← regret_neg_mul_eq_mul_sub_wealth L ε (fun s ↦ -g s / L) x n, regret_eq_sum_sub_sum,
    regret_eq_sum_sub_sum, hu]
  simp

/-- A loss `g` with `|g| ≤ L` gives the coin `-g / L ∈ [-1, 1]`. -/
lemma abs_neg_div_le_one {g L : ℝ} (hL : 0 < L) (hg : |g| ≤ L) : |-g / L| ≤ 1 := by
  rw [abs_div, abs_neg, abs_of_pos hL, div_le_one hL]
  exact hg

/-- Coins in `[-1, 1]` sum to at most the number of rounds in absolute value. -/
lemma abs_sum_le_of_abs_le_one (hc : ∀ s < t, |c s| ≤ 1) : |∑ s ∈ range t, c s| ≤ t := by
  simpa using norm_sum_le_card_mul (range t) (L := 1) fun s hs ↦
    (norm_eq_abs (c s)).trans_le (hc s (mem_range.1 hs))

end Wealth

section ConstantFraction

variable {c : ℕ → ℝ} {n : ℕ}

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
  · rw [sum_eq_two_mul_card_filter_sub_card fun t ht ↦ hc t (mem_range.1 ht), card_range]

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
  exact one_add_pow_mul_one_sub_pow_le_exp_mul_klBerReal
    (Nat.add_sub_cancel' (card_filter_le _ _ |>.trans_eq (card_range n))) hβ

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
  rw [one_div_two_add_sum_div hc hn, hprod, hsum,
    exp_mul_klBerReal_div_one_div_two (Nat.add_sub_cancel' hk)]
  generalize #{t ∈ range n | c t = 1} = k at hk ⊢
  have e₁ : 1 + (2 * (k : ℝ) - n) / n = 2 * (k / n) := by field_simp; ring
  have e₂ : 1 - (2 * (k : ℝ) - n) / n = 2 * (((n - k : ℕ) : ℝ) / n) := by
    rw [Nat.cast_sub hk]
    field_simp
    ring
  have e₃ : (2 : ℝ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [e₁, e₂, mul_pow, mul_pow, e₃]
  ring

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
  rw [RCLike.ofReal_real_eq_id, id_eq] at hz
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

/-- The bets are predictable, so the wealth on the coins of the signs `σ` has mean `ε`: its sum over
the sign cube is `2 ^ n ε`. -/
private lemma sum_wealth_signCoins (A : OnlineLearner C ℝ ℝ) (c : ℕ → C) (ε : ℝ) (n : ℕ) :
    ∑ σ : Fin n → ℤˣ, wealth ε (signCoins σ) (A.run c (signCoins σ)) n = 2 ^ n * ε := by
  have hpred : 𝔼 σ : Fin n → ℤˣ, ∑ t, ((σ t : ℤ) : ℝ) * A.run c (signCoins σ) t = 0 :=
    expect_sum_units_apply_mul_eq_zero fun σ σ' t h ↦ by
      refine A.run_congr_feedback c fun s hs ↦ ?_
      have hsn : s < n := hs.trans t.isLt
      simp only [signCoins, hsn, ↓reduceDIte]
      rw [h ⟨s, hsn⟩ (Fin.lt_def.2 hs)]
  have hW (σ : Fin n → ℤˣ) : wealth ε (signCoins σ) (A.run c (signCoins σ)) n =
      ε + ∑ t, ((σ t : ℤ) : ℝ) * A.run c (signCoins σ) t := by
    simp only [wealth_def, ← Fin.sum_univ_eq_sum_range]
    exact congrArg (ε + ·) (sum_congr rfl fun t _ ↦ by simp [signCoins])
  rw [Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at hpred
  simp only [hW, sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_units_int,
    Fintype.card_fin, nsmul_eq_mul]
  rcases hpred with h | h
  · rw [h]
    push_cast
    ring
  · simp at h

/-- For `2 k - n > 0`, the signs `σ : Fin n → ℤˣ` with `|∑ t, σ t| ≥ 2 k - n` are
`2 ∑ i ∈ Icc k n, n.choose i`. -/
private lemma card_filter_le_abs_sum_eq_two_mul_sum_choose {n k : ℕ} (hd : (0 : ℝ) < 2 * k - n) :
    (#{σ : Fin n → ℤˣ | (2 * k - n : ℝ) ≤ |∑ t, ((σ t : ℤ) : ℝ)|} : ℝ) =
      2 * ∑ i ∈ Icc k n, (n.choose i : ℝ) := by
  have h := card_filter_le_abs_sum_units_eq_two_mul (ι := Fin n) hd
  have h₂ := card_filter_le_sum_units_eq_sum_Icc_choose (ι := Fin n) k
  rw [Fintype.card_fin] at h₂
  rw [h₂] at h
  rw [h]
  push_cast
  ring

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
  have hmean : ∑ σ, W σ = 2 ^ n * ε := sum_wealth_signCoins A c ε n
  -- in particular the initial wealth is nonnegative
  have hε : 0 ≤ ε := by
    have h := sum_nonneg fun σ (_ : σ ∈ univ) ↦ hW0 σ
    rw [hmean] at h
    exact nonneg_of_mul_nonneg_right h (by positivity : (0 : ℝ) < 2 ^ n)
  -- the event `|∑ t, σ t| ≥ 2 k - n` and its size
  set G := univ.filter fun σ : Fin n → ℤˣ ↦ (2 * k - n : ℝ) ≤ |∑ t, ((σ t : ℤ) : ℝ)|
  set T := ∑ i ∈ Icc k n, (n.choose i : ℝ)
  have hG : (#G : ℝ) = 2 * T := card_filter_le_abs_sum_eq_two_mul_sum_choose hd
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

section FractionBettor

variable {C : Type*} {frac : ℕ → (ℕ → ℝ) → ℝ}

/-- A fraction rule `t c ↦ f t (∑ s < t, c s)` of the past sums of the coins depends only on the
past coins. -/
lemma apply_sum_range_congr (f : ℕ → ℝ → ℝ) {t : ℕ} {c c' : ℕ → ℝ} (h : ∀ s < t, c s = c' s) :
    f t (∑ s ∈ range t, c s) = f t (∑ s ∈ range t, c' s) := by
  rw [sum_congr rfl fun s hs ↦ h s (mem_range.1 hs)]

/-- The bet at round `t` of the bettor with the fraction rule `frac` on the coins `c`, from the
initial wealth `ε`: the fraction `frac t c` of the wealth `ε ∏ s < t, (1 + frac s c * c s)`. -/
private noncomputable def fractionBet (frac : ℕ → (ℕ → ℝ) → ℝ) (ε : ℝ) (c : ℕ → ℝ) (t : ℕ) : ℝ :=
  frac t c * (ε * ∏ s ∈ range t, (1 + frac s c * c s))

/-- If the fraction rule depends only on the past coins, the bet of round `t` depends only on the
coins of the rounds `s < t`. -/
private lemma fractionBet_congr
    (hfrac : ∀ t (c c' : ℕ → ℝ), (∀ s < t, c s = c' s) → frac t c = frac t c') {ε : ℝ}
    {c c' : ℕ → ℝ} {t : ℕ} (h : ∀ s < t, c s = c' s) :
    fractionBet frac ε c t = fractionBet frac ε c' t := by
  have hf {s : ℕ} (hs : s ≤ t) : frac s c = frac s c' :=
    hfrac s c c' fun r hr ↦ h r (hr.trans_le hs)
  rw [fractionBet, fractionBet, hf le_rfl]
  congr 2
  exact prod_congr rfl fun s hs ↦ by
    rw [hf (mem_range.1 hs).le, h s (mem_range.1 hs)]

/-- The **bettor with the fraction rule `frac`** from the initial wealth `ε`: a bettor whose
feedback is the coins, and which bets at round `t` the fraction `frac t c` of its wealth, for a
rule `frac` that depends only on the past coins `c s`, `s < t` (`run_fractionBettor`). The
Krichevsky–Trofimov bettor and the constant-fraction bettor are such bettors. -/
noncomputable def fractionBettor (frac : ℕ → (ℕ → ℝ) → ℝ) (ε : ℝ) : OnlineLearner C ℝ ℝ where
  play t h _ := fractionBet frac ε (fun s ↦ if hs : s < t then (h ⟨s, hs⟩).2 else 0) t

/-- **The bets of the bettor with the fraction rule `frac`**: if `frac t c` depends only on the
past coins, then at round `t` it bets the fraction `frac t c` of its wealth on the coins `c`. -/
theorem run_fractionBettor
    (hfrac : ∀ t (c c' : ℕ → ℝ), (∀ s < t, c s = c' s) → frac t c = frac t c') (ε : ℝ)
    (d : ℕ → C) (c : ℕ → ℝ) (t : ℕ) :
    (fractionBettor frac ε).run d c t =
      frac t c * wealth ε c ((fractionBettor frac ε).run d c) t := by
  have hbet (t : ℕ) : (fractionBettor frac ε).run d c t = fractionBet frac ε c t := by
    rw [run_def]
    exact fractionBet_congr hfrac fun s hs ↦ by simp [hs]
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [wealth_eq_mul_prod (β := fun s ↦ frac s c) fun s hs ↦ ih s hs, hbet, fractionBet]

/-- The **bettor with the fraction rule `frac` for one-dimensional online linear optimization**
with losses bounded by `L`, from the initial wealth `ε`: on the linear losses `g t`, it plays the
bets of `fractionBettor frac ε` on the coins `-g t / L` (`run_fractionBettorOCO`). -/
noncomputable def fractionBettorOCO (frac : ℕ → (ℕ → ℝ) → ℝ) (L ε : ℝ) : OnlineLearner C ℝ ℝ :=
  (fractionBettor frac ε).reduce id fun _ g ↦ -g / L

/-- The plays of the bettor for online linear optimization are the bets of the bettor on the coins
`-g t / L`. -/
theorem run_fractionBettorOCO (frac : ℕ → (ℕ → ℝ) → ℝ) (L ε : ℝ) (d : ℕ → C) (g : ℕ → ℝ)
    (t : ℕ) :
    (fractionBettorOCO frac L ε).run d g t =
      (fractionBettor frac ε).run d (fun s ↦ -g s / L) t := by
  rw [fractionBettorOCO, run_reduce,
    ← (fractionBettor frac ε).closedLoopFeedback_unique (g := fun s ↦ -g s / L) fun _ ↦ rfl]
  rfl

/-- If `frac t c` depends only on the past coins, the plays of the bettor for online linear
optimization bet the fraction `frac t c` of the wealth on the coins `c t = -g t / L`. -/
theorem run_fractionBettorOCO_eq_mul_wealth
    (hfrac : ∀ t (c c' : ℕ → ℝ), (∀ s < t, c s = c' s) → frac t c = frac t c') (L ε : ℝ)
    (d : ℕ → C) (g : ℕ → ℝ) (t : ℕ) :
    (fractionBettorOCO frac L ε).run d g t =
      frac t (fun s ↦ -g s / L) *
        wealth ε (fun s ↦ -g s / L) ((fractionBettorOCO frac L ε).run d g) t := by
  rw [funext (run_fractionBettorOCO frac L ε d g)]
  exact run_fractionBettor hfrac ε d _ t

end FractionBettor

end OnlineLearner

end LMLExplore.OnlineLearning
