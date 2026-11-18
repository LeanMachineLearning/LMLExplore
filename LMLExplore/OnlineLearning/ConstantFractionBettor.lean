/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.CoinBetting
public import LMLExplore.OnlineLearning.Learner.Operations
import LMLExplore.Analysis.Convex.Conjugate.ExpSq
import LMLExplore.Analysis.Normed.Group.Basic
import LMLExplore.Analysis.SpecialFunctions.Log.Basic
import LMLExplore.OnlineLearning.FTRL.Stability
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The constant-fraction bettor

The **constant-fraction bettor** [Ora, §13.7] plays the coin-betting game of
`LMLExplore.OnlineLearning.CoinBetting` by betting at round `t` the fraction
`β t = (∑ s < t, c s) / (2 (t + a))` of its current wealth, for a parameter `a > 0`. These
fractions are the plays of follow the regularized leader on `[-1 / 2, 1 / 2]` with the
regularizers `(t + a) β ^ 2` on the losses `β ↦ -c s * β` (`isMinOn_mul_sq_add_sum_iff`).

Unlike the Krichevsky–Trofimov bettor, whose guaranteed wealth contains the factor `1 / √n`, this
bettor loses at most a constant fraction of its initial wealth when the parameter `a` is
proportional to the horizon `n`. Since `log (1 + x) ≥ x - x ^ 2` for `|x| ≤ 1 / 2`, its log-wealth
is at least the reward of the fractions on the linear losses minus `∑ t < n, β t ^ 2`, and the FTRL
bound, which keeps the increments `-β (t + 1) ^ 2` of the regularizers, cancels this sum. This
gives the wealth bound [Ora, §13.7]
`ε exp ((∑ t < n, c t) ^ 2 / (4 (n + a)) - n / (4 a)) ≤ wealth after n rounds`
for coins in `[-1, 1]` (`mul_exp_sq_div_sub_div_le_wealth`). Through the regret–reward duality
[Ora, Theorem 13.5] and the conjugate bound `Real.mul_sub_mul_exp_sq_div_le` [Ora, Lemma 13.6],
the bettor on the coins `-g t / L` is an algorithm for one-dimensional online linear
optimization with losses `|g t| ≤ L` whose regret against every `u ∈ ℝ` is at most
`|u| L √(2 (n + a) log (1 + 2 (n + a) exp (n / (2 a)) u ^ 2 / ε ^ 2)) + ε L`
(`constantFractionBettor_regret_le`). With `a = n / 4` this is the bound
`|u| L √(5 n log (|u| √(19 n) / ε + 1)) + ε L` of [Ora, (13.10)]
(`constantFractionBettor_regret_le_of_horizon`), with `√n` in place of the factor `n` of the
Krichevsky–Trofimov algorithm inside the logarithm.

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner.constantFractionBettor a ε`: the constant-fraction
  bettor with parameter `a`, from the initial wealth `ε`.
* `LMLExplore.OnlineLearning.OnlineLearner.constantFractionBettorOCO L a ε`: the constant-fraction
  bettor for one-dimensional online linear optimization with losses bounded by `L`.

## Main statements

* `isMinOn_mul_sq_add_sum_iff`: the fractions are the FTRL plays.
* `regret_neg_mul_le_mul_sq_add_sum_sub_sum`: [Ora, Corollary 7.6] for these FTRL plays, keeping
  the increments of the regularizers.
* `mul_exp_sq_div_sub_sum_le_wealth`, `mul_exp_sq_div_sub_div_le_wealth`: the wealth bounds
  [Ora, §13.7].
* `constantFractionBettor_regret_le`, `constantFractionBettor_regret_le_of_horizon`: the regret
  bounds of one-dimensional online linear optimization [Ora, (13.10)].
* `OnlineLearner.hasRegretBound_constantFractionBettorOCO`,
  `OnlineLearner.regret_run_constantFractionBettorOCO_le`: the same for the learner.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, §13.7.
-/

public section

open Finset Real

namespace LMLExplore.OnlineLearning

section FTRL

variable {a : ℝ} {c : ℕ → ℝ} {t n : ℕ}

/-- Coins in `[-1, 1]` sum to at most the number of rounds in absolute value. -/
private lemma abs_sum_le (hc : ∀ s < t, |c s| ≤ 1) : |∑ s ∈ range t, c s| ≤ t := by
  simpa using norm_sum_le_card_mul (range t) (L := 1) fun s hs ↦
    (norm_eq_abs (c s)).trans_le (hc s (mem_range.1 hs))

/-- The fraction `(∑ s < t, c s) / (2 (t + a))` of coins in `[-1, 1]` lies in `[-1 / 2, 1 / 2]`
for `a > 0`. -/
private lemma abs_sum_div_le (ha : 0 < a) (hc : ∀ s < t, |c s| ≤ 1) :
    |(∑ s ∈ range t, c s) / (2 * (t + a))| ≤ 1 / 2 := by
  have hta : 0 < 2 * ((t : ℝ) + a) := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  rw [abs_div, abs_of_pos hta, div_le_iff₀ hta]
  linarith [abs_sum_le hc]

/-- **The fractions of the constant-fraction bettor are FTRL plays** [Ora, §13.7]: for `a > 0` and
coins `c s ∈ [-1, 1]`, the minimizer over `[-1 / 2, 1 / 2]` of the FTRL objective
`(t + a) β ^ 2 + ∑ s < t, -c s * β` of the regularizer `(t + a) β ^ 2` and the linear losses
`β ↦ -c s * β` is the fraction `(∑ s < t, c s) / (2 (t + a))`. -/
theorem isMinOn_mul_sq_add_sum_iff (ha : 0 < a) (hc : ∀ s < t, |c s| ≤ 1) {b : ℝ} :
    IsMinOn (fun β ↦ (t + a) * β ^ 2 + ∑ s ∈ range t, -c s * β) (Set.Icc (-(1 / 2)) (1 / 2)) b ↔
      b = (∑ s ∈ range t, c s) / (2 * (t + a)) := by
  set β₀ := (∑ s ∈ range t, c s) / (2 * (t + a)) with hβ₀
  have hta : 0 < (t : ℝ) + a := by linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  -- the objective is `(t + a) (β - β₀) ^ 2 - (t + a) β₀ ^ 2`
  have hf (β : ℝ) : (t + a) * β ^ 2 + ∑ s ∈ range t, -c s * β =
      (t + a) * (β - β₀) ^ 2 - (t + a) * β₀ ^ 2 := by
    rw [← sum_mul, sum_neg_distrib, hβ₀]
    field_simp
    ring
  have hmem : β₀ ∈ Set.Icc (-(1 / 2)) (1 / 2) := abs_le.1 (abs_sum_div_le ha hc)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := h hmem
    simp only [Set.mem_ofPred_eq, hf, sub_self] at h'
    have hsq : (b - β₀) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)
  · intro β _
    simp only [Set.mem_ofPred_eq, hf, h, sub_self]
    nlinarith [sq_nonneg (β - β₀)]

/-- **The regret of the FTRL plays of the constant-fraction bettor** [Ora, Corollary 7.6, §13.7]:
for `a > 0`, coins `c t ∈ [-1, 1]` and the fractions `β t = (∑ s < t, c s) / (2 (t + a))` for
`t ≤ n`, the regret on the linear losses `β ↦ -c t * β` against every `u ∈ [-1 / 2, 1 / 2]` is at
most `(n + a) u ^ 2 + ∑ t < n, c t ^ 2 / (4 (t + a)) - ∑ t < n, β (t + 1) ^ 2`. The last sum comes
from the increments `(t + a) β ^ 2 - (t + 1 + a) β ^ 2` of the regularizers at the next plays. -/
theorem regret_neg_mul_le_mul_sq_add_sum_sub_sum (ha : 0 < a) (hc : ∀ t < n, |c t| ≤ 1)
    {β : ℕ → ℝ} (hβ : ∀ t ≤ n, β t = (∑ s ∈ range t, c s) / (2 * (t + a))) {u : ℝ}
    (hu : u ∈ Set.Icc (-(1 / 2)) (1 / 2)) :
    regret (fun t b ↦ -c t * b) β u n ≤
      (n + a) * u ^ 2 + ∑ t ∈ range n, c t ^ 2 / (4 * (t + a)) - ∑ t ∈ range n, β (t + 1) ^ 2 := by
  set V : Set ℝ := Set.Icc (-(1 / 2)) (1 / 2)
  have hmin (t : ℕ) (ht : t ≤ n) :
      IsMinOn (fun b ↦ (t + a) * b ^ 2 + ∑ s ∈ range t, -c s * b) V (β t) :=
    (isMinOn_mul_sq_add_sum_iff ha fun s hs ↦ hc s (by omega)).2 (hβ t ht)
  have hβV (t : ℕ) (ht : t ≤ n) : β t ∈ V := by
    rw [hβ t ht]
    exact abs_le.1 (abs_sum_div_le ha fun s hs ↦ hc s (by omega))
  -- the objective plus the loss of the round is `2 (t + a)`-strongly convex
  have hconv (t : ℕ) : StrongConvexOn V (2 * (t + a))
      fun b ↦ (t + a) * b ^ 2 + ∑ s ∈ range (t + 1), -c s * b := by
    refine strongConvexOn_iff_convex.2 ?_
    have hlin : (fun b : ℝ ↦ (t + a) * b ^ 2 + ∑ s ∈ range (t + 1), -c s * b -
        2 * (t + a) / 2 * ‖b‖ ^ 2) = LinearMap.mul ℝ ℝ (∑ s ∈ range (t + 1), -c s) := by
      ext b
      rw [LinearMap.mul_apply', Real.norm_eq_abs, sq_abs, sum_mul]
      ring
    rw [hlin]
    exact LinearMap.convexOn _ (convex_Icc _ _)
  have h := regret_le_ftrl_of_strongConvexOn (V := V) (fun t b ↦ (t + a) * b ^ 2)
    (fun t b ↦ -c t * b) β (fun t ↦ ContinuousLinearMap.mul ℝ ℝ (-c t))
    (lam := fun t ↦ 2 * (t + a)) (fun t _ ↦ by positivity) (fun t _ ↦ hconv t) hβV
    (fun t ht ↦ hmin t ht.le) (fun t _ ↦ ?_) (hmin n le_rfl hu)
  swap
  · have hℓ : (fun b ↦ -c t * b) = ⇑(ContinuousLinearMap.mul ℝ ℝ (-c t)) := by
      ext b
      rw [ContinuousLinearMap.mul_apply']
    rw [hℓ]
    exact hasSubgradientWithinAt_linear _
  refine h.trans (le_of_eq ?_)
  have h0 : β 0 = 0 := by simp [hβ 0 (Nat.zero_le n)]
  have hstab (t : ℕ) : ‖ContinuousLinearMap.mul ℝ ℝ (-c t)‖ ^ 2 / (2 * (2 * (t + a))) =
      c t ^ 2 / (4 * (t + a)) := by
    rw [ContinuousLinearMap.opNorm_mul_apply, Real.norm_eq_abs, sq_abs, neg_sq]
    ring
  have hinc (t : ℕ) : (t + a) * β (t + 1) ^ 2 - (((t + 1 : ℕ) : ℝ) + a) * β (t + 1) ^ 2 =
      -β (t + 1) ^ 2 := by
    push_cast
    ring
  simp only [h0, hstab, hinc, sum_neg_distrib]
  ring

end FTRL

section Wealth

variable {ε a : ℝ} {c x : ℕ → ℝ} {n : ℕ}

/-- **The wealth of the constant-fraction bettor** [Ora, §13.7]: if the bets `x` are the bets
`x t = (∑ s < t, c s) / (2 (t + a)) * W t` of the constant-fraction bettor with parameter `a > 0`
on coins in `[-1, 1]` from the initial wealth `ε ≥ 0`, then after `n` rounds its wealth is at least
`ε exp ((∑ t < n, c t) ^ 2 / (4 (n + a)) - ∑ t < n, c t ^ 2 / (4 (t + a)))`. -/
theorem mul_exp_sq_div_sub_sum_le_wealth (hε : 0 ≤ ε) (ha : 0 < a) (hc : ∀ t < n, |c t| ≤ 1)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, c s) / (2 * (t + a)) * wealth ε c x t) :
    ε * exp ((∑ t ∈ range n, c t) ^ 2 / (4 * (n + a)) -
      ∑ t ∈ range n, c t ^ 2 / (4 * (t + a))) ≤ wealth ε c x n := by
  set β : ℕ → ℝ := fun t ↦ (∑ s ∈ range t, c s) / (2 * (t + a)) with hβ_def
  set S := ∑ t ∈ range n, c t
  set Q := ∑ t ∈ range n, c t ^ 2 / (4 * (t + a))
  have hna : 0 < (n : ℝ) + a := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hβ (t : ℕ) (ht : t ≤ n) : |β t| ≤ 1 / 2 := abs_sum_div_le ha fun s hs ↦ hc s (by omega)
  rw [wealth_eq_mul_prod (β := β) hx]
  refine mul_le_mul_of_nonneg_left ?_ hε
  -- the FTRL bound against the comparator `u = S / (2 (n + a))`
  have hu : S / (2 * (n + a)) ∈ Set.Icc (-(1 / 2)) (1 / 2) := abs_le.1 (abs_sum_div_le ha hc)
  have hregret := regret_neg_mul_le_mul_sq_add_sum_sub_sum ha hc (β := β) (fun t _ ↦ rfl) hu
  have hSeq : ∑ t ∈ range n, c t = S := rfl
  simp only [regret_eq_sum_sub_sum, neg_mul, sum_neg_distrib, ← sum_mul, hSeq] at hregret
  have hS : S * (S / (2 * (n + a))) - (n + a) * (S / (2 * (n + a))) ^ 2 =
      S ^ 2 / (4 * (n + a)) := by
    field_simp
    ring
  -- each factor `1 + β t c t` is at least `1 / 2`, and its logarithm at least `β t c t - β t ^ 2`
  have hbc (t : ℕ) (ht : t < n) : |β t * c t| ≤ 1 / 2 := by
    rw [abs_mul]
    nlinarith [hβ t ht.le, hc t ht, abs_nonneg (β t), abs_nonneg (c t)]
  have hlog (t : ℕ) (ht : t < n) : β t * c t - β t ^ 2 ≤ log (1 + β t * c t) := by
    have hc2 : (β t * c t) ^ 2 ≤ β t ^ 2 := by
      rw [mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left ((sq_le_one_iff_abs_le_one _).2 (hc t ht))
        (sq_nonneg (β t))]
    linarith [Real.sub_sq_le_log_one_add (by linarith [(abs_le.1 (hbc t ht)).1] :
      -1 / 2 ≤ β t * c t)]
  have hpos (t : ℕ) (ht : t < n) : 0 < 1 + β t * c t := by
    linarith [(abs_le.1 (hbc t ht)).1]
  -- `∑ t < n, β t ^ 2 ≤ ∑ t < n, β (t + 1) ^ 2`, since `β 0 = 0`
  have hshift : ∑ t ∈ range n, β t ^ 2 ≤ ∑ t ∈ range n, β (t + 1) ^ 2 := by
    have h := sum_range_succ' (fun t ↦ β t ^ 2) n
    have h0 : β 0 = 0 := by simp [hβ_def]
    rw [h0] at h
    linarith [sum_range_succ (fun t ↦ β t ^ 2) n, sq_nonneg (β n)]
  have hsum := sum_le_sum fun t ht ↦ hlog t (mem_range.1 ht)
  rw [sum_sub_distrib] at hsum
  -- the reward of the fractions appears as `∑ c t * β t` in the regret
  have hbc_sum : ∑ t ∈ range n, β t * c t = ∑ t ∈ range n, c t * β t :=
    sum_congr rfl fun t _ ↦ mul_comm _ _
  calc exp (S ^ 2 / (4 * (n + a)) - Q)
      ≤ exp (∑ t ∈ range n, log (1 + β t * c t)) := exp_le_exp.2 (by linarith)
    _ = ∏ t ∈ range n, (1 + β t * c t) := by
        rw [exp_sum]
        exact prod_congr rfl fun t ht ↦ exp_log (hpos t (mem_range.1 ht))

/-- **The wealth bound of the constant-fraction bettor** [Ora, §13.7]: under the assumptions of
`mul_exp_sq_div_sub_sum_le_wealth`, after `n` rounds the wealth is at least
`ε exp ((∑ t < n, c t) ^ 2 / (4 (n + a)) - n / (4 a))`. For `a = n / 4` the bettor loses at most
the fraction `1 - 1 / e` of its initial wealth, whatever the coins. -/
theorem mul_exp_sq_div_sub_div_le_wealth (hε : 0 ≤ ε) (ha : 0 < a) (hc : ∀ t < n, |c t| ≤ 1)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, c s) / (2 * (t + a)) * wealth ε c x t) :
    ε * exp ((∑ t ∈ range n, c t) ^ 2 / (4 * (n + a)) - n / (4 * a)) ≤ wealth ε c x n := by
  refine le_trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 (sub_le_sub_left ?_ _)) hε)
    (mul_exp_sq_div_sub_sum_le_wealth hε ha hc hx)
  -- each term `c t ^ 2 / (4 (t + a))` is at most `1 / (4 a)`
  calc ∑ t ∈ range n, c t ^ 2 / (4 * (t + a)) ≤ ∑ _t ∈ range n, 1 / (4 * a) :=
        sum_le_sum fun t ht ↦ by
          have hc2 : c t ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hc t (mem_range.1 ht))
          have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith
    _ = n / (4 * a) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

end Wealth

section Regret

variable {ε L a : ℝ} {g x : ℕ → ℝ} {n : ℕ}

/-- **The regret of the constant-fraction bettor** for one-dimensional online linear optimization
[Ora, §13.7]. Let `|g t| ≤ L` for the rounds `t < n`, and let `x` be the bets of the
constant-fraction bettor with parameter `a > 0` from the initial wealth `ε > 0` on the coins
`-g t / L`. Then for every `u ∈ ℝ`, `∑ t < n, g t (x t - u)` is at most
`|u| L √(2 (n + a) log (1 + 2 (n + a) exp (n / (2 a)) u ^ 2 / ε ^ 2)) + ε L`.
It is the regret–reward duality [Ora, Theorem 13.5] for the wealth bound
`mul_exp_sq_div_sub_div_le_wealth`, whose conjugate is bounded by `Real.mul_sub_mul_exp_sq_div_le`
[Ora, Lemma 13.6]. -/
theorem constantFractionBettor_regret_le (hε : 0 < ε) (hL : 0 < L) (ha : 0 < a)
    (hg : ∀ t < n, |g t| ≤ L)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, -g s / L) / (2 * (t + a)) *
      wealth ε (fun s ↦ -g s / L) x t) (u : ℝ) :
    regret (fun t y ↦ g t * y) x u n ≤
      |u| * L * √(2 * (n + a) * log (1 + 2 * (n + a) * exp (n / (2 * a)) * u ^ 2 / ε ^ 2)) +
        ε * L := by
  set c : ℕ → ℝ := fun s ↦ -g s / L with hc_def
  have hc : ∀ t < n, |c t| ≤ 1 := fun t ht ↦ by
    rw [hc_def, abs_div, abs_neg, abs_of_pos hL, div_le_one hL]
    exact hg t ht
  have hna : 0 < (n : ℝ) + a := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set S := ∑ t ∈ range n, c t with hS
  set β := ε * exp (-(n / (4 * a))) with hβ_def
  have hβ : 0 < β := by positivity
  -- the regret is `L * (ε - W) + L * (u * S)`
  have hregret : regret (fun t y ↦ g t * y) x u n =
      L * (ε - wealth ε c x n) + L * (S * u) := by
    have hℓ : (fun t y ↦ g t * y) = fun t y ↦ -L * c t * y := by
      funext t y
      rw [hc_def]
      field_simp
    have hu : ∑ t ∈ range n, -L * c t * u = -(L * (S * u)) := by
      rw [hS, sum_mul, mul_sum, ← sum_neg_distrib]
      exact sum_congr rfl fun t _ ↦ by ring
    rw [hℓ, ← regret_neg_mul_eq_mul_sub_wealth L ε c x n, regret_eq_sum_sub_sum,
      regret_eq_sum_sub_sum, hu]
    simp
  -- the wealth is at least `β * exp (S ^ 2 / (2 * (2 (n + a))))`
  have hW : β * exp (S ^ 2 / (2 * (2 * (n + a)))) ≤ wealth ε c x n := by
    refine le_of_eq_of_le ?_ (mul_exp_sq_div_sub_div_le_wealth hε.le ha hc hx)
    rw [hβ_def, hS, mul_assoc, ← exp_add]
    ring_nf
  have hconj := Real.mul_sub_mul_exp_sq_div_le (by positivity : 0 < 2 * ((n : ℝ) + a)) hβ S u
  -- `2 (n + a) u ^ 2 / β ^ 2 = 2 (n + a) exp (n / (2 a)) u ^ 2 / ε ^ 2`
  have hβsq : 2 * ((n : ℝ) + a) * u ^ 2 / β ^ 2 =
      2 * (n + a) * exp (n / (2 * a)) * u ^ 2 / ε ^ 2 := by
    have hβ2 : β ^ 2 = ε ^ 2 / exp (n / (2 * a)) := by
      rw [hβ_def, mul_pow, ← exp_nat_mul, div_eq_mul_inv (ε ^ 2), ← exp_neg]
      congr 2
      push_cast
      ring
    rw [hβ2]
    field_simp
  rw [hβsq] at hconj
  rw [hregret]
  nlinarith [mul_le_mul_of_nonneg_left hconj hL.le]

/-- **The regret of the constant-fraction bettor tuned to the horizon** [Ora, (13.10)]: with the
parameter `a = n / 4` for the horizon `n`, under the assumptions of
`constantFractionBettor_regret_le`, for every `u ∈ ℝ`,
`∑ t < n, g t (x t - u) ≤ |u| L √(5 n log (|u| √(19 n) / ε + 1)) + ε L`. -/
theorem constantFractionBettor_regret_le_of_horizon (hε : 0 < ε) (hL : 0 < L)
    (hg : ∀ t < n, |g t| ≤ L)
    (hx : ∀ t < n, x t = (∑ s ∈ range t, -g s / L) / (2 * (t + n / 4)) *
      wealth ε (fun s ↦ -g s / L) x t) (u : ℝ) :
    regret (fun t y ↦ g t * y) x u n ≤
      |u| * L * √(5 * n * log (|u| * √(19 * n) / ε + 1)) + ε * L := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [regret_zero]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine (constantFractionBettor_regret_le hε hL (by positivity) hg hx u).trans ?_
  have h1 : 2 * ((n : ℝ) + n / 4) = 5 * n / 2 := by ring
  have h2 : (n : ℝ) / (2 * (n / 4)) = 2 := by field_simp; norm_num
  rw [h1, h2]
  -- `e ^ 2 ≤ 38 / 5`, so `5 n e ^ 2 u ^ 2 / (2 ε ^ 2) ≤ (|u| √(19 n) / ε) ^ 2`
  have he : exp 2 ≤ 38 / 5 := by
    have h := exp_one_lt_d9
    have h2 : exp 2 = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
    rw [h2]
    nlinarith [exp_pos 1]
  set z := |u| * √(19 * n) / ε with hz_def
  have hz : z ^ 2 = 19 * n * u ^ 2 / ε ^ 2 := by
    rw [hz_def, div_pow, mul_pow, sq_abs, sq_sqrt (by positivity)]
    ring
  have hle : 1 + 5 * n / 2 * exp 2 * u ^ 2 / ε ^ 2 ≤ 1 + z ^ 2 := by
    have h : 5 * n / 2 * exp 2 ≤ 19 * n := by nlinarith
    rw [hz]
    exact add_le_add_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (sq_nonneg u)) (sq_nonneg ε)) 1
  -- `log (1 + z ^ 2) ≤ 2 log (z + 1)`
  have hlog : log (1 + 5 * n / 2 * exp 2 * u ^ 2 / ε ^ 2) ≤ 2 * log (z + 1) :=
    (log_le_log (by positivity) hle).trans
      (Real.log_one_add_sq_le_two_mul_log_add_one (by positivity))
  have hsq : 5 * n / 2 * log (1 + 5 * n / 2 * exp 2 * u ^ 2 / ε ^ 2) ≤ 5 * n * log (z + 1) := by
    nlinarith
  gcongr

end Regret

namespace OnlineLearner

variable {C : Type*}

/-- The bet of the constant-fraction bettor with parameter `a` at round `t` on the coins `c`, from
the initial wealth `ε`: the fraction `(∑ s < t, c s) / (2 (t + a))` of the wealth
`ε ∏ s < t, (1 + β s c s)`. -/
private noncomputable def constantFractionBet (a ε : ℝ) (c : ℕ → ℝ) (t : ℕ) : ℝ :=
  (∑ s ∈ range t, c s) / (2 * (t + a)) *
    (ε * ∏ s ∈ range t, (1 + (∑ r ∈ range s, c r) / (2 * (s + a)) * c s))

/-- The bet of round `t` depends only on the coins of the rounds `s < t`. -/
private lemma constantFractionBet_congr {a ε : ℝ} {c c' : ℕ → ℝ} {t : ℕ}
    (h : ∀ s < t, c s = c' s) : constantFractionBet a ε c t = constantFractionBet a ε c' t := by
  have hsum {s : ℕ} (hs : s ≤ t) : ∑ r ∈ range s, c r = ∑ r ∈ range s, c' r :=
    sum_congr rfl fun r hr ↦ h r ((mem_range.1 hr).trans_le hs)
  rw [constantFractionBet, constantFractionBet, hsum le_rfl]
  congr 2
  exact prod_congr rfl fun s hs ↦ by
    rw [hsum (mem_range.1 hs).le, h s (mem_range.1 hs)]

/-- The **constant-fraction bettor** [Ora, §13.7] with parameter `a`, from the initial wealth `ε`:
a bettor whose feedback is the coins, and which bets at round `t` the fraction
`(∑ s < t, c s) / (2 (t + a))` of its wealth (`run_constantFractionBettor`). -/
noncomputable def constantFractionBettor (a ε : ℝ) : OnlineLearner C ℝ ℝ where
  play t h _ := constantFractionBet a ε (fun s ↦ if hs : s < t then (h ⟨s, hs⟩).2 else 0) t

/-- **The bets of the constant-fraction bettor**: at round `t`, it bets the fraction
`(∑ s < t, c s) / (2 (t + a))` of its wealth on the coins `c`. -/
theorem run_constantFractionBettor (a ε : ℝ) (d : ℕ → C) (c : ℕ → ℝ) (t : ℕ) :
    (constantFractionBettor a ε).run d c t =
      (∑ s ∈ range t, c s) / (2 * (t + a)) *
        wealth ε c ((constantFractionBettor a ε).run d c) t := by
  have hbet (t : ℕ) : (constantFractionBettor a ε).run d c t = constantFractionBet a ε c t := by
    rw [run_def]
    exact constantFractionBet_congr fun s hs ↦ by simp [hs]
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [wealth_eq_mul_prod (β := fun s ↦ (∑ r ∈ range s, c r) / (2 * (s + a))) fun s hs ↦ ih s hs,
      hbet, constantFractionBet]

/-- The **constant-fraction bettor for one-dimensional online linear optimization** [Ora, §13.7]
with losses bounded by `L`, parameter `a` and initial wealth `ε`: on the linear losses `g t`, it
plays the bets of the constant-fraction bettor on the coins `-g t / L`
(`run_constantFractionBettorOCO`). -/
noncomputable def constantFractionBettorOCO (L a ε : ℝ) : OnlineLearner C ℝ ℝ :=
  (constantFractionBettor a ε).reduce id fun _ g ↦ -g / L

/-- The plays of the constant-fraction bettor for online linear optimization are the bets of the
constant-fraction bettor on the coins `-g t / L`. -/
theorem run_constantFractionBettorOCO (L a ε : ℝ) (d : ℕ → C) (g : ℕ → ℝ) (t : ℕ) :
    (constantFractionBettorOCO L a ε).run d g t =
      (constantFractionBettor a ε).run d (fun s ↦ -g s / L) t := by
  rw [constantFractionBettorOCO, run_reduce,
    ← (constantFractionBettor a ε).closedLoopFeedback_unique (g := fun s ↦ -g s / L) fun _ ↦ rfl]
  rfl

variable {ε L a : ℝ}

/-- The plays of the constant-fraction bettor for online linear optimization bet the fraction
`(∑ s < t, -g s / L) / (2 (t + a))` of the wealth on the coins `-g t / L`. -/
private lemma run_constantFractionBettorOCO_eq (d : ℕ → C) (g : ℕ → ℝ) (t : ℕ) :
    (constantFractionBettorOCO L a ε).run d g t =
      (∑ s ∈ range t, -g s / L) / (2 * (t + a)) *
        wealth ε (fun s ↦ -g s / L) ((constantFractionBettorOCO L a ε).run d g) t := by
  have hrun : (constantFractionBettorOCO L a ε).run d g =
      (constantFractionBettor a ε).run d (fun s ↦ -g s / L) :=
    funext (run_constantFractionBettorOCO L a ε d g)
  rw [hrun]
  exact run_constantFractionBettor a ε d _ t

/-- **The anytime regret bound of the constant-fraction bettor** [Ora, §13.7]: for `ε, L, a > 0`,
on linear losses `g t` with `|g t| ≤ L`, the regret against every `u ∈ ℝ` after `n` rounds is at
most `|u| L √(2 (n + a) log (1 + 2 (n + a) exp (n / (2 a)) u ^ 2 / ε ^ 2)) + ε L`. -/
theorem hasRegretBound_constantFractionBettorOCO (hε : 0 < ε) (hL : 0 < L) (ha : 0 < a) :
    (constantFractionBettorOCO (C := C) L a ε).HasRegretBound (fun g x ↦ g * x)
      (fun _ g ↦ |g| ≤ L) Set.univ fun n _ _ u ↦
        |u| * L * √(2 * (n + a) * log (1 + 2 * (n + a) * exp (n / (2 * a)) * u ^ 2 / ε ^ 2)) +
          ε * L :=
  hasRegretBound_iff.2 fun d g _ hg u _ ↦ constantFractionBettor_regret_le hε hL ha hg
    (fun t _ ↦ run_constantFractionBettorOCO_eq d g t) u

/-- **The regret of the constant-fraction bettor tuned to the horizon** [Ora, (13.10)]: for
`ε, L > 0`, on linear losses `g t` with `|g t| ≤ L`, the constant-fraction bettor with parameter
`n / 4` has after `n` rounds a regret against every `u ∈ ℝ` of at most
`|u| L √(5 n log (|u| √(19 n) / ε + 1)) + ε L`. -/
theorem regret_run_constantFractionBettorOCO_le (hε : 0 < ε) (hL : 0 < L) (d : ℕ → C)
    {g : ℕ → ℝ} {n : ℕ} (hg : ∀ t < n, |g t| ≤ L) (u : ℝ) :
    regret (fun t y ↦ g t * y) ((constantFractionBettorOCO L (n / 4) ε).run d g) u n ≤
      |u| * L * √(5 * n * log (|u| * √(19 * n) / ε + 1)) + ε * L :=
  constantFractionBettor_regret_le_of_horizon hε hL hg
    (fun t _ ↦ run_constantFractionBettorOCO_eq d g t) u

end OnlineLearner

end LMLExplore.OnlineLearning
