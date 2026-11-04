/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.SequentialLearning.FiniteActions
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Tracking lemmas

A *tracking* sampling rule plays, at each round, the arm whose number of pulls lags the most
behind a target, so that the empirical proportions of pulls follow a sequence of target
allocations. Track-and-Stop tracks the optimal allocations `w*(μ̂(t))` at the empirical means,
either through their cumulated sums (C-tracking) or directly, with forced exploration of the arms
that are pulled too rarely (D-tracking). The pure exploration algorithms of [DKM19] track the
cumulated sums of the allocations played by an online learner, through the ratios of the pull
counts to these sums (cumulative tracking). This file contains the deterministic statements behind
these rules: they hold for every sequence of actions `A k ω` (at a fixed `ω`) following the rule,
with `N_a(n) = pullCount A a n ω` the number of pulls of `a` in the rounds `0, …, n - 1` and
`K = Fintype.card α`. The cumulated targets of a target rule along a history, which C-tracking and
cumulative tracking compare with the pull counts, are defined here as well.

## Main definitions

* `LMLExplore.Identification.cumulatedTargets v n h`: the cumulated targets `∑_{s ≤ n} v_a(s)` of
  the target rule `v` after `n` rounds with history `h`, where `v(s)` is the target of the prefix
  of length `s` of `h`.

## Main statements

* `LMLExplore.Identification.abs_pullCount_sub_sum_le`: tracking a cumulated sum of proportions.
  If `p k` is a probability vector for every `k` and the arm played at round `k` maximizes
  `∑_{s ≤ k} p s a - N_a(k)`, then `|N_a(n) - ∑_{s < n} p s a| ≤ K - 1` [GK16, Lemma 15].
* `LMLExplore.Identification.sub_one_lt_pullCount`: forced exploration. If the arm played at
  round `k` has been pulled at most as often as every arm `a` with `N_a(k) < g k`, for a
  nondecreasing `g` with `g 0 ≤ 0` that needs more than `K` rounds to cross each integer, then
  `g n - 1 < N_a(n)` [GK16, Lemma 17].
* `LMLExplore.Identification.sqrt_sub_sub_one_lt_pullCount`: the case `g k = √k - K / 2` of the
  D-tracking rule, `√n - K / 2 - 1 < N_a(n)` [GK16, Lemma 8].
* `LMLExplore.Identification.abs_pullCount_sub_mul_le`: tracking a changing sequence of targets
  `w k` that stays `ε`-close to a probability vector `l` from round `n₀` on, with forced
  exploration below a threshold `g k ≤ 2 ε k`: `|N_a(n) - n l_a| ≤ (K - 1) max(n₀, 2 ε n + 1)` for
  `n ≥ n₀`.
* `LMLExplore.Identification.abs_pullCount_div_sub_le`: under the same assumptions, the
  proportions of pulls after `n ≥ n₀` rounds with `n₀ ≤ 3 ε n` and `1 ≤ ε n` are
  `3 (K - 1) ε`-close to `l`.
* `LMLExplore.Identification.eventually_abs_pullCount_div_sub_le`: for a sublinear threshold `g`,
  if the targets are eventually `ε`-close to `l`, the proportions of pulls are eventually
  `3 (K - 1) ε`-close to `l` [GK16, Lemma 17].
* `LMLExplore.Identification.tendsto_pullCount_div`,
  `LMLExplore.Identification.tendsto_pullCount_div_of_sqrt_sub`: if the targets converge to `l`,
  the proportions of pulls `N_a(n) / n` converge to `l a`, for a sublinear threshold `g` and for
  the threshold `√k - K / 2` of D-tracking.
* `LMLExplore.Identification.abs_pullCount_sub_sum_le_add_sum`,
  `LMLExplore.Identification.sum_sub_le_pullCount`: tracking the cumulated sums of perturbations
  `p k` of targets `w k`: if `|p k a - w k a| ≤ c k`, then
  `|N_a(n) - ∑_{s < n} w s a| ≤ K - 1 + ∑_{s < n} c s`, and if `ε k ≤ p k a`, then
  `∑_{s < n} ε s - (K - 1) ≤ N_a(n)`.
* `LMLExplore.Identification.tendsto_pullCount_div_sub_inv_mul_sum_of_abs_le`,
  `LMLExplore.Identification.tendsto_pullCount_div_of_abs_sub_sum_le`: if
  `|N_a(n) - ∑_{s < n} w s a| ≤ g n` for a sublinear `g`, then the difference between the
  proportions of pulls `N_a(n) / n` and the averages of the targets `n⁻¹ ∑_{s < n} w s a` tends
  to `0`; in particular the proportions converge to the limit of the targets whenever the targets
  converge.
* `LMLExplore.Identification.abs_pullCount_sub_sum_le_mul_one_add_sqrt_of_cTracking`,
  `LMLExplore.Identification.sqrt_add_sub_le_pullCount_of_cTracking`: C-tracking
  [GK16, Lemma 7]. If the arm
  played at round `k` maximizes `∑_{s ≤ k} w^{ε_s}_s a - N_a(k)`, with `w^ε` the mixture
  `cTrackingTarget ε w` of the target `w` with the uniform allocation and
  `ε_s = 1 / (2 √(K² + s))`, then `|N_a(n) - ∑_{s < n} w s a| ≤ (K - 1) (1 + √n)` and
  `√(n + K²) - 2 K + 1 ≤ N_a(n)`.
* `LMLExplore.Identification.tendsto_pullCount_div_sub_inv_mul_sum_of_cTracking`,
  `LMLExplore.Identification.tendsto_pullCount_div_of_cTracking`: under C-tracking, the
  difference between the proportions of pulls `N_a(n) / n` and the averages of the targets
  `n⁻¹ ∑_{s < n} w s a` tends to `0`; in particular the proportions converge to the limit of
  the targets whenever the targets converge.
* `LMLExplore.Identification.pullCount_le_sum_add_one_of_cumulativeTracking`,
  `LMLExplore.Identification.sum_sub_le_pullCount_of_cumulativeTracking`,
  `LMLExplore.Identification.abs_pullCount_sub_sum_le_of_cumulativeTracking`: cumulative tracking
  [DKM19, Lemma 7]. If `p k` is a probability vector for every `k` and the arm played at round
  `k` minimizes `N_a(k) / ∑_{s ≤ k} p s a` (in cross-multiplied form), then
  `∑_{s < n} p s a - (K - 1) ≤ N_a(n) ≤ ∑_{s < n} p s a + 1`, so that
  `|N_a(n) - ∑_{s < n} p s a| ≤ K - 1`.
* `LMLExplore.Identification.tendsto_pullCount_div_sub_inv_mul_sum_of_cumulativeTracking`,
  `LMLExplore.Identification.tendsto_pullCount_div_of_cumulativeTracking`: under cumulative
  tracking, the proportions of pulls get close to the averages of the proportions `p k`, and
  converge to their limit whenever they converge.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 3.1 and Appendix B.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Lemma 7 (in the numbering of arXiv:1906.10431).
-/

public section

open Finset Filter Learning
open scoped Topology

namespace LMLExplore.Identification

variable {α Ω : Type*} [Fintype α] [DecidableEq α] {A : ℕ → Ω → α} {ω : Ω}

omit [DecidableEq α] in
/-- There is at least one arm. -/
private lemma one_le_card_real [Nonempty α] : (1 : ℝ) ≤ Fintype.card α :=
  Nat.one_le_cast.2 Fintype.card_pos

/-- All arms but `b`: there are `K - 1` of them. -/
private lemma card_univ_erase_real (b : α) : ((univ.erase b).card : ℝ) = Fintype.card α - 1 := by
  have : Nonempty α := ⟨b⟩
  rw [card_erase_of_mem (mem_univ b), card_univ, Nat.cast_pred Fintype.card_pos]

/-! ### Tracking a cumulated sum of proportions -/

/-- The pull counts and the cumulated proportions both sum to the number of rounds. -/
private lemma sum_pullCount_sub_sum_eq_zero (p : ℕ → α → ℝ) (hp1 : ∀ k, ∑ a, p k a = 1)
    (n : ℕ) : ∑ b, ((pullCount A b n ω : ℝ) - ∑ s ∈ range n, p s b) = 0 := by
  simp only [sum_sub_distrib, ← Nat.cast_sum, sum_pullCount]
  rw [sum_comm]
  simp [hp1]

/-- The sum of the positive parts of the deficits `∑_{s < n} p s a - N_a(n)` stays at most
`K - 1` along the tracking rule of `abs_pullCount_sub_sum_le`. -/
private lemma sum_max_sum_sub_pullCount_le (p : ℕ → α → ℝ) (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, ∑ s ∈ range (k + 1), p s a - pullCount A a k ω ≤
      ∑ s ∈ range (k + 1), p s (A k ω) - pullCount A (A k ω) k ω) (n : ℕ) :
    ∑ a, max (∑ s ∈ range n, p s a - pullCount A a n ω) 0 ≤ Fintype.card α - 1 := by
  have : Nonempty α := ⟨A 0 ω⟩
  induction n with
  | zero => simpa using one_le_card_real
  | succ k ih =>
    set b := A k ω
    by_cases hb : (pullCount A b (k + 1) ω : ℝ) ≤ ∑ s ∈ range (k + 1), p s b
    · -- The played arm `b` is still in deficit: each deficit grows by at most `p k a`, and the
      -- deficit of `b` decreases by `1 - p k b`.
      calc ∑ a, max (∑ s ∈ range (k + 1), p s a - pullCount A a (k + 1) ω) 0
          ≤ ∑ a, (max (∑ s ∈ range k, p s a - pullCount A a k ω) 0 + p k a -
              if b = a then 1 else 0) := by
            refine sum_le_sum fun a _ ↦ ?_
            have hle := le_max_left (∑ s ∈ range k, p s a - pullCount A a k ω) 0
            rw [cast_pullCount_add_one, sum_range_succ]
            split_ifs with hba
            · subst hba
              rw [cast_pullCount_action_add_one, sum_range_succ] at hb
              exact max_le (by linarith) (by linarith)
            · have hle' := le_max_right (∑ s ∈ range k, p s a - pullCount A a k ω) 0
              exact max_le (by linarith) (by linarith [hp0 k a])
        _ = ∑ a, max (∑ s ∈ range k, p s a - pullCount A a k ω) 0 := by
            simp [sum_add_distrib, sum_sub_distrib, hp1]
        _ ≤ Fintype.card α - 1 := ih
    · -- The played arm `b` is no longer in deficit, and every other deficit is at most the
      -- deficit of `b` before it was played, which is less than `1`.
      rw [not_le, cast_pullCount_action_add_one] at hb
      rw [← add_sum_erase _ _ (mem_univ b)]
      have hb0 : max (∑ s ∈ range (k + 1), p s b - pullCount A b (k + 1) ω) 0 = 0 := by
        rw [cast_pullCount_action_add_one]
        exact max_eq_right (by linarith)
      rw [hb0, zero_add, ← card_univ_erase_real b, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      refine sum_le_sum fun a ha ↦ max_le ?_ zero_le_one
      rw [pullCount_eq_pullCount_of_action_ne (ne_of_mem_erase ha).symm]
      linarith [hA k a]

/-- **Tracking a cumulated sum of proportions** [GK16, Lemma 15]. Let `p k` be a probability
vector for every round `k`. If the arm played at round `k` maximizes `∑_{s ≤ k} p s a - N_a(k)`,
then after every number `n` of rounds, `|N_a(n) - ∑_{s < n} p s a| ≤ K - 1` for every arm `a`. -/
theorem abs_pullCount_sub_sum_le (p : ℕ → α → ℝ) (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, ∑ s ∈ range (k + 1), p s a - pullCount A a k ω ≤
      ∑ s ∈ range (k + 1), p s (A k ω) - pullCount A (A k ω) k ω) (n : ℕ) (a : α) :
    |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, p s a| ≤ Fintype.card α - 1 := by
  have hr := sum_max_sum_sub_pullCount_le p hp0 hp1 hA n
  set f := fun b ↦ (pullCount A b n ω : ℝ) - ∑ s ∈ range n, p s b with hf
  have hsum : ∑ b, f b = 0 := sum_pullCount_sub_sum_eq_zero p hp1 n
  have hmax : ∀ b, -f b ≤ max (∑ s ∈ range n, p s b - pullCount A b n ω) 0 :=
    fun b ↦ by simp [hf]
  rw [abs_le]
  constructor
  · have := single_le_sum (f := fun b ↦ max (∑ s ∈ range n, p s b - pullCount A b n ω) 0)
      (fun b _ ↦ le_max_right _ _) (mem_univ a)
    linarith [hmax a]
  · -- The deficits sum to zero, so the excess of `a` is the total deficit of the other arms.
    rw [← add_sum_erase _ _ (mem_univ a)] at hsum
    calc f a = ∑ b ∈ univ.erase a, -f b := by rw [sum_neg_distrib]; linarith
      _ ≤ ∑ b ∈ univ.erase a, max (∑ s ∈ range n, p s b - pullCount A b n ω) 0 :=
          sum_le_sum fun b _ ↦ hmax b
      _ ≤ ∑ b, max (∑ s ∈ range n, p s b - pullCount A b n ω) 0 :=
          sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ ↦ le_max_right _ _
      _ ≤ Fintype.card α - 1 := hr

/-! ### Forced exploration -/

/-- Suppose that from round `t` on every arm has been pulled at least `c` times, and that an arm
with exactly `c` pulls forces the play of an arm with at most `c` pulls. Then each round from `t`
on decreases by one the number of arms with at most `c` pulls, as long as it is positive. -/
private lemma card_filter_pullCount_le_le {c t : ℕ} (hc : ∀ s ≥ t, ∀ a, c ≤ pullCount A a s ω)
    (hA : ∀ s ≥ t, ∀ a, pullCount A a s ω = c → pullCount A (A s ω) s ω ≤ c) (j : ℕ) :
    (univ.filter fun a ↦ pullCount A a (t + j) ω ≤ c).card ≤ Fintype.card α - j := by
  induction j with
  | zero => simpa using card_filter_le univ _
  | succ j ihj =>
    rw [show t + (j + 1) = t + j + 1 by omega]
    have hs : t ≤ t + j := by omega
    generalize t + j = s at ihj hs ⊢
    by_cases hex : ∃ b, pullCount A b s ω ≤ c
    · obtain ⟨b, hb⟩ := hex
      have hAs : pullCount A (A s ω) s ω ≤ c := hA s hs b (le_antisymm hb (hc s hs b))
      have hsub : (univ.filter fun a ↦ pullCount A a (s + 1) ω ≤ c) ⊆
          (univ.filter fun a ↦ pullCount A a s ω ≤ c).erase (A s ω) := by
        intro a ha
        simp only [mem_filter, mem_univ, true_and, mem_erase] at ha ⊢
        refine ⟨fun has ↦ ?_, (pullCount_mono a (by omega) ω).trans ha⟩
        subst has
        rw [pullCount_action_eq_pullCount_add_one] at ha
        have := hc s hs (A s ω)
        omega
      have := card_le_card hsub
      rw [card_erase_of_mem (by simpa using hAs)] at this
      omega
    · simp only [not_exists, not_le] at hex
      have : (univ.filter fun a ↦ pullCount A a (s + 1) ω ≤ c) = ∅ :=
        filter_false_of_mem fun a _ ↦
          not_le.2 ((hex a).trans_le (pullCount_mono a (Nat.le_succ s) ω))
      simp [this]

/-- One level of the induction of `sub_one_lt_pullCount`: once `g` has reached the integer `c`,
every arm has been pulled at least `c` times. -/
private lemma le_pullCount_of_le {g : ℕ → ℝ} (hg_mono : Monotone g) (hg0 : g 0 ≤ 0)
    (hg : ∀ k (c : ℕ), g k ≤ c → g (k + Fintype.card α) < c + 1)
    (hA : ∀ k a, (pullCount A a k ω : ℝ) < g k → pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (c : ℕ) : ∀ k, (c : ℝ) ≤ g k → ∀ a, c ≤ pullCount A a k ω := by
  induction c with
  | zero => simp
  | succ c ih =>
    intro k hk
    push_cast at hk
    -- The last round `t` at which `g t ≤ c`.
    obtain ⟨t, ht, ht'⟩ : ∃ t, g t ≤ c ∧ (c : ℝ) < g (t + 1) := by
      classical
      have hex : ∃ t, (c : ℝ) < g t := ⟨k, by linarith⟩
      have h0 : Nat.find hex ≠ 0 := fun h ↦ by
        have := Nat.find_spec hex
        rw [h] at this
        linarith [c.cast_nonneg (α := ℝ)]
      refine ⟨Nat.find hex - 1, not_lt.1 (Nat.find_min hex (by omega)), ?_⟩
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
      exact Nat.find_spec hex
    have htk : t + 1 + Fintype.card α ≤ k := by
      by_contra! h
      linarith [hg_mono (show k ≤ t + Fintype.card α by omega), hg t c ht]
    -- From round `t + 1` on, every arm has `c` pulls and the arms with exactly `c` pulls are
    -- forced: each round decreases their number by one.
    have hc s (hs : t + 1 ≤ s) a : c ≤ pullCount A a s ω := ih s (ht'.trans_le (hg_mono hs)).le a
    have hZ := card_filter_pullCount_le_le hc
      (fun s hs b hb ↦ hb ▸ hA s b (by rw [hb]; exact ht'.trans_le (hg_mono hs)))
    intro a
    by_contra! ha
    have hmem : a ∈ univ.filter fun a ↦ pullCount A a (t + 1 + Fintype.card α) ω ≤ c := by
      simp only [mem_filter, mem_univ, true_and]
      have := pullCount_mono (A := A) a htk ω
      omega
    have := hZ (Fintype.card α)
    rw [Nat.sub_self, Nat.le_zero, card_eq_zero] at this
    simp [this] at hmem

/-- **Forced exploration**, the first part of [GK16, Lemma 17]. Let `g` be nondecreasing with
`g 0 ≤ 0`, such that `g` stays below `c + 1` for more than `K` rounds after it is at most the
integer `c` (in [GK16], the rounds at which `g` reaches successive integers are more than `K`
apart). If, whenever an arm `a` is in deficit (`N_a(k) < g k`), the arm played at round `k` has
been pulled at most as often as `a`, then every arm satisfies `g n - 1 < N_a(n)` after every
number `n` of rounds. -/
theorem sub_one_lt_pullCount {g : ℕ → ℝ} (hg_mono : Monotone g) (hg0 : g 0 ≤ 0)
    (hg : ∀ k (c : ℕ), g k ≤ c → g (k + Fintype.card α) < c + 1)
    (hA : ∀ k a, (pullCount A a k ω : ℝ) < g k → pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (n : ℕ) (a : α) : g n - 1 < pullCount A a n ω := by
  rcases lt_or_ge (g n) 0 with h | h
  · linarith [(pullCount A a n ω).cast_nonneg (α := ℝ)]
  · have := le_pullCount_of_le hg_mono hg0 hg hA ⌊g n⌋₊ n (Nat.floor_le h) a
    have hlt := Nat.lt_floor_add_one (g n)
    have : (⌊g n⌋₊ : ℝ) ≤ pullCount A a n ω := by exact_mod_cast this
    linarith

/-- The threshold `√k - K / 2` of the D-tracking rule needs more than `K` rounds to cross each
integer. -/
private lemma sqrt_add_sub_lt (K : ℕ) (k c : ℕ) (h : √(k : ℝ) - K / 2 ≤ c) :
    √((k + K : ℕ) : ℝ) - K / 2 < c + 1 := by
  have hs := Real.sqrt_nonneg (k : ℝ)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
  have hc := c.cast_nonneg (α := ℝ)
  push_cast
  rcases lt_or_ge ((K : ℝ) - 1) (2 * √(k : ℝ)) with hK | hK
  · -- `√(k + K) < √k + 1` since `K < 2 √k + 1`.
    have : √((k : ℝ) + K) < √k + 1 := by
      rw [Real.sqrt_lt' (by positivity)]
      nlinarith
    linarith
  · -- `√(k + K) ≤ (K + 1) / 2` since `k ≤ (K - 1)² / 4`.
    have : √((k : ℝ) + K) ≤ (K + 1) / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    linarith

/-- **Forced exploration of D-tracking**, the first part of [GK16, Lemma 8]. If, whenever an arm
`a` satisfies `N_a(k) < √k - K / 2`, the arm played at round `k` has been pulled at most as often
as `a`, then every arm satisfies `√n - K / 2 - 1 < N_a(n)` after every number `n` of rounds. -/
theorem sqrt_sub_sub_one_lt_pullCount
    (hA : ∀ k a, (pullCount A a k ω : ℝ) < √(k : ℝ) - Fintype.card α / 2 →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω) (n : ℕ) (a : α) :
    √(n : ℝ) - Fintype.card α / 2 - 1 < pullCount A a n ω :=
  sub_one_lt_pullCount (g := fun k ↦ √(k : ℝ) - Fintype.card α / 2)
    (fun _ _ h ↦ sub_le_sub_right (Real.sqrt_le_sqrt (Nat.cast_le.2 h)) _)
    (by rw [Nat.cast_zero, Real.sqrt_zero, zero_sub, neg_nonpos]; positivity)
    (sqrt_add_sub_lt _) hA n a

/-! ### Tracking a changing sequence of targets -/

/-- The excesses `N_b(k) - k l_b` of the arms over a probability vector `l` sum to zero. -/
private lemma sum_pullCount_sub_mul_eq_zero {l : α → ℝ} (hl1 : ∑ a, l a = 1) (k : ℕ) :
    ∑ b, ((pullCount A b k ω : ℝ) - k * l b) = 0 := by
  simp only [sum_sub_distrib, ← Nat.cast_sum, sum_pullCount, ← mul_sum, hl1, mul_one, sub_self]

/-- One round of the rule of `abs_pullCount_sub_mul_le`: if the targets `w k` are `ε`-close to the
probability vector `l` and `g k ≤ 2 ε k`, the arm played at round `k` has excess `N_a(k) - k l_a`
at most `2 ε k`, either because it is forced or because it tracks `w k`. -/
private lemma pullCount_action_sub_mul_le {g : ℕ → ℝ} {w : ℕ → α → ℝ} {l : α → ℝ} {ε : ℝ}
    {k : ℕ} (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ a, (pullCount A a k ω : ℝ) < g k → pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : (∀ a, g k ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hw : ∀ a, |w k a - l a| ≤ ε) (hg : g k ≤ 2 * ε * k) :
    (pullCount A (A k ω) k ω : ℝ) - k * l (A k ω) ≤ 2 * ε * k := by
  have hkl := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hl0 (A k ω))
  by_cases hU : ∃ b, (pullCount A b k ω : ℝ) < g k
  · obtain ⟨b, hb⟩ := hU
    have : (pullCount A (A k ω) k ω : ℝ) ≤ pullCount A b k ω := by exact_mod_cast hforced b hb
    linarith
  · simp only [not_exists, not_lt] at hU
    -- Since the excesses sum to zero, some arm `j` has nonpositive excess.
    have : Nonempty α := ⟨A k ω⟩
    obtain ⟨j, -, hj⟩ := exists_le_of_sum_le univ_nonempty
      (show ∑ b, ((pullCount A b k ω : ℝ) - k * l b) ≤ ∑ _b : α, (0 : ℝ) by
        simp [sum_pullCount_sub_mul_eq_zero hl1])
    have htj := htrack hU j
    have hk0 := Nat.cast_nonneg (α := ℝ) k
    have h1 := mul_le_mul_of_nonneg_left (abs_le.1 (hw j)).1 hk0
    have h2 := mul_le_mul_of_nonneg_left (abs_le.1 (hw (A k ω))).2 hk0
    nlinarith

omit [Fintype α] in
/-- The induction of `abs_pullCount_sub_mul_le`: if from round `n₀` on the arm played at round `k`
has excess `N_a(k) - k l_a` at most `2 ε k`, then for `n ≥ n₀` the excess of every arm is at most
`max(n₀, 2 ε n + 1)`. -/
private lemma pullCount_sub_mul_le_max {l : α → ℝ} {ε : ℝ} {n₀ : ℕ} (hl0 : ∀ a, 0 ≤ l a)
    (hε : 0 ≤ ε) (hA : ∀ k ≥ n₀, (pullCount A (A k ω) k ω : ℝ) - k * l (A k ω) ≤ 2 * ε * k)
    (b : α) {n : ℕ} (hn : n₀ ≤ n) :
    (pullCount A b n ω : ℝ) - n * l b ≤ max (n₀ : ℝ) (2 * ε * n + 1) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine le_max_of_le_left ?_
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n₀) (hl0 b)
    have : (pullCount A b n₀ ω : ℝ) ≤ n₀ := by exact_mod_cast pullCount_le b n₀ ω
    linarith
  | succ n hn ih =>
    rw [cast_pullCount_add_one]
    push_cast
    split_ifs with hb
    · have := hA n hn
      rw [hb] at this
      refine le_max_of_le_right ?_
      nlinarith [hl0 b]
    · have hmono : max (n₀ : ℝ) (2 * ε * n + 1) ≤ max (n₀ : ℝ) (2 * ε * (n + 1) + 1) :=
        max_le_max le_rfl (by nlinarith)
      linarith [hl0 b]

/-- **Tracking a changing sequence of targets**, the non-asymptotic bound in the proof of the
second part of [GK16, Lemma 17]. Let `l` be a probability vector and `n₀` a round from which the
targets `w k` are `ε`-close to `l` and the exploration threshold satisfies `g k ≤ 2 ε k`. Suppose
that from round `n₀` on, the arm played at round `k` has been pulled at most as often as every arm
`a` in deficit (`N_a(k) < g k`), and, if no arm is in deficit, maximizes `k w k a - N_a(k)`. Then
for `n ≥ n₀`, `|N_a(n) - n l_a| ≤ (K - 1) max(n₀, 2 ε n + 1)`. -/
theorem abs_pullCount_sub_mul_le {g : ℕ → ℝ} {w : ℕ → α → ℝ} {l : α → ℝ} {ε : ℝ} {n₀ : ℕ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ k ≥ n₀, ∀ a, (pullCount A a k ω : ℝ) < g k →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ k ≥ n₀, (∀ a, g k ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hw : ∀ k ≥ n₀, ∀ a, |w k a - l a| ≤ ε) (hg : ∀ k ≥ n₀, g k ≤ 2 * ε * k)
    {n : ℕ} (hn : n₀ ≤ n) (a : α) :
    |(pullCount A a n ω : ℝ) - n * l a| ≤ (Fintype.card α - 1) * max (n₀ : ℝ) (2 * ε * n + 1) := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hw n₀ le_rfl a)
  -- Every excess is at most `M`, and the excesses sum to zero.
  have hup b := pullCount_sub_mul_le_max hl0 hε (fun k hk ↦ pullCount_action_sub_mul_le hl0 hl1
    (hforced k hk) (htrack k hk) (hw k hk) (hg k hk)) b hn
  set M := max (n₀ : ℝ) (2 * ε * n + 1)
  have hM : 0 ≤ M := le_max_of_le_left (Nat.cast_nonneg _)
  have hrest := sum_pullCount_sub_mul_eq_zero (A := A) (ω := ω) hl1 n
  rw [← add_sum_erase _ _ (mem_univ a)] at hrest
  rw [← card_univ_erase_real a, abs_le]
  constructor
  · -- The excess of `a` is minus the excess of the other arms, each at most `M`.
    have : ∑ b ∈ univ.erase a, ((pullCount A b n ω : ℝ) - n * l b) ≤ ∑ _b ∈ univ.erase a, M :=
      sum_le_sum fun b _ ↦ hup b
    rw [sum_const, nsmul_eq_mul] at this
    linarith
  · rcases (univ.erase a).eq_empty_or_nonempty with h | h
    · rw [h, sum_empty, add_zero] at hrest
      rw [h, card_empty, Nat.cast_zero, zero_mul]
      exact hrest.le
    · have : (1 : ℝ) ≤ (univ.erase a).card := by exact_mod_cast h.card_pos
      calc (pullCount A a n ω : ℝ) - n * l a ≤ M := hup a
        _ ≤ (univ.erase a).card * M := le_mul_of_one_le_left hM this

/-- **Tracking a changing sequence of targets**, the bound on the proportions of pulls after a
fixed round in the proof of the second part of [GK16, Lemma 17]. Under the assumptions of
`abs_pullCount_sub_mul_le`, if `n ≥ n₀` satisfies `n₀ ≤ 3 ε n` and `1 ≤ ε n`, then the proportions
of pulls after `n` rounds are `3 (K - 1) ε`-close to `l`. -/
theorem abs_pullCount_div_sub_le {g : ℕ → ℝ} {w : ℕ → α → ℝ} {l : α → ℝ} {ε : ℝ} {n₀ : ℕ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ k ≥ n₀, ∀ a, (pullCount A a k ω : ℝ) < g k →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ k ≥ n₀, (∀ a, g k ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hw : ∀ k ≥ n₀, ∀ a, |w k a - l a| ≤ ε) (hg : ∀ k ≥ n₀, g k ≤ 2 * ε * k)
    {n : ℕ} (hn : n₀ ≤ n) (hn₀ : (n₀ : ℝ) ≤ 3 * ε * n) (hεn : 1 ≤ ε * n) (a : α) :
    |(pullCount A a n ω : ℝ) / n - l a| ≤ 3 * (Fintype.card α - 1) * ε := by
  have : Nonempty α := ⟨a⟩
  have hK := one_le_card_real (α := α)
  have hpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h ↦ by norm_num [h] at hεn)
  have h := abs_pullCount_sub_mul_le hl0 hl1 hforced htrack hw hg hn a
  have hmax : max (n₀ : ℝ) (2 * ε * n + 1) ≤ 3 * ε * n := max_le hn₀ (by linarith)
  rw [show (pullCount A a n ω : ℝ) / n - l a = ((pullCount A a n ω : ℝ) - n * l a) / n by
    field_simp, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |(pullCount A a n ω : ℝ) - n * l a| ≤ (Fintype.card α - 1) * max (n₀ : ℝ) (2 * ε * n + 1) :=
        h
    _ ≤ (Fintype.card α - 1) * (3 * ε * n) := by gcongr
    _ = 3 * (Fintype.card α - 1) * ε * n := by ring

/-- **Tracking a changing sequence of targets**, the second part of [GK16, Lemma 17]. Let `l` be
a probability vector and `g` a sublinear exploration threshold (`g k ≤ c k` eventually, for every
`c > 0`). Suppose that from some round on, the arm played at round `k` has been pulled at most as
often as every arm `a` in deficit (`N_a(k) < g k`), and, if no arm is in deficit, maximizes
`k w k a - N_a(k)`. If the targets `w k` are eventually `ε`-close to `l`, then the proportions of
pulls are eventually `3 (K - 1) ε`-close to `l`. -/
theorem eventually_abs_pullCount_div_sub_le {g : ℕ → ℝ} {w : ℕ → α → ℝ} {l : α → ℝ} {ε : ℝ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ᶠ k in atTop, ∀ a, (pullCount A a k ω : ℝ) < g k →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ᶠ k in atTop, (∀ a, g k ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hg : ∀ c > 0, ∀ᶠ k in atTop, g k ≤ c * k) (hε : 0 < ε)
    (hw : ∀ᶠ k in atTop, ∀ a, |w k a - l a| ≤ ε) :
    ∀ᶠ n in atTop, ∀ a, |(pullCount A a n ω : ℝ) / n - l a| ≤ 3 * (Fintype.card α - 1) * ε := by
  obtain ⟨n₀, hn₀⟩ :=
    eventually_atTop.1 ((hw.and (hg (2 * ε) (by positivity))).and (hforced.and htrack))
  filter_upwards [eventually_ge_atTop n₀,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop ((n₀ : ℝ) / (3 * ε)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / ε)] with n hn hn₀' hn1' a
  rw [div_le_iff₀ (by positivity)] at hn₀'
  rw [div_le_iff₀ hε] at hn1'
  exact abs_pullCount_div_sub_le hl0 hl1 (fun k hk ↦ (hn₀ k hk).2.1) (fun k hk ↦ (hn₀ k hk).2.2)
    (fun k hk ↦ (hn₀ k hk).1.1) (fun k hk ↦ (hn₀ k hk).1.2) hn (by linarith) (by linarith) a

/-- **Convergence of the proportions of pulls**, a consequence of [GK16, Lemma 17]. Let `l` be a
probability vector and `g` a sublinear exploration threshold (`g k ≤ c k` eventually, for every
`c > 0`). Suppose that from some round on, the arm played at round `k` has been pulled at most as
often as every arm `a` in deficit (`N_a(k) < g k`), and, if no arm is in deficit, maximizes
`k w k a - N_a(k)`. If the targets `w k` converge to `l`, then the proportions of pulls
`N_a(n) / n` converge to `l a`. -/
theorem tendsto_pullCount_div {g : ℕ → ℝ} {w : ℕ → α → ℝ} {l : α → ℝ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ᶠ k in atTop, ∀ a, (pullCount A a k ω : ℝ) < g k →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ᶠ k in atTop, (∀ a, g k ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hg : ∀ c > 0, ∀ᶠ k in atTop, g k ≤ c * k)
    (hw : ∀ a, Tendsto (fun k ↦ w k a) atTop (𝓝 (l a))) (a : α) :
    Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  have : Nonempty α := ⟨a⟩
  have hK := one_le_card_real (α := α)
  refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε > 0, 3 * Fintype.card α * ε = δ :=
    ⟨δ / (3 * Fintype.card α), by positivity, by field_simp⟩
  have hw' : ∀ᶠ k in atTop, ∀ b, |w k b - l b| ≤ ε := eventually_all.2 fun b ↦
    (Metric.tendsto_nhds.1 (hw b) ε hε).mono fun k hk ↦ (Real.dist_eq _ _ ▸ hk).le
  filter_upwards [eventually_abs_pullCount_div_sub_le hl0 hl1 hforced htrack hg hε hw'] with n hn
  rw [Real.dist_eq]
  linarith [hn a]

/-- **Convergence of the proportions of pulls of D-tracking**, the limit form of the second part
of [GK16, Lemma 8]. Let `l` be a probability vector. Suppose that from some round on, the arm
played at round `k` has been pulled at most as often as every arm `a` with `N_a(k) < √k - K / 2`,
and, if there is no such arm, maximizes `k w k a - N_a(k)`. If the targets `w k` converge to `l`,
then the proportions of pulls `N_a(n) / n` converge to `l a`. -/
theorem tendsto_pullCount_div_of_sqrt_sub {w : ℕ → α → ℝ} {l : α → ℝ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ᶠ k : ℕ in atTop, ∀ a, (pullCount A a k ω : ℝ) < √(k : ℝ) - Fintype.card α / 2 →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ᶠ k : ℕ in atTop, (∀ a, √(k : ℝ) - Fintype.card α / 2 ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hw : ∀ a, Tendsto (fun k ↦ w k a) atTop (𝓝 (l a))) (a : α) :
    Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  refine tendsto_pullCount_div (g := fun k ↦ √(k : ℝ) - Fintype.card α / 2) hl0 hl1 hforced
    htrack (fun c hc ↦ ?_) hw a
  -- `√k ≤ c k` as soon as `1 / c ^ 2 ≤ k`.
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / c ^ 2)] with k hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsq : √(k : ℝ) ≤ c * k := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hk
    nlinarith
  linarith [show (0 : ℝ) ≤ Fintype.card α / 2 by positivity]

/-! ### C-tracking -/

/-- **Tracking perturbed cumulated targets.** Let `p k` be a probability vector for every round
`k`, and let the arm played at round `k` maximize `∑_{s ≤ k} p s a - N_a(k)`. If `p k` is
`c k`-close to the target `w k` on every arm, then after every number `n` of rounds,
`|N_a(n) - ∑_{s < n} w s a| ≤ K - 1 + ∑_{s < n} c s`. -/
theorem abs_pullCount_sub_sum_le_add_sum (p w : ℕ → α → ℝ) {c : ℕ → ℝ} (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, ∑ s ∈ range (k + 1), p s a - pullCount A a k ω ≤
      ∑ s ∈ range (k + 1), p s (A k ω) - pullCount A (A k ω) k ω)
    (hpw : ∀ k a, |p k a - w k a| ≤ c k) (n : ℕ) (a : α) :
    |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, w s a| ≤
      Fintype.card α - 1 + ∑ s ∈ range n, c s := by
  have hp := abs_pullCount_sub_sum_le p hp0 hp1 hA n a
  have hpw' : |∑ s ∈ range n, p s a - ∑ s ∈ range n, w s a| ≤ ∑ s ∈ range n, c s := by
    rw [← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ ↦ hpw s a)
  calc |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, w s a|
      = |((pullCount A a n ω : ℝ) - ∑ s ∈ range n, p s a) +
          (∑ s ∈ range n, p s a - ∑ s ∈ range n, w s a)| := by rw [sub_add_sub_cancel]
    _ ≤ Fintype.card α - 1 + ∑ s ∈ range n, c s := (abs_add_le _ _).trans (add_le_add hp hpw')

/-- **Forced exploration by tracking cumulated targets.** Let `p k` be a probability vector for
every round `k`, and let the arm played at round `k` maximize `∑_{s ≤ k} p s a - N_a(k)`. If
`ε k ≤ p k a` for every arm, then after every number `n` of rounds,
`∑_{s < n} ε s - (K - 1) ≤ N_a(n)`. -/
theorem sum_sub_le_pullCount (p : ℕ → α → ℝ) {ε : ℕ → ℝ} (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, ∑ s ∈ range (k + 1), p s a - pullCount A a k ω ≤
      ∑ s ∈ range (k + 1), p s (A k ω) - pullCount A (A k ω) k ω)
    (hε : ∀ k a, ε k ≤ p k a) (n : ℕ) (a : α) :
    ∑ s ∈ range n, ε s - (Fintype.card α - 1) ≤ pullCount A a n ω := by
  have hp := (abs_le.1 (abs_pullCount_sub_sum_le p hp0 hp1 hA n a)).1
  have : ∑ s ∈ range n, ε s ≤ ∑ s ∈ range n, p s a := sum_le_sum fun s _ ↦ hε s a
  linarith

omit [DecidableEq α] in
/-- The target of C-tracking for the allocation `w` and the exploration rate `ε`: the mixture
`(1 - K ε) w + ε` of `w` with the uniform allocation, which gives at least `ε` to every arm. It
replaces the `ℓ^∞` projection of `w` on the allocations with entries at least `ε` of [GK16]: both
are allocations with entries at least `ε` and at distance at most `(K - 1) ε` from `w`, the two
properties that the guarantees of C-tracking use. -/
noncomputable def cTrackingTarget (ε : ℝ) (w : α → ℝ) (a : α) : ℝ :=
  (1 - Fintype.card α * ε) * w a + ε

omit [DecidableEq α] in
/-- The target of C-tracking is `(1 - K ε) w a + ε` on the arm `a`. -/
lemma cTrackingTarget_apply (ε : ℝ) (w : α → ℝ) (a : α) :
    cTrackingTarget ε w a = (1 - Fintype.card α * ε) * w a + ε :=
  (rfl)

omit [DecidableEq α] in
/-- The target of C-tracking gives at least `ε` to every arm. -/
lemma le_cTrackingTarget {ε : ℝ} {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a)
    (hε : Fintype.card α * ε ≤ 1) (a : α) : ε ≤ cTrackingTarget ε w a := by
  rw [cTrackingTarget_apply]
  nlinarith [hw0 a]

omit [DecidableEq α] in
/-- The target of C-tracking with a nonnegative exploration rate is nonnegative. -/
lemma cTrackingTarget_nonneg {ε : ℝ} {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hε0 : 0 ≤ ε)
    (hε : Fintype.card α * ε ≤ 1) (a : α) : 0 ≤ cTrackingTarget ε w a :=
  hε0.trans (le_cTrackingTarget hw0 hε a)

omit [DecidableEq α] in
/-- The target of C-tracking of an allocation is an allocation. -/
lemma sum_cTrackingTarget {ε : ℝ} {w : α → ℝ} (hw1 : ∑ a, w a = 1) :
    ∑ a, cTrackingTarget ε w a = 1 := by
  simp only [cTrackingTarget_apply, sum_add_distrib, ← mul_sum, hw1, sum_const, card_univ,
    nsmul_eq_mul]
  ring

omit [DecidableEq α] in
/-- The target of C-tracking of an allocation `w` is `(K - 1) ε`-close to `w` on every arm. -/
lemma abs_cTrackingTarget_sub_le {ε : ℝ} {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (hε : 0 ≤ ε) (a : α) : |cTrackingTarget ε w a - w a| ≤ (Fintype.card α - 1) * ε := by
  classical
  have : Nonempty α := ⟨a⟩
  have hK := one_le_card_real (α := α)
  have hw : w ∈ simplex α := mem_simplex_iff.2 ⟨hw0, hw1⟩
  have hwa : w a ≤ 1 := (simplex_subset_Icc hw).2 a
  -- The other arms have total weight `1 - w a ≤ K - 1`.
  have hrest : 1 - w a ≤ Fintype.card α - 1 := by
    have hsplit := add_sum_erase univ w (mem_univ a)
    have : ∑ b ∈ univ.erase a, w b ≤ ∑ _b ∈ univ.erase a, (1 : ℝ) :=
      sum_le_sum fun b _ ↦ (simplex_subset_Icc hw).2 b
    rw [sum_const, nsmul_eq_mul, mul_one, card_univ_erase_real a] at this
    linarith
  rw [cTrackingTarget_apply, show (1 - Fintype.card α * ε) * w a + ε - w a =
    (1 - Fintype.card α * w a) * ε by ring, abs_mul, abs_of_nonneg hε]
  refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) hε <;> nlinarith [hw0 a]

/-- The exploration rate `ε_s = 1 / (2 √(K² + s))` of C-tracking after `s` rounds with `K` arms
[GK16]. -/
noncomputable def cTrackingRate (K s : ℕ) : ℝ := 1 / (2 * √((K : ℝ) ^ 2 + s))

/-- The exploration rate of C-tracking is `ε_s = 1 / (2 √(K² + s))`. -/
lemma cTrackingRate_def (K s : ℕ) : cTrackingRate K s = 1 / (2 * √((K : ℝ) ^ 2 + s)) :=
  (rfl)

/-- The exploration rate of C-tracking is nonnegative. -/
lemma cTrackingRate_nonneg (K s : ℕ) : 0 ≤ cTrackingRate K s := by
  rw [cTrackingRate_def]
  positivity

/-- `K ε_s ≤ 1`, so the target of C-tracking is a mixture of the target and the uniform
allocation. -/
lemma mul_cTrackingRate_le_one (K s : ℕ) : K * cTrackingRate K s ≤ 1 := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsq : (K : ℝ) ≤ √((K : ℝ) ^ 2 + s) :=
    Real.le_sqrt_of_sq_le (by linarith [Nat.cast_nonneg (α := ℝ) s])
  rw [cTrackingRate_def, mul_one_div, div_le_one (by positivity)]
  linarith

/-- The sum of the exploration rates of C-tracking over the first `n` rounds is at most `√n`. -/
lemma sum_cTrackingRate_le {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    ∑ s ∈ range n, cTrackingRate K s ≤ √(n : ℝ) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  calc ∑ s ∈ range n, cTrackingRate K s
      ≤ ∑ s ∈ range n, (√((s : ℝ) + 1) - √(s : ℝ)) := by
        refine sum_le_sum fun s _ ↦ ?_
        have hs := Nat.cast_nonneg (α := ℝ) s
        refine le_trans ?_ (Real.one_div_two_mul_sqrt_add_one_le_sqrt_add_one_sub_sqrt hs)
        rw [cTrackingRate_def]
        exact one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith)) zero_le_two)
    _ = √(n : ℝ) := by
        have h := sum_range_sub (fun s : ℕ ↦ √(s : ℝ)) n
        push_cast at h
        simpa using h

/-- The sum of the exploration rates of C-tracking over the first `n` rounds is at least
`√(n + K²) - K`. -/
lemma sqrt_add_sub_le_sum_cTrackingRate {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    √((n : ℝ) + K ^ 2) - K ≤ ∑ s ∈ range n, cTrackingRate K s := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  calc √((n : ℝ) + K ^ 2) - K
      = ∑ s ∈ range n, (√((K : ℝ) ^ 2 + s + 1) - √((K : ℝ) ^ 2 + s)) := by
        have h := sum_range_sub (fun s : ℕ ↦ √((K : ℝ) ^ 2 + s)) n
        push_cast at h
        simp only [← add_assoc] at h
        rw [h, add_zero, Real.sqrt_sq (by linarith), add_comm]
    _ ≤ ∑ s ∈ range n, cTrackingRate K s := by
        refine sum_le_sum fun s _ ↦ ?_
        rw [cTrackingRate_def]
        exact Real.sqrt_add_one_sub_sqrt_le_one_div_two_mul_sqrt (by positivity)

/-- **Tracking of C-tracking** [GK16, Lemma 7]. Let `w k` be an allocation for every round `k`,
and let the arm played at round `k` maximize `∑_{s ≤ k} w^{ε_s}_s a - N_a(k)`, where `w^{ε_s}_s` is
the target `cTrackingTarget ε_s (w s)` and `ε_s = cTrackingRate K s`. Then after every number `n`
of rounds, `|N_a(n) - ∑_{s < n} w s a| ≤ (K - 1) (1 + √n)` for every arm `a`. ([GK16] states
the bound `K (1 + √n)`.) -/
theorem abs_pullCount_sub_sum_le_mul_one_add_sqrt_of_cTracking {w : ℕ → α → ℝ}
    (hw0 : ∀ k a, 0 ≤ w k a) (hw1 : ∀ k, ∑ a, w k a = 1)
    (hA : ∀ k a,
      ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) a -
          pullCount A a k ω ≤
        ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) (A k ω) -
          pullCount A (A k ω) k ω) (n : ℕ) (a : α) :
    |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, w s a| ≤ (Fintype.card α - 1) * (1 + √(n : ℝ)) := by
  have : Nonempty α := ⟨a⟩
  have hK : 1 ≤ Fintype.card α := Fintype.card_pos
  have h := abs_pullCount_sub_sum_le_add_sum _ w
    (fun k ↦ cTrackingTarget_nonneg (hw0 k) (cTrackingRate_nonneg _ k)
      (mul_cTrackingRate_le_one _ k))
    (fun k ↦ sum_cTrackingTarget (hw1 k)) hA
    (fun k b ↦ abs_cTrackingTarget_sub_le (hw0 k) (hw1 k) (cTrackingRate_nonneg _ k) b) n a
  rw [← mul_sum] at h
  have hK1 : (0 : ℝ) ≤ Fintype.card α - 1 := by linarith [one_le_card_real (α := α)]
  nlinarith [sum_cTrackingRate_le hK n]

/-- **Forced exploration of C-tracking** [GK16, Lemma 7]. Let `w k` be an allocation for every
round `k`, and let the arm played at round `k` maximize `∑_{s ≤ k} w^{ε_s}_s a - N_a(k)`, where
`w^{ε_s}_s` is the target `cTrackingTarget ε_s (w s)` and `ε_s = cTrackingRate K s`. Then after
every number `n` of rounds, `√(n + K²) - 2 K + 1 ≤ N_a(n)` for every arm `a`. ([GK16] states the
bound `√(n + K²) - 2 K`.) -/
theorem sqrt_add_sub_le_pullCount_of_cTracking {w : ℕ → α → ℝ} (hw0 : ∀ k a, 0 ≤ w k a)
    (hw1 : ∀ k, ∑ a, w k a = 1)
    (hA : ∀ k a,
      ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) a -
          pullCount A a k ω ≤
        ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) (A k ω) -
          pullCount A (A k ω) k ω) (n : ℕ) (a : α) :
    √((n : ℝ) + Fintype.card α ^ 2) - 2 * Fintype.card α + 1 ≤ pullCount A a n ω := by
  have : Nonempty α := ⟨a⟩
  have hK : 1 ≤ Fintype.card α := Fintype.card_pos
  have h := sum_sub_le_pullCount _
    (fun k ↦ cTrackingTarget_nonneg (hw0 k) (cTrackingRate_nonneg _ k)
      (mul_cTrackingRate_le_one _ k))
    (fun k ↦ sum_cTrackingTarget (hw1 k)) hA
    (fun k b ↦ le_cTrackingTarget (hw0 k) (mul_cTrackingRate_le_one _ k) b) n a
  linarith [sqrt_add_sub_le_sum_cTrackingRate hK n]

omit [Fintype α] in
/-- **Proportions of pulls of a sublinear tracking.** If
`|N_a(n) - ∑_{s < n} w s a| ≤ g n` for every `n`, with `g n / n → 0`, then the difference between
the proportion of pulls `N_a(n) / n` and the average `n⁻¹ ∑_{s < n} w s a` of the targets tends
to `0`. -/
theorem tendsto_pullCount_div_sub_inv_mul_sum_of_abs_le {w : ℕ → α → ℝ} {g : ℕ → ℝ} {a : α}
    (h : ∀ n, |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, w s a| ≤ g n)
    (hg : Tendsto (fun n : ℕ ↦ g n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (pullCount A a n ω : ℝ) / n - (n : ℝ)⁻¹ * ∑ s ∈ range n, w s a) atTop
      (𝓝 0) := by
  refine squeeze_zero_norm (fun n ↦ ?_) hg
  rw [inv_mul_eq_div, ← sub_div, norm_div, Real.norm_eq_abs, Real.norm_natCast]
  exact div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg n)

omit [Fintype α] in
/-- **Convergence of the proportions of pulls of a sublinear tracking.** If
`|N_a(n) - ∑_{s < n} w s a| ≤ g n` for every `n`, with `g n / n → 0`, and if the targets `w k a`
converge to `l a`, then the proportions of pulls `N_a(n) / n` converge to `l a`. -/
theorem tendsto_pullCount_div_of_abs_sub_sum_le {w : ℕ → α → ℝ} {l : α → ℝ} {g : ℕ → ℝ} {a : α}
    (h : ∀ n, |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, w s a| ≤ g n)
    (hg : Tendsto (fun n : ℕ ↦ g n / n) atTop (𝓝 0))
    (hw : Tendsto (fun k ↦ w k a) atTop (𝓝 (l a))) :
    Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  simpa using (tendsto_pullCount_div_sub_inv_mul_sum_of_abs_le h hg).add hw.cesaro

/-- **Proportions of pulls of C-tracking.** Under the assumptions of
`abs_pullCount_sub_sum_le_mul_one_add_sqrt_of_cTracking`, the difference between the proportion
of pulls `N_a(n) / n` and the average `n⁻¹ ∑_{s < n} w s a` of the targets tends to `0`. -/
theorem tendsto_pullCount_div_sub_inv_mul_sum_of_cTracking {w : ℕ → α → ℝ}
    (hw0 : ∀ k a, 0 ≤ w k a) (hw1 : ∀ k, ∑ a, w k a = 1)
    (hA : ∀ k a,
      ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) a -
          pullCount A a k ω ≤
        ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) (A k ω) -
          pullCount A (A k ω) k ω) (a : α) :
    Tendsto (fun n : ℕ ↦ (pullCount A a n ω : ℝ) / n - (n : ℝ)⁻¹ * ∑ s ∈ range n, w s a) atTop
      (𝓝 0) := by
  refine tendsto_pullCount_div_sub_inv_mul_sum_of_abs_le
    (abs_pullCount_sub_sum_le_mul_one_add_sqrt_of_cTracking hw0 hw1 hA · a) ?_
  -- `(K - 1) (1 + √n) / n` tends to `0`.
  simpa only [mul_div_assoc, mul_zero, Function.comp_def] using
    (Real.tendsto_one_add_sqrt_div_atTop.comp tendsto_natCast_atTop_atTop).const_mul
      ((Fintype.card α : ℝ) - 1)

/-- **Convergence of the proportions of pulls of C-tracking.** Under the assumptions of
`abs_pullCount_sub_sum_le_mul_one_add_sqrt_of_cTracking`, if the targets `w k a` converge to
`l a`, then the proportions of pulls `N_a(n) / n` converge to `l a`. -/
theorem tendsto_pullCount_div_of_cTracking {w : ℕ → α → ℝ} {l : α → ℝ} (hw0 : ∀ k a, 0 ≤ w k a)
    (hw1 : ∀ k, ∑ a, w k a = 1)
    (hA : ∀ k a,
      ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) a -
          pullCount A a k ω ≤
        ∑ s ∈ range (k + 1), cTrackingTarget (cTrackingRate (Fintype.card α) s) (w s) (A k ω) -
          pullCount A (A k ω) k ω) {a : α} (hw : Tendsto (fun k ↦ w k a) atTop (𝓝 (l a))) :
    Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  simpa using (tendsto_pullCount_div_sub_inv_mul_sum_of_cTracking hw0 hw1 hA a).add hw.cesaro

/-! ### Cumulative tracking -/

/-- The step of cumulative tracking: if the arm `b` played at round `k` minimizes
`N_a(k) / ∑_{s ≤ k} p s a` (in cross-multiplied form), then `N_b(k) ≤ ∑_{s ≤ k} p s b`. Summing
the inequalities over `a` gives `(k + 1) N_b(k) ≤ k ∑_{s ≤ k} p s b`. -/
private lemma pullCount_action_le_sum_of_cumulativeTracking (p : ℕ → α → ℝ)
    (hp0 : ∀ k a, 0 ≤ p k a) (hp1 : ∀ k, ∑ a, p k a = 1) {k : ℕ}
    (hA : ∀ a, (pullCount A (A k ω) k ω : ℝ) * ∑ s ∈ range (k + 1), p s a ≤
      pullCount A a k ω * ∑ s ∈ range (k + 1), p s (A k ω)) :
    (pullCount A (A k ω) k ω : ℝ) ≤ ∑ s ∈ range (k + 1), p s (A k ω) := by
  have hsum := sum_le_sum fun a (_ : a ∈ univ) ↦ hA a
  rw [← mul_sum, ← sum_mul, ← Nat.cast_sum, sum_pullCount, sum_comm] at hsum
  simp only [hp1, sum_const, card_range, nsmul_eq_mul, mul_one] at hsum
  have hS : 0 ≤ ∑ s ∈ range (k + 1), p s (A k ω) := sum_nonneg fun s _ ↦ hp0 s _
  push_cast at hsum
  nlinarith

/-- **Cumulative tracking, upper bound** [DKM19, Lemma 7]. Let `p k` be a probability vector for
every round `k`. If the arm played at round `k` minimizes `N_a(k) / ∑_{s ≤ k} p s a`, in the
cross-multiplied form `N_{A_k}(k) ∑_{s ≤ k} p s a ≤ N_a(k) ∑_{s ≤ k} p s A_k`, then after every
number `n` of rounds, `N_a(n) ≤ ∑_{s < n} p s a + 1` for every arm `a`. In [DKM19], the first `K`
proportions are the vertices of the simplex, so that the first `K` rounds pull every arm once and
the ratios are defined from round `K` on; the cross-multiplied form needs no such
initialization. -/
theorem pullCount_le_sum_add_one_of_cumulativeTracking (p : ℕ → α → ℝ) (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, (pullCount A (A k ω) k ω : ℝ) * ∑ s ∈ range (k + 1), p s a ≤
      pullCount A a k ω * ∑ s ∈ range (k + 1), p s (A k ω)) (n : ℕ) (a : α) :
    (pullCount A a n ω : ℝ) ≤ ∑ s ∈ range n, p s a + 1 := by
  induction n generalizing a with
  | zero => simp
  | succ k ih =>
    by_cases ha : A k ω = a
    · subst ha
      rw [cast_pullCount_action_add_one]
      linarith [pullCount_action_le_sum_of_cumulativeTracking p hp0 hp1 (hA k)]
    · rw [pullCount_eq_pullCount_of_action_ne ha, sum_range_succ]
      linarith [ih a, hp0 k a]

/-- **Cumulative tracking, lower bound** [DKM19, Lemma 7]. Under the assumptions of
`pullCount_le_sum_add_one_of_cumulativeTracking`, after every number `n` of rounds,
`∑_{s < n} p s a - (K - 1) ≤ N_a(n)` for every arm `a`. -/
theorem sum_sub_le_pullCount_of_cumulativeTracking (p : ℕ → α → ℝ) (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, (pullCount A (A k ω) k ω : ℝ) * ∑ s ∈ range (k + 1), p s a ≤
      pullCount A a k ω * ∑ s ∈ range (k + 1), p s (A k ω)) (n : ℕ) (a : α) :
    ∑ s ∈ range n, p s a - (Fintype.card α - 1) ≤ pullCount A a n ω := by
  -- The excesses of pulls sum to zero, and the excess of every other arm is at most `1`.
  have hsum := sum_pullCount_sub_sum_eq_zero (A := A) (ω := ω) p hp1 n
  rw [← add_sum_erase _ _ (mem_univ a)] at hsum
  have hle : ∑ b ∈ univ.erase a, ((pullCount A b n ω : ℝ) - ∑ s ∈ range n, p s b) ≤
      Fintype.card α - 1 := by
    rw [← card_univ_erase_real a, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact sum_le_sum fun b _ ↦ by
      linarith [pullCount_le_sum_add_one_of_cumulativeTracking p hp0 hp1 hA n b]
  linarith

/-- **Cumulative tracking** [DKM19, Lemma 7]. Under the assumptions of
`pullCount_le_sum_add_one_of_cumulativeTracking`, after every number `n` of rounds,
`|N_a(n) - ∑_{s < n} p s a| ≤ K - 1` for every arm `a`. -/
theorem abs_pullCount_sub_sum_le_of_cumulativeTracking (p : ℕ → α → ℝ) (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, (pullCount A (A k ω) k ω : ℝ) * ∑ s ∈ range (k + 1), p s a ≤
      pullCount A a k ω * ∑ s ∈ range (k + 1), p s (A k ω)) (n : ℕ) (a : α) :
    |(pullCount A a n ω : ℝ) - ∑ s ∈ range n, p s a| ≤ Fintype.card α - 1 := by
  have hlow := sum_sub_le_pullCount_of_cumulativeTracking p hp0 hp1 hA n a
  have hup := pullCount_le_sum_add_one_of_cumulativeTracking p hp0 hp1 hA n a
  rw [abs_le]
  refine ⟨by linarith, ?_⟩
  rcases Nat.lt_or_ge 1 (Fintype.card α) with hK | hK
  · have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast Nat.succ_le_of_lt hK
    linarith
  · -- With a single arm, it is played at every round.
    have hK1 : Fintype.card α = 1 := le_antisymm hK (Fintype.card_pos_iff.2 ⟨a⟩)
    have he : univ.erase a = ∅ := by
      rw [← card_eq_zero, card_erase_of_mem (mem_univ a), card_univ, hK1]
    have hsum := sum_pullCount_sub_sum_eq_zero (A := A) (ω := ω) p hp1 n
    rw [← add_sum_erase _ _ (mem_univ a), he, sum_empty, add_zero] at hsum
    rw [hK1, hsum]
    simp

/-- **Proportions of pulls of cumulative tracking.** Under the assumptions of
`pullCount_le_sum_add_one_of_cumulativeTracking`, the difference between the proportion of pulls
`N_a(n) / n` and the average `n⁻¹ ∑_{s < n} p s a` of the proportions tends to `0`. -/
theorem tendsto_pullCount_div_sub_inv_mul_sum_of_cumulativeTracking (p : ℕ → α → ℝ)
    (hp0 : ∀ k a, 0 ≤ p k a) (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, (pullCount A (A k ω) k ω : ℝ) * ∑ s ∈ range (k + 1), p s a ≤
      pullCount A a k ω * ∑ s ∈ range (k + 1), p s (A k ω)) (a : α) :
    Tendsto (fun n : ℕ ↦ (pullCount A a n ω : ℝ) / n - (n : ℝ)⁻¹ * ∑ s ∈ range n, p s a) atTop
      (𝓝 0) :=
  tendsto_pullCount_div_sub_inv_mul_sum_of_abs_le
    (abs_pullCount_sub_sum_le_of_cumulativeTracking p hp0 hp1 hA · a)
    (tendsto_const_div_atTop_nhds_zero_nat _)

/-- **Convergence of the proportions of pulls of cumulative tracking.** Under the assumptions of
`pullCount_le_sum_add_one_of_cumulativeTracking`, if the proportions `p k a` converge to `l a`,
then the proportions of pulls `N_a(n) / n` converge to `l a`. -/
theorem tendsto_pullCount_div_of_cumulativeTracking (p : ℕ → α → ℝ) {l : α → ℝ}
    (hp0 : ∀ k a, 0 ≤ p k a) (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, (pullCount A (A k ω) k ω : ℝ) * ∑ s ∈ range (k + 1), p s a ≤
      pullCount A a k ω * ∑ s ∈ range (k + 1), p s (A k ω)) {a : α}
    (hp : Tendsto (fun k ↦ p k a) atTop (𝓝 (l a))) :
    Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) :=
  tendsto_pullCount_div_of_abs_sub_sum_le
    (abs_pullCount_sub_sum_le_of_cumulativeTracking p hp0 hp1 hA · a)
    (tendsto_const_div_atTop_nhds_zero_nat _) hp

/-! ### Cumulated targets along a history -/

section CumulatedTargets

omit [Fintype α] [DecidableEq α]

variable {𝓞 𝓨 : Type*} {v : (n : ℕ) → Hist 𝓞 α 𝓨 n → α → ℝ}

/-- The cumulated targets `∑_{s ≤ n} v_a(s)` of the target rule `v` after `n` rounds with history
`h`, where `v(s)` is the target `v s` of the prefix of length `s` of `h` (for `s = n`, of `h`
itself). C-tracking and cumulative tracking compare these sums with the pull counts. -/
noncomputable def cumulatedTargets (v : (n : ℕ) → Hist 𝓞 α 𝓨 n → α → ℝ) (n : ℕ)
    (h : Hist 𝓞 α 𝓨 n) (a : α) : ℝ :=
  ∑ s : Fin (n + 1), v s (fun i ↦ h (Fin.castLE (Nat.lt_succ_iff.1 s.isLt) i)) a

/-- The cumulated targets, unfolded. -/
lemma cumulatedTargets_def (v : (n : ℕ) → Hist 𝓞 α 𝓨 n → α → ℝ) (n : ℕ) (h : Hist 𝓞 α 𝓨 n)
    (a : α) :
    cumulatedTargets v n h a =
      ∑ s : Fin (n + 1), v s (fun i ↦ h (Fin.castLE (Nat.lt_succ_iff.1 s.isLt) i)) a :=
  (rfl)

/-- Along a sequence of rounds, the cumulated targets at the history of the first `k` rounds are
`∑_{s ≤ k} v_a(s)`, with `v(s)` the target of the history of the first `s` rounds. -/
lemma cumulatedTargets_history (O : ℕ → Ω → 𝓞) (A : ℕ → Ω → α) (Y : ℕ → Ω → 𝓨) (k : ℕ) (ω : Ω)
    (a : α) :
    cumulatedTargets v k (history O A Y k ω) a =
      ∑ s ∈ range (k + 1), v s (history O A Y s ω) a := by
  rw [cumulatedTargets_def, ← Fin.sum_univ_eq_sum_range (fun s ↦ v s (history O A Y s ω) a)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [history_eq_comp_history (Nat.lt_succ_iff.1 s.isLt), Function.comp_apply]

/-- The cumulated targets are a measurable function of the history if the target rule is. -/
@[fun_prop]
lemma measurable_cumulatedTargets [MeasurableSpace 𝓞] [MeasurableSpace α] [MeasurableSpace 𝓨]
    {n : ℕ} (hv : ∀ n, Measurable (v n)) : Measurable (cumulatedTargets v n) :=
  Measurable.of_eval fun a ↦ Finset.measurable_sum _ fun s _ ↦ (measurable_pi_apply a).comp
    ((hv s).comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _))

end CumulatedTargets

end LMLExplore.Identification
