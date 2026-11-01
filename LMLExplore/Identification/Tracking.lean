/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.FiniteActions
public import Mathlib.Analysis.Real.Sqrt

/-!
# Tracking lemmas

A *tracking* sampling rule plays, at each round, the arm whose number of pulls lags the most
behind a target, so that the empirical proportions of pulls follow a sequence of target
allocations. Track-and-Stop tracks the optimal allocations `w*(μ̂(t))` at the empirical means,
either through their cumulated sums (C-tracking) or directly, with forced exploration of the arms
that are pulled too rarely (D-tracking). This file contains the deterministic statements behind
these rules: they hold for every sequence of actions `A k ω` (at a fixed `ω`) following the rule,
with `N_a(n) = pullCount A a n ω` the number of pulls of `a` in the rounds `0, …, n - 1` and
`K = Fintype.card α`.

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
* `LMLExplore.Identification.eventually_abs_pullCount_div_sub_le`: for a sublinear threshold `g`,
  if the targets are eventually `ε`-close to `l`, the proportions of pulls are eventually
  `3 (K - 1) ε`-close to `l` [GK16, Lemma 17].
* `LMLExplore.Identification.tendsto_pullCount_div`,
  `LMLExplore.Identification.tendsto_pullCount_div_of_sqrt_sub`: if the targets converge to `l`,
  the proportions of pulls `N_a(n) / n` converge to `l a`, for a sublinear threshold `g` and for
  the threshold `√k - K / 2` of D-tracking.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, Section 3.1 and Appendix B.
-/

public section

open Finset Filter Learning
open scoped Topology

namespace LMLExplore.Identification

variable {α Ω : Type*} [Fintype α] [DecidableEq α] {A : ℕ → Ω → α} {ω : Ω}

omit [Fintype α] in
/-- `pullCount_add_one` for the real-valued numbers of pulls. -/
private lemma pullCount_add_one_real (a : α) (k : ℕ) :
    (pullCount A a (k + 1) ω : ℝ) = pullCount A a k ω + if A k ω = a then 1 else 0 := by
  rw [pullCount_add_one]
  split_ifs <;> simp

omit [Fintype α] in
/-- `pullCount_action_eq_pullCount_add_one` for the real-valued numbers of pulls. -/
private lemma pullCount_action_add_one_real (k : ℕ) :
    (pullCount A (A k ω) (k + 1) ω : ℝ) = pullCount A (A k ω) k ω + 1 := by
  exact_mod_cast pullCount_action_eq_pullCount_add_one k ω

/-! ### Tracking a cumulated sum of proportions -/

/-- The sum of the positive parts of the deficits `∑_{s < n} p s a - N_a(n)` stays at most
`K - 1` along the tracking rule of `abs_pullCount_sub_sum_le`. -/
private lemma sum_max_sum_sub_pullCount_le (p : ℕ → α → ℝ) (hp0 : ∀ k a, 0 ≤ p k a)
    (hp1 : ∀ k, ∑ a, p k a = 1)
    (hA : ∀ k a, ∑ s ∈ range (k + 1), p s a - pullCount A a k ω ≤
      ∑ s ∈ range (k + 1), p s (A k ω) - pullCount A (A k ω) k ω) (n : ℕ) :
    ∑ a, max (∑ s ∈ range n, p s a - pullCount A a n ω) 0 ≤ Fintype.card α - 1 := by
  have hK : (1 : ℝ) ≤ Fintype.card α := by
    have : Nonempty α := ⟨A 0 ω⟩
    exact_mod_cast Fintype.card_pos
  induction n with
  | zero => simpa using hK
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
            rw [pullCount_add_one_real, sum_range_succ]
            split_ifs with hba
            · subst hba
              rw [pullCount_action_add_one_real, sum_range_succ] at hb
              exact max_le (by linarith) (by linarith)
            · have hle' := le_max_right (∑ s ∈ range k, p s a - pullCount A a k ω) 0
              exact max_le (by linarith) (by linarith [hp0 k a])
        _ = ∑ a, max (∑ s ∈ range k, p s a - pullCount A a k ω) 0 := by
            simp [sum_add_distrib, sum_sub_distrib, hp1]
        _ ≤ Fintype.card α - 1 := ih
    · -- The played arm `b` is no longer in deficit, and every other deficit is at most the
      -- deficit of `b` before it was played, which is less than `1`.
      rw [not_le, pullCount_action_add_one_real] at hb
      rw [← add_sum_erase _ _ (mem_univ b)]
      have hb0 : max (∑ s ∈ range (k + 1), p s b - pullCount A b (k + 1) ω) 0 = 0 := by
        rw [pullCount_action_add_one_real]
        exact max_eq_right (by linarith)
      have hcard : ((univ.erase b).card : ℝ) = Fintype.card α - 1 := by
        rw [card_erase_of_mem (mem_univ b), card_univ, Nat.cast_pred (by exact_mod_cast hK)]
      rw [hb0, zero_add, ← hcard, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
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
  have hsum : ∑ b, f b = 0 := by
    simp only [hf, sum_sub_distrib, ← Nat.cast_sum, sum_pullCount]
    rw [sum_comm]
    simp [hp1]
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
    have hZ : ∀ j, (univ.filter fun a ↦ pullCount A a (t + 1 + j) ω ≤ c).card ≤
        Fintype.card α - j := by
      intro j
      induction j with
      | zero => simpa using card_filter_le univ _
      | succ j ihj =>
        rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega]
        have hs : t + 1 ≤ t + 1 + j := by omega
        generalize t + 1 + j = s at ihj hs ⊢
        by_cases hex : ∃ b, pullCount A b s ω ≤ c
        · obtain ⟨b, hb⟩ := hex
          have hbc : pullCount A b s ω = c := le_antisymm hb (hc s hs b)
          have hAs : pullCount A (A s ω) s ω ≤ c :=
            hbc ▸ hA s b (by rw [hbc]; exact ht'.trans_le (hg_mono hs))
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
  -- `E b k` is the excess of pulls of `b` after `k` rounds; the excesses sum to zero.
  set E : α → ℕ → ℝ := fun b k ↦ (pullCount A b k ω : ℝ) - k * l b with hE
  have hsum k : ∑ b, E b k = 0 := by
    simp only [hE, sum_sub_distrib, ← Nat.cast_sum, sum_pullCount, ← mul_sum, hl1, mul_one,
      sub_self]
  have : Nonempty α := ⟨a⟩
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hw n₀ le_rfl a)
  -- From round `n₀` on, the arm played at round `k` has excess at most `2 ε k`.
  have h15 k (hk : n₀ ≤ k) : E (A k ω) k ≤ 2 * ε * k := by
    have hkl := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hl0 (A k ω))
    by_cases hU : ∃ b, (pullCount A b k ω : ℝ) < g k
    · obtain ⟨b, hb⟩ := hU
      have : (pullCount A (A k ω) k ω : ℝ) ≤ pullCount A b k ω := by
        exact_mod_cast hforced k hk b hb
      simp only [hE]
      linarith [hg k hk]
    · simp only [not_exists, not_lt] at hU
      obtain ⟨j, -, hj⟩ := exists_le_of_sum_le univ_nonempty
        (show ∑ b, E b k ≤ ∑ _b : α, (0 : ℝ) by simp [hsum])
      have htj := htrack k hk hU j
      have hk0 := Nat.cast_nonneg (α := ℝ) k
      have h1 := mul_le_mul_of_nonneg_left (abs_le.1 (hw k hk j)).1 hk0
      have h2 := mul_le_mul_of_nonneg_left (abs_le.1 (hw k hk (A k ω))).2 hk0
      simp only [hE] at hj ⊢
      nlinarith
  -- Hence the excess of every arm stays below `max(n₀, 2 ε k + 1)`.
  have hup b : ∀ m, E b (n₀ + m) ≤ max (n₀ : ℝ) (2 * ε * (n₀ + m : ℕ) + 1) := by
    intro m
    induction m with
    | zero =>
      refine le_max_of_le_left ?_
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n₀) (hl0 b)
      have : (pullCount A b n₀ ω : ℝ) ≤ n₀ := by exact_mod_cast pullCount_le b n₀ ω
      simp only [hE, add_zero]
      linarith
    | succ m ih =>
      have hk : n₀ ≤ n₀ + m := by omega
      have hrec : E b (n₀ + (m + 1)) =
          E b (n₀ + m) + (if A (n₀ + m) ω = b then 1 else 0) - l b := by
        simp only [hE, ← add_assoc, pullCount_add_one_real]
        push_cast
        ring
      have hmono : max (n₀ : ℝ) (2 * ε * (n₀ + m : ℕ) + 1) ≤
          max (n₀ : ℝ) (2 * ε * (n₀ + (m + 1) : ℕ) + 1) := by
        gcongr
        omega
      rw [hrec]
      split_ifs with hb
      · have := h15 _ hk
        rw [hb] at this
        refine le_max_of_le_right ?_
        push_cast at this ⊢
        nlinarith [hl0 b]
      · linarith [hl0 b]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  set M := max (n₀ : ℝ) (2 * ε * (n₀ + m : ℕ) + 1)
  have hM : 0 ≤ M := le_max_of_le_left (Nat.cast_nonneg _)
  have hcard : ((univ.erase a).card : ℝ) = Fintype.card α - 1 := by
    rw [card_erase_of_mem (mem_univ a), card_univ, Nat.cast_pred Fintype.card_pos]
  have hrest := hsum (n₀ + m)
  rw [← add_sum_erase _ _ (mem_univ a)] at hrest
  have hE_eq : (pullCount A a (n₀ + m) ω : ℝ) - (n₀ + m : ℕ) * l a = E a (n₀ + m) := rfl
  rw [hE_eq, ← hcard, abs_le]
  constructor
  · -- The excess of `a` is minus the excess of the other arms, each at most `M`.
    have : ∑ b ∈ univ.erase a, E b (n₀ + m) ≤ ∑ _b ∈ univ.erase a, M :=
      sum_le_sum fun b _ ↦ hup b m
    rw [sum_const, nsmul_eq_mul] at this
    linarith
  · rcases (univ.erase a).eq_empty_or_nonempty with h | h
    · rw [h, sum_empty, add_zero] at hrest
      simp [h, hrest]
    · have : (1 : ℝ) ≤ (univ.erase a).card := by exact_mod_cast h.card_pos
      calc E a (n₀ + m) ≤ M := hup a m
        _ ≤ (univ.erase a).card * M := le_mul_of_one_le_left hM this

/-- **Tracking a changing sequence of targets**, the second part of [GK16, Lemma 17]. Let `l` be
a probability vector and `g` a sublinear exploration threshold (`g k ≤ c k` eventually, for every
`c > 0`). Suppose that the arm played at round `k` has been pulled at most as often as every arm
`a` in deficit (`N_a(k) < g k`), and, if no arm is in deficit, maximizes `k w k a - N_a(k)`. If
the targets `w k` are eventually `ε`-close to `l`, then the proportions of pulls are eventually
`3 (K - 1) ε`-close to `l`. -/
theorem eventually_abs_pullCount_div_sub_le {g : ℕ → ℝ} {w : ℕ → α → ℝ} {l : α → ℝ} {ε : ℝ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ k a, (pullCount A a k ω : ℝ) < g k →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ k, (∀ a, g k ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hg : ∀ c > 0, ∀ᶠ k in atTop, g k ≤ c * k) (hε : 0 < ε)
    (hw : ∀ᶠ k in atTop, ∀ a, |w k a - l a| ≤ ε) :
    ∀ᶠ n in atTop, ∀ a, |(pullCount A a n ω : ℝ) / n - l a| ≤ 3 * (Fintype.card α - 1) * ε := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hw.and (hg (2 * ε) (by positivity)))
  have hK : (1 : ℝ) ≤ Fintype.card α := by
    have : Nonempty α := ⟨A 0 ω⟩
    exact_mod_cast Fintype.card_pos
  filter_upwards [eventually_ge_atTop n₀, eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop ((n₀ : ℝ) / (3 * ε)),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 / ε)] with n hn hn1 hn₀' hn1' a
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h := abs_pullCount_sub_mul_le hl0 hl1 (fun k _ ↦ hforced k) (fun k _ ↦ htrack k)
    (fun k hk ↦ (hn₀ k hk).1) (fun k hk ↦ (hn₀ k hk).2) hn a
  -- `max(n₀, 2 ε n + 1) ≤ 3 ε n` for `n ≥ n₀ / (3 ε)` and `n ≥ 1 / ε`.
  have hmax : max (n₀ : ℝ) (2 * ε * n + 1) ≤ 3 * ε * n := by
    rw [div_le_iff₀ (by positivity)] at hn₀'
    rw [div_le_iff₀ hε] at hn1'
    exact max_le (by linarith) (by linarith)
  rw [show (pullCount A a n ω : ℝ) / n - l a = ((pullCount A a n ω : ℝ) - n * l a) / n by
    field_simp, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  calc |(pullCount A a n ω : ℝ) - n * l a| ≤ (Fintype.card α - 1) * max (n₀ : ℝ) (2 * ε * n + 1) :=
        h
    _ ≤ (Fintype.card α - 1) * (3 * ε * n) := by gcongr
    _ = 3 * (Fintype.card α - 1) * ε * n := by ring

/-- **Convergence of the proportions of pulls**, a consequence of [GK16, Lemma 17]. Let `l` be a
probability vector and `g` a sublinear exploration threshold (`g k ≤ c k` eventually, for every
`c > 0`). Suppose that the arm played at round `k` has been pulled at most as often as every arm
`a` in deficit (`N_a(k) < g k`), and, if no arm is in deficit, maximizes `k w k a - N_a(k)`. If
the targets `w k` converge to `l`, then the proportions of pulls `N_a(n) / n` converge to
`l a`. -/
theorem tendsto_pullCount_div {g : ℕ → ℝ} {w : ℕ → α → ℝ} {l : α → ℝ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ k a, (pullCount A a k ω : ℝ) < g k →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ k, (∀ a, g k ≤ pullCount A a k ω) → ∀ a,
      k * w k a - pullCount A a k ω ≤ k * w k (A k ω) - pullCount A (A k ω) k ω)
    (hg : ∀ c > 0, ∀ᶠ k in atTop, g k ≤ c * k)
    (hw : ∀ a, Tendsto (fun k ↦ w k a) atTop (𝓝 (l a))) (a : α) :
    Tendsto (fun n ↦ (pullCount A a n ω : ℝ) / n) atTop (𝓝 (l a)) := by
  have hK : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨a⟩
    exact_mod_cast Fintype.card_pos
  refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε > 0, 3 * Fintype.card α * ε = δ :=
    ⟨δ / (3 * Fintype.card α), by positivity, by field_simp⟩
  have hw' : ∀ᶠ k in atTop, ∀ b, |w k b - l b| ≤ ε := eventually_all.2 fun b ↦
    (Metric.tendsto_nhds.1 (hw b) ε hε).mono fun k hk ↦ (Real.dist_eq _ _ ▸ hk).le
  filter_upwards [eventually_abs_pullCount_div_sub_le hl0 hl1 hforced htrack hg hε hw'] with n hn
  rw [Real.dist_eq]
  linarith [hn a]

/-- **Convergence of the proportions of pulls of D-tracking**, the limit form of the second part
of [GK16, Lemma 8]. Let `l` be a probability vector. Suppose that the arm played at round `k` has
been pulled at most as often as every arm `a` with `N_a(k) < √k - K / 2`, and, if there is no such
arm, maximizes `k w k a - N_a(k)`. If the targets `w k` converge to `l`, then the proportions of
pulls `N_a(n) / n` converge to `l a`. -/
theorem tendsto_pullCount_div_of_sqrt_sub {w : ℕ → α → ℝ} {l : α → ℝ}
    (hl0 : ∀ a, 0 ≤ l a) (hl1 : ∑ a, l a = 1)
    (hforced : ∀ k a, (pullCount A a k ω : ℝ) < √(k : ℝ) - Fintype.card α / 2 →
      pullCount A (A k ω) k ω ≤ pullCount A a k ω)
    (htrack : ∀ k : ℕ, (∀ a, √(k : ℝ) - Fintype.card α / 2 ≤ pullCount A a k ω) → ∀ a,
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

end LMLExplore.Identification
