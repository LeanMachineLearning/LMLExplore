/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Regret notions of online learning

In online learning, a learner plays `x t` in a set `α` at each round `t = 0, 1, …`, and then
suffers the loss `ℓ t (x t)` of a loss function `ℓ t : α → ℝ` chosen by an adversary. This file
defines the ways of comparing the cumulative loss of the learner with that of comparators
[Ora, Chapter 1 and Chapter 14]. The losses and the plays are arbitrary sequences: no convexity is
needed, and every statement holds for losses chosen adaptively from the past plays.

* The **regret** `regret ℓ x u n = ∑ t < n, (ℓ t (x t) - ℓ t u)` against a fixed comparator `u`
  after `n` rounds. For linear losses `y t` on a vector space, it is
  `∑ t < n, y t (x t - u)` (`regret_eq_sum_apply_sub`).
* The **dynamic regret** `dynRegret ℓ x u n = ∑ t < n, (ℓ t (x t) - ℓ t (u t))` against a sequence
  of comparators `u` [Ora, Definition 14.1]. Against a constant sequence it is the regret
  (`dynRegret_const`).
* The **interval regret** `intervalRegret ℓ x u s τ`, the regret against `u` on the `τ` rounds
  `s, …, s + τ - 1`. It is the regret of the shifted sequences of losses and plays
  (`intervalRegret_eq_regret`), and the regret over consecutive intervals is the sum of the
  interval regrets (`intervalRegret_add_intervalRegret`, `regret_add_intervalRegret`). The
  dynamic regret against a sequence of comparators that is constant on each of consecutive
  intervals is the sum of the interval regrets against these constants
  (`dynRegret_eq_sum_intervalRegret`).
* The **strongly adaptive regret** `stronglyAdaptiveRegret ℓ x U τ n`, the supremum of the regrets
  on the intervals of `τ` rounds within the horizon `n` against the comparators in `U`
  [Ora, Definition 14.7]. For `U = {u}` it is the strongly adaptive regret against `u` of [Ora].
* The **tracking regret** `trackingRegret ℓ x U m n`, the supremum of the dynamic regrets against
  the sequences of comparators in `U` that switch at most `m` times within the horizon
  [Ora, Definition 14.13]. The number of switches of a sequence `u` within the horizon `n` is
  `numSwitches u n`.
* The **path length** `pathLength u n = ∑ t < n - 1, ‖u (t + 1) - u t‖` of a sequence of
  comparators in a normed group [Ora, Section 14.1]. A sequence with at most `m` switches in a
  bounded set `S` has path length at most `m * diam S` (`pathLength_le_mul_diam`), so that dynamic
  regret bounds in terms of the path length bound the tracking regret.

The strongly adaptive and tracking regrets are suprema of unbounded families of real numbers, and
take values in `EReal`; they are characterized by `stronglyAdaptiveRegret_le_iff` and
`trackingRegret_le_iff`, which express a bound on them as a bound on every interval regret, or on
every dynamic regret, in the supremum.

## Main definitions

* `LMLExplore.OnlineLearning.regret ℓ x u n`: the regret of the plays `x` against `u`.
* `LMLExplore.OnlineLearning.dynRegret ℓ x u n`: the dynamic regret against the sequence `u`.
* `LMLExplore.OnlineLearning.intervalRegret ℓ x u s τ`: the regret on the rounds `[s, s + τ)`.
* `LMLExplore.OnlineLearning.stronglyAdaptiveRegret ℓ x U τ n`: the strongly adaptive regret.
* `LMLExplore.OnlineLearning.numSwitches u n`: the number of rounds `t + 1 < n` with
  `u (t + 1) ≠ u t`.
* `LMLExplore.OnlineLearning.trackingRegret ℓ x U m n`: the tracking regret.
* `LMLExplore.OnlineLearning.pathLength u n`: the path length of `u`.

## Main statements

* `regret_add`, `dynRegret_add`, `intervalRegret_add`: the regrets are additive in the losses.
* `dynRegret_const`: the dynamic regret against a constant sequence is the regret.
* `regret_add_intervalRegret`, `intervalRegret_add_intervalRegret`: the regret over consecutive
  intervals is the sum of the interval regrets.
* `dynRegret_eq_sum_intervalRegret`: the dynamic regret against a sequence that is constant on each
  of consecutive intervals is the sum of the interval regrets.
* `pathLength_le_numSwitches_mul`: a sequence whose steps have norm at most `D` has path length at
  most `numSwitches u n * D`.
* `pathLength_le_mul_diam`: a sequence with at most `m` switches in a bounded set `S` has path
  length at most `m * diam S`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {α : Type*} {ℓ ℓ' : ℕ → α → ℝ} {x : ℕ → α} {u : α} {n : ℕ}

section Regret

/-- The **regret** after `n` rounds of the plays `x` against the comparator `u`, for the losses
`ℓ`: `∑ t < n, (ℓ t (x t) - ℓ t u)` [Ora, Section 1.1]. -/
def regret (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, (ℓ t (x t) - ℓ t u)

lemma regret_def (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (n : ℕ) :
    regret ℓ x u n = ∑ t ∈ range n, (ℓ t (x t) - ℓ t u) := (rfl)

@[simp]
lemma regret_zero (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) : regret ℓ x u 0 = 0 := by
  simp [regret_def]

lemma regret_succ (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (n : ℕ) :
    regret ℓ x u (n + 1) = regret ℓ x u n + (ℓ n (x n) - ℓ n u) := by
  rw [regret_def, regret_def, sum_range_succ]

/-- The regret against a comparator is the difference of the cumulative losses. -/
lemma regret_eq_sum_sub_sum (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (n : ℕ) :
    regret ℓ x u n = ∑ t ∈ range n, ℓ t (x t) - ∑ t ∈ range n, ℓ t u := by
  simp [regret_def, sum_sub_distrib]

/-- The regret is additive in the losses. -/
lemma regret_add (ℓ ℓ' : ℕ → α → ℝ) (x : ℕ → α) (u : α) (n : ℕ) :
    regret (ℓ + ℓ') x u n = regret ℓ x u n + regret ℓ' x u n := by
  simp only [regret_def, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ ↦ by ring

/-- The regret is homogeneous in the losses. -/
lemma regret_smul (c : ℝ) (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (n : ℕ) :
    regret (c • ℓ) x u n = c * regret ℓ x u n := by
  simp only [regret_def, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ ↦ by ring

/-- For linear losses `y t`, the regret is `∑ t < n, y t (x t - u)`. -/
lemma regret_eq_sum_apply_sub {E F : Type*} [AddCommGroup E] [FunLike F E ℝ]
    [AddMonoidHomClass F E ℝ] (y : ℕ → F) (x : ℕ → E) (u : E) (n : ℕ) :
    regret (fun t ↦ y t) x u n = ∑ t ∈ range n, y t (x t - u) := by
  simp [regret_def, map_sub]

end Regret

section DynRegret

/-- The **dynamic regret** after `n` rounds of the plays `x` against the sequence of comparators
`u`, for the losses `ℓ`: `∑ t < n, (ℓ t (x t) - ℓ t (u t))` [Ora, Definition 14.1]. -/
def dynRegret (ℓ : ℕ → α → ℝ) (x u : ℕ → α) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, (ℓ t (x t) - ℓ t (u t))

lemma dynRegret_def (ℓ : ℕ → α → ℝ) (x u : ℕ → α) (n : ℕ) :
    dynRegret ℓ x u n = ∑ t ∈ range n, (ℓ t (x t) - ℓ t (u t)) := (rfl)

@[simp]
lemma dynRegret_zero (ℓ : ℕ → α → ℝ) (x u : ℕ → α) : dynRegret ℓ x u 0 = 0 := by
  simp [dynRegret_def]

lemma dynRegret_succ (ℓ : ℕ → α → ℝ) (x u : ℕ → α) (n : ℕ) :
    dynRegret ℓ x u (n + 1) = dynRegret ℓ x u n + (ℓ n (x n) - ℓ n (u n)) := by
  rw [dynRegret_def, dynRegret_def, sum_range_succ]

/-- The dynamic regret against a constant sequence of comparators is the regret. -/
@[simp]
lemma dynRegret_const (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (n : ℕ) :
    dynRegret ℓ x (fun _ ↦ u) n = regret ℓ x u n := by
  rw [dynRegret_def, regret_def]

/-- The dynamic regret depends only on the comparators of the first `n` rounds. -/
lemma dynRegret_congr {u v : ℕ → α} (h : ∀ t < n, u t = v t) :
    dynRegret ℓ x u n = dynRegret ℓ x v n := by
  simp only [dynRegret_def]
  exact sum_congr rfl fun t ht ↦ by rw [h t (mem_range.mp ht)]

/-- The dynamic regret is additive in the losses. -/
lemma dynRegret_add (ℓ ℓ' : ℕ → α → ℝ) (x u : ℕ → α) (n : ℕ) :
    dynRegret (ℓ + ℓ') x u n = dynRegret ℓ x u n + dynRegret ℓ' x u n := by
  simp only [dynRegret_def, Pi.add_apply, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ ↦ by ring

/-- The dynamic regret is homogeneous in the losses. -/
lemma dynRegret_smul (c : ℝ) (ℓ : ℕ → α → ℝ) (x u : ℕ → α) (n : ℕ) :
    dynRegret (c • ℓ) x u n = c * dynRegret ℓ x u n := by
  simp only [dynRegret_def, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun _ _ ↦ by ring

end DynRegret

section IntervalRegret

/-- The **interval regret** of the plays `x` against the comparator `u` on the `τ` rounds
`s, …, s + τ - 1`, for the losses `ℓ`: `∑ t ∈ [s, s + τ), (ℓ t (x t) - ℓ t u)`. -/
def intervalRegret (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s τ : ℕ) : ℝ :=
  ∑ t ∈ Ico s (s + τ), (ℓ t (x t) - ℓ t u)

lemma intervalRegret_def (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s τ : ℕ) :
    intervalRegret ℓ x u s τ = ∑ t ∈ Ico s (s + τ), (ℓ t (x t) - ℓ t u) := (rfl)

@[simp]
lemma intervalRegret_zero_right (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s : ℕ) :
    intervalRegret ℓ x u s 0 = 0 := by
  simp [intervalRegret_def]

/-- The interval regret on the first `τ` rounds is the regret after `τ` rounds. -/
@[simp]
lemma intervalRegret_zero_left (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (τ : ℕ) :
    intervalRegret ℓ x u 0 τ = regret ℓ x u τ := by
  rw [intervalRegret_def, regret_def, zero_add, Nat.Ico_zero_eq_range]

/-- The interval regret on the rounds `[s, s + τ)` is the regret after `τ` rounds of the losses
and plays shifted by `s`. -/
lemma intervalRegret_eq_regret (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s τ : ℕ) :
    intervalRegret ℓ x u s τ = regret (fun t ↦ ℓ (s + t)) (fun t ↦ x (s + t)) u τ := by
  rw [intervalRegret_def, regret_def, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- The regret over two consecutive intervals is the sum of the interval regrets. -/
lemma intervalRegret_add_intervalRegret (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s τ τ' : ℕ) :
    intervalRegret ℓ x u s τ + intervalRegret ℓ x u (s + τ) τ' =
      intervalRegret ℓ x u s (τ + τ') := by
  simp only [intervalRegret_def]
  rw [← add_assoc, sum_Ico_consecutive _ (by omega) (by omega)]

/-- The regret after `s + τ` rounds is the regret after `s` rounds plus the interval regret on the
rounds `[s, s + τ)`. -/
lemma regret_add_intervalRegret (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s τ : ℕ) :
    regret ℓ x u s + intervalRegret ℓ x u s τ = regret ℓ x u (s + τ) := by
  rw [← intervalRegret_zero_left, ← intervalRegret_zero_left, ← intervalRegret_add_intervalRegret,
    zero_add]

/-- The interval regret is additive in the losses. -/
lemma intervalRegret_add (ℓ ℓ' : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s τ : ℕ) :
    intervalRegret (ℓ + ℓ') x u s τ = intervalRegret ℓ x u s τ + intervalRegret ℓ' x u s τ := by
  simp only [intervalRegret_eq_regret]
  exact regret_add _ _ _ _ _

/-- The interval regret is homogeneous in the losses. -/
lemma intervalRegret_smul (c : ℝ) (ℓ : ℕ → α → ℝ) (x : ℕ → α) (u : α) (s τ : ℕ) :
    intervalRegret (c • ℓ) x u s τ = c * intervalRegret ℓ x u s τ := by
  simp only [intervalRegret_eq_regret]
  exact regret_smul _ _ _ _ _

/-- If the comparators are equal to `v` on the rounds `[s, s + τ)`, the dynamic regret after
`s + τ` rounds is the dynamic regret after `s` rounds plus the interval regret against `v` on
these rounds. -/
lemma dynRegret_add_intervalRegret {u : ℕ → α} {v : α} {s τ : ℕ}
    (hu : ∀ t ∈ Ico s (s + τ), u t = v) :
    dynRegret ℓ x u s + intervalRegret ℓ x v s τ = dynRegret ℓ x u (s + τ) := by
  rw [dynRegret_def, dynRegret_def, intervalRegret_def,
    ← sum_range_add_sum_Ico _ (Nat.le_add_right s τ)]
  congr 1
  exact sum_congr rfl fun t ht ↦ by rw [hu t ht]

/-- The **regret over consecutive intervals**. Let the rounds `[0, b K)` be split into the
consecutive intervals `[b k, b (k + 1))`, `k < K`, and let the comparators `u` be equal to `v k`
on the `k`-th interval. Then the dynamic regret against `u` is the sum of the interval regrets
against the `v k`. -/
theorem dynRegret_eq_sum_intervalRegret {u v : ℕ → α} {b : ℕ → ℕ} {K : ℕ} (hb0 : b 0 = 0)
    (hb : ∀ k < K, b k ≤ b (k + 1)) (hu : ∀ k < K, ∀ t ∈ Ico (b k) (b (k + 1)), u t = v k) :
    dynRegret ℓ x u (b K) = ∑ k ∈ range K, intervalRegret ℓ x (v k) (b k) (b (k + 1) - b k) := by
  induction K with
  | zero => simp [hb0]
  | succ K ih =>
    have hbK := hb K (Nat.lt_succ_self K)
    have h_end : b (K + 1) = b K + (b (K + 1) - b K) := by omega
    rw [sum_range_succ, ← ih (fun k hk ↦ hb k (by omega)) (fun k hk ↦ hu k (by omega)),
      dynRegret_add_intervalRegret fun t ht ↦ hu K (Nat.lt_succ_self K) t (by rwa [h_end]),
      ← h_end]

end IntervalRegret

section StronglyAdaptive

/-- The **strongly adaptive regret** of the plays `x` for the losses `ℓ`, the comparators in `U`,
the interval length `τ` and the horizon `n` [Ora, Definition 14.7]: the supremum, over the
intervals `[s, s + τ)` of `τ` rounds within the first `n` rounds and over the comparators
`u ∈ U`, of the interval regret against `u` on `[s, s + τ)`. It takes values in `EReal`, since
the interval regrets need not be bounded over `U`. For `U = {u}`, it is the strongly adaptive
regret against `u` of [Ora]. -/
noncomputable def stronglyAdaptiveRegret (ℓ : ℕ → α → ℝ) (x : ℕ → α) (U : Set α) (τ n : ℕ) :
    EReal :=
  ⨆ (s : ℕ) (_ : s + τ ≤ n) (u ∈ U), (intervalRegret ℓ x u s τ : EReal)

lemma stronglyAdaptiveRegret_def (ℓ : ℕ → α → ℝ) (x : ℕ → α) (U : Set α) (τ n : ℕ) :
    stronglyAdaptiveRegret ℓ x U τ n =
      ⨆ (s : ℕ) (_ : s + τ ≤ n) (u ∈ U), (intervalRegret ℓ x u s τ : EReal) := (rfl)

/-- The strongly adaptive regret is at most `B` iff the regret on every interval of `τ` rounds
within the horizon against every comparator of `U` is at most `B`. -/
lemma stronglyAdaptiveRegret_le_iff {U : Set α} {τ : ℕ} {B : EReal} :
    stronglyAdaptiveRegret ℓ x U τ n ≤ B ↔
      ∀ s, s + τ ≤ n → ∀ u ∈ U, (intervalRegret ℓ x u s τ : EReal) ≤ B := by
  simp only [stronglyAdaptiveRegret_def, iSup_le_iff]

/-- The regret on an interval of `τ` rounds within the horizon against a comparator of `U` is at
most the strongly adaptive regret. -/
lemma intervalRegret_le_stronglyAdaptiveRegret {U : Set α} {s τ : ℕ} (hs : s + τ ≤ n)
    (hu : u ∈ U) : (intervalRegret ℓ x u s τ : EReal) ≤ stronglyAdaptiveRegret ℓ x U τ n :=
  stronglyAdaptiveRegret_le_iff.mp le_rfl s hs u hu

/-- The strongly adaptive regret is monotone in the set of comparators. -/
lemma stronglyAdaptiveRegret_mono_set {U V : Set α} (hUV : U ⊆ V) (τ : ℕ) :
    stronglyAdaptiveRegret ℓ x U τ n ≤ stronglyAdaptiveRegret ℓ x V τ n :=
  stronglyAdaptiveRegret_le_iff.mpr fun _ hs _ hu ↦
    intervalRegret_le_stronglyAdaptiveRegret hs (hUV hu)

/-- The strongly adaptive regret is monotone in the horizon. -/
lemma stronglyAdaptiveRegret_mono {U : Set α} {τ n' : ℕ} (hn : n ≤ n') :
    stronglyAdaptiveRegret ℓ x U τ n ≤ stronglyAdaptiveRegret ℓ x U τ n' :=
  stronglyAdaptiveRegret_le_iff.mpr fun _ hs _ hu ↦
    intervalRegret_le_stronglyAdaptiveRegret (hs.trans hn) hu

end StronglyAdaptive

section Tracking

/-- The **number of switches** of the sequence `u` within the horizon `n`: the number of rounds
`t` with `t + 1 < n` and `u (t + 1) ≠ u t`. -/
noncomputable def numSwitches (u : ℕ → α) (n : ℕ) : ℕ :=
  open scoped Classical in #{t ∈ range (n - 1) | u (t + 1) ≠ u t}

lemma numSwitches_def [DecidableEq α] (u : ℕ → α) (n : ℕ) :
    numSwitches u n = #{t ∈ range (n - 1) | u (t + 1) ≠ u t} := by
  rw [numSwitches]
  congr

@[simp]
lemma numSwitches_zero (u : ℕ → α) : numSwitches u 0 = 0 := by
  classical
  simp [numSwitches_def]

@[simp]
lemma numSwitches_one (u : ℕ → α) : numSwitches u 1 = 0 := by
  classical
  simp [numSwitches_def]

/-- Extending the horizon by one round adds one switch iff the sequence switches at the last
round. -/
lemma numSwitches_succ [DecidableEq α] (u : ℕ → α) (n : ℕ) :
    numSwitches u (n + 2) = numSwitches u (n + 1) + if u (n + 1) ≠ u n then 1 else 0 := by
  simp [numSwitches_def, card_filter, sum_range_succ]

/-- The number of switches is monotone in the horizon. -/
lemma numSwitches_mono (u : ℕ → α) {n n' : ℕ} (hn : n ≤ n') :
    numSwitches u n ≤ numSwitches u n' := by
  classical
  rw [numSwitches_def, numSwitches_def]
  exact card_le_card (filter_subset_filter _ (range_subset_range.mpr (by omega)))

/-- A constant sequence has no switches. -/
@[simp]
lemma numSwitches_const (u : α) (n : ℕ) : numSwitches (fun _ ↦ u) n = 0 := by
  classical
  simp [numSwitches_def]

/-- A sequence switches at most `n - 1` times within the horizon `n`. -/
lemma numSwitches_le (u : ℕ → α) (n : ℕ) : numSwitches u n ≤ n - 1 := by
  classical
  rw [numSwitches_def]
  exact (card_filter_le _ _).trans (card_range _).le

/-- The **tracking regret** of the plays `x` for the losses `ℓ`, the comparators in `U`, at most
`m` switches and the horizon `n` [Ora, Definition 14.13]: the supremum of the dynamic regrets
after `n` rounds against the sequences of comparators in `U` with at most `m` switches within the
horizon. It takes values in `EReal`, since the dynamic regrets need not be bounded over these
sequences. -/
noncomputable def trackingRegret (ℓ : ℕ → α → ℝ) (x : ℕ → α) (U : Set α) (m n : ℕ) : EReal :=
  ⨆ (u : ℕ → α) (_ : ∀ t < n, u t ∈ U) (_ : numSwitches u n ≤ m), (dynRegret ℓ x u n : EReal)

lemma trackingRegret_def (ℓ : ℕ → α → ℝ) (x : ℕ → α) (U : Set α) (m n : ℕ) :
    trackingRegret ℓ x U m n =
      ⨆ (u : ℕ → α) (_ : ∀ t < n, u t ∈ U) (_ : numSwitches u n ≤ m),
        (dynRegret ℓ x u n : EReal) := (rfl)

/-- The tracking regret is at most `B` iff the dynamic regret against every sequence of
comparators in `U` with at most `m` switches is at most `B`. -/
lemma trackingRegret_le_iff {U : Set α} {m : ℕ} {B : EReal} :
    trackingRegret ℓ x U m n ≤ B ↔
      ∀ u : ℕ → α, (∀ t < n, u t ∈ U) → numSwitches u n ≤ m → (dynRegret ℓ x u n : EReal) ≤ B := by
  simp only [trackingRegret_def, iSup_le_iff]

/-- The dynamic regret against a sequence of comparators in `U` with at most `m` switches is at
most the tracking regret. -/
lemma dynRegret_le_trackingRegret {U : Set α} {m : ℕ} {u : ℕ → α} (hu : ∀ t < n, u t ∈ U)
    (hm : numSwitches u n ≤ m) : (dynRegret ℓ x u n : EReal) ≤ trackingRegret ℓ x U m n :=
  trackingRegret_le_iff.mp le_rfl u hu hm

/-- The regret against a comparator of `U` is at most the tracking regret. -/
lemma regret_le_trackingRegret {U : Set α} (hu : u ∈ U) (m : ℕ) :
    (regret ℓ x u n : EReal) ≤ trackingRegret ℓ x U m n := by
  rw [← dynRegret_const]
  exact dynRegret_le_trackingRegret (fun _ _ ↦ hu) (by simp)

/-- The tracking regret is monotone in the number of switches. -/
lemma trackingRegret_mono {U : Set α} {m m' : ℕ} (hm : m ≤ m') :
    trackingRegret ℓ x U m n ≤ trackingRegret ℓ x U m' n :=
  trackingRegret_le_iff.mpr fun _ hu hum ↦ dynRegret_le_trackingRegret hu (hum.trans hm)

/-- The tracking regret is monotone in the set of comparators. -/
lemma trackingRegret_mono_set {U V : Set α} (hUV : U ⊆ V) (m : ℕ) :
    trackingRegret ℓ x U m n ≤ trackingRegret ℓ x V m n :=
  trackingRegret_le_iff.mpr fun _ hu hum ↦
    dynRegret_le_trackingRegret (fun t ht ↦ hUV (hu t ht)) hum

end Tracking

section PathLength

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The **path length** of the sequence `u` within the horizon `n`:
`∑ t < n - 1, ‖u (t + 1) - u t‖` [Ora, Section 14.1]. -/
def pathLength (u : ℕ → E) (n : ℕ) : ℝ :=
  ∑ t ∈ range (n - 1), ‖u (t + 1) - u t‖

lemma pathLength_def (u : ℕ → E) (n : ℕ) :
    pathLength u n = ∑ t ∈ range (n - 1), ‖u (t + 1) - u t‖ := (rfl)

@[simp]
lemma pathLength_zero (u : ℕ → E) : pathLength u 0 = 0 := by
  simp [pathLength_def]

@[simp]
lemma pathLength_one (u : ℕ → E) : pathLength u 1 = 0 := by
  simp [pathLength_def]

/-- Extending the horizon by one round adds the norm of the last step to the path length. -/
lemma pathLength_succ (u : ℕ → E) (n : ℕ) :
    pathLength u (n + 2) = pathLength u (n + 1) + ‖u (n + 1) - u n‖ := by
  simp [pathLength_def, sum_range_succ]

lemma pathLength_nonneg (u : ℕ → E) (n : ℕ) : 0 ≤ pathLength u n :=
  sum_nonneg fun _ _ ↦ norm_nonneg _

/-- A constant sequence has path length `0`. -/
@[simp]
lemma pathLength_const (u : E) (n : ℕ) : pathLength (fun _ ↦ u) n = 0 := by
  simp [pathLength_def]

/-- If the sequence `u` moves by at most `D` at each round within the horizon `n`, its path length
is at most `D` times its number of switches. -/
theorem pathLength_le_numSwitches_mul {u : ℕ → E} {D : ℝ}
    (hD : ∀ t, t + 1 < n → ‖u (t + 1) - u t‖ ≤ D) :
    pathLength u n ≤ numSwitches u n * D := by
  classical
  -- only the rounds where the sequence switches contribute to the path length
  have h_filter : ∑ t ∈ range (n - 1) with u (t + 1) ≠ u t, ‖u (t + 1) - u t‖ = pathLength u n :=
    sum_filter_of_ne fun t _ ht h_eq ↦ ht (by simp [h_eq])
  rw [← h_filter, numSwitches_def, ← nsmul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun t ht ↦ hD t ?_
  have := (mem_range.mp (mem_filter.mp ht).1)
  omega

/-- A sequence with at most `m` switches within the horizon `n` in a bounded set `S` has path
length at most `m * diam S` [Ora, Section 14.3]. -/
theorem pathLength_le_mul_diam {u : ℕ → E} {S : Set E} {m : ℕ} (hS : Bornology.IsBounded S)
    (hu : ∀ t < n, u t ∈ S) (hm : numSwitches u n ≤ m) :
    pathLength u n ≤ m * Metric.diam S := by
  refine (pathLength_le_numSwitches_mul (D := Metric.diam S) fun t ht ↦ ?_).trans ?_
  · rw [← dist_eq_norm]
    exact Metric.dist_le_diam_of_mem hS (hu _ ht) (hu t (by omega))
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) Metric.diam_nonneg

end PathLength

end LMLExplore.OnlineLearning
