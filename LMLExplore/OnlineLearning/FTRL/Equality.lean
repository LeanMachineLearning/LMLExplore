/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.OnlineLearning.Regret
public import LMLExplore.Order.Filter.Extr

/-!
# The FTRL equality

The regret analysis of follow the regularized leader (FTRL) rests on an equality that needs no
structure at all: for regularizers and losses `ψ ℓ : ℕ → α → ℝ` on an arbitrary type `α`, with
objectives `F t = ψ t + ∑ s < t, ℓ s`, and any points `x`, the regret of `x` is
`ψ n u - ψ 0 (x 0)` plus the stability terms `F t (x t) - F (t + 1) (x (t + 1)) + ℓ t (x t)` plus
`F n (x n) - F n u` [Ora, Lemma 7.1]. It holds for nonconvex losses, and the last term is
nonpositive when `x n` minimizes `F n` over a set containing `u`. FTRL plays at round `t` a
minimizer of `F t`. Adding a constant to the regularizer `ψ t` adds it to `F t`, which changes no
play by `isMinOn_add_const_iff` [Ora, Remark 7.3], so the bounds may use `ψ t - c t` in place of
`ψ t`, for instance with `c t` the minimum of `ψ t`.

The bounds of FTRL for linear losses on a normed space, in
`LMLExplore.OnlineLearning.FTRL.Basic`, are derived from this equality.

## Main statements

* `regret_eq_ftrl`: the **FTRL equality** [Ora, Lemma 7.1], on an arbitrary type and for arbitrary
  losses, regularizers and points. The regret on the left may be that of other points than the
  points of the stability terms [Ora, Remark 7.4].
* `regret_le_ftrl`: the FTRL inequality, when the last point does at least as well as the
  comparator on the last objective.
* `sum_le_of_isMinOn_sum`: the **be-the-leader lemma** [Ora, Lemma 1.2]: the minimizers of the
  cumulative losses including the current round have nonpositive regret.
* `regret_le_sum_sub_of_isMinOn_sum`: the regret of follow-the-leader is at most
  `∑ t < n, (ℓ t (x t) - ℓ t (x (t + 1)))`.

## Implementation notes

The telescoping proof of the FTRL equality is adapted from the LMLPapers project (same author),
where the FTRL lemma is stated for gains on the probability simplex; here it holds for losses on
any type.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/
public section

open Finset

namespace LMLExplore.OnlineLearning

variable {α : Type*}

/-- **The FTRL equality** [Ora, Lemma 7.1 and Remark 7.4]. Let `ψ ℓ : ℕ → α → ℝ` be regularizers
and losses on an arbitrary type `α`, let `F t = ψ t + ∑ s < t, ℓ s` be the objective of round `t`,
and let `x z : ℕ → α` be any points. Then the regret of `z` against `u` after `n` rounds is
`ψ n u - ψ 0 (x 0) + ∑ t < n, (F t (x t) - F (t + 1) (x (t + 1)) + ℓ t (z t))
  + (F n (x n) - F n u)`.
For `z = x` this is the regret of `x` [Ora, Lemma 7.1]. With `x t` the plays of FTRL, a minimizer
of `F t`, and `z t` the plays of another algorithm, it expresses the regret of that algorithm
through the FTRL plays [Ora, Remark 7.4]. No convexity and no minimality is needed. -/
theorem regret_eq_ftrl (ψ ℓ : ℕ → α → ℝ) (x z : ℕ → α) (u : α) (n : ℕ) :
    regret ℓ z u n = ψ n u - ψ 0 (x 0) +
      ∑ t ∈ range n, ((ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) -
        (ψ (t + 1) (x (t + 1)) + ∑ s ∈ range (t + 1), ℓ s (x (t + 1))) + ℓ t (z t)) +
      ((ψ n (x n) + ∑ s ∈ range n, ℓ s (x n)) - (ψ n u + ∑ s ∈ range n, ℓ s u)) := by
  -- the values of the objectives at the points telescope
  have h_tele := sum_range_sub' (fun t ↦ ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) n
  simp only [range_zero, sum_empty, add_zero] at h_tele
  rw [regret_eq_sum_sub_sum, sum_add_distrib, h_tele]
  ring

/-- **The FTRL inequality** [Ora, Lemma 7.1]. Let `F t = ψ t + ∑ s < t, ℓ s` be the objective of
round `t` and let `x n` do at least as well as `u` on `F n`, for instance a minimizer of `F n` over
a set containing `u`. Then for any points `z`, the regret of `z` against `u` after `n` rounds is at
most `ψ n u - ψ 0 (x 0) + ∑ t < n, (F t (x t) - F (t + 1) (x (t + 1)) + ℓ t (z t))`. -/
theorem regret_le_ftrl (ψ ℓ : ℕ → α → ℝ) (x z : ℕ → α) {u : α} {n : ℕ}
    (hx : ψ n (x n) + ∑ s ∈ range n, ℓ s (x n) ≤ ψ n u + ∑ s ∈ range n, ℓ s u) :
    regret ℓ z u n ≤ ψ n u - ψ 0 (x 0) +
      ∑ t ∈ range n, ((ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) -
        (ψ (t + 1) (x (t + 1)) + ∑ s ∈ range (t + 1), ℓ s (x (t + 1))) + ℓ t (z t)) := by
  rw [regret_eq_ftrl ψ ℓ x z u n]
  linarith

/-- **Be-the-leader** [Ora, Lemma 1.2, Remark 15.32]. If each `w t`, for `t < n`, lies in `V` and
minimizes over `V` the cumulative loss `∑ s ≤ t, ℓ s` of the rounds up to and including `t`, then
`∑ t < n, ℓ t (w t) ≤ ∑ t < n, ℓ t u` for every `u ∈ V`: the regret of the leaders that know the
current loss is nonpositive. -/
theorem sum_le_of_isMinOn_sum {V : Set α} (ℓ : ℕ → α → ℝ) (w : ℕ → α) {u : α} {n : ℕ}
    (hw : ∀ t < n, w t ∈ V) (hmin : ∀ t < n, IsMinOn (fun a ↦ ∑ s ∈ range (t + 1), ℓ s a) V (w t))
    (hu : u ∈ V) :
    ∑ t ∈ range n, ℓ t (w t) ≤ ∑ t ∈ range n, ℓ t u := by
  have hx : (0 : ℝ) + ∑ s ∈ range n, ℓ s (w (n - 1)) ≤ 0 + ∑ s ∈ range n, ℓ s u := by
    rcases n with _ | n
    · simp
    simpa using isMinOn_iff.mp (hmin n n.lt_succ_self) u hu
  -- the FTRL inequality with no regularizer, the follow-the-leader points `w (t - 1)` in the
  -- stability terms and the be-the-leader points `w t` in the regret
  have h := regret_le_ftrl (fun _ _ ↦ 0) ℓ (fun t ↦ w (t - 1)) w hx
  -- each round compares the leader `w (t - 1)` of the first `t` rounds with `w t` on these rounds
  have h_round : ∀ t ∈ range n, (0 + ∑ s ∈ range t, ℓ s (w (t - 1))) -
      (0 + ∑ s ∈ range (t + 1), ℓ s (w (t + 1 - 1))) + ℓ t (w t) ≤ 0 := by
    intro t ht
    have ht := mem_range.mp ht
    rw [Nat.add_sub_cancel, sum_range_succ]
    rcases t with _ | t
    · simp
    have h_le := isMinOn_iff.mp (hmin t (by omega)) (w (t + 1)) (hw (t + 1) ht)
    simp only [Nat.add_sub_cancel] at h_le ⊢
    linarith
  rw [regret_eq_sum_sub_sum] at h
  linarith [sum_nonpos h_round]

/-- **The regret of follow-the-leader** [Ora, Lemma 1.2 and the proof of Theorem 1.3]. If each
`x (t + 1)`, for `t < n`, lies in `V` and minimizes over `V` the cumulative loss
`∑ s ≤ t, ℓ s`, then the regret of `x` against every `u ∈ V` after `n` rounds is at most
`∑ t < n, (ℓ t (x t) - ℓ t (x (t + 1)))`. The first point `x 0` is arbitrary. -/
theorem regret_le_sum_sub_of_isMinOn_sum {V : Set α} (ℓ : ℕ → α → ℝ) (x : ℕ → α) {u : α}
    {n : ℕ} (hx : ∀ t < n, x (t + 1) ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ∑ s ∈ range (t + 1), ℓ s a) V (x (t + 1))) (hu : u ∈ V) :
    regret ℓ x u n ≤ ∑ t ∈ range n, (ℓ t (x t) - ℓ t (x (t + 1))) := by
  have h := sum_le_of_isMinOn_sum ℓ (fun t ↦ x (t + 1)) hx hmin hu
  rw [regret_eq_sum_sub_sum, sum_sub_distrib]
  linarith

end LMLExplore.OnlineLearning
