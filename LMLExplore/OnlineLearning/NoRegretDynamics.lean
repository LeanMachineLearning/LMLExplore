/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import LMLExplore.OnlineLearning.Learner.Basic
public import LMLExplore.Optimization.SaddlePoint

/-!
# No-regret dynamics for saddle-point problems

For a payoff `f : E → F → ℝ` convex in its first argument on `X` and concave in its second on `Y`,
let a minimizing player play `xs t ∈ X` and a maximizing player play `ys t ∈ Y` at each round
`t = 0, 1, …`. The minimizing player suffers the losses `f · (ys t)` and the maximizing player the
losses `-f (xs t) ·`. This file bounds the duality gap of the averages of the plays by the regrets
of the two players [Ora, Chapter 15]:

* `sub_le_regret_add_regret_div` [Ora, Theorem 15.12]: for every `x` and `y`, with
  `xa = (∑ t < n, xs t) / n` and `ya = (∑ t < n, ys t) / n`,
  `f xa y - f x ya ≤ (regret^X_n(x) + regret^Y_n(y)) / n`. The plays are arbitrary sequences: no
  property of the algorithms that produce them is used.
* `dualityGap_le_of_regret_le`: hence the duality gap of `(xa, ya)` is at most the sum of bounds on
  the regrets against all comparators, divided by `n`. Neither the gap nor the regrets need be
  attained, and no saddle point need exist.
* `dualityGap_le_of_regret_le_of_le_add` [Ora, Chapter 15]: if the maximizing player plays
  `ε t`-approximate best responses to the plays of the minimizing one, its regret is at most
  `∑ t < n, ε t`, so the gap is at most `(R + ∑ t < n, ε t) / n` for a bound `R` on the regret of
  the minimizing player.
* `OnlineLearner.sub_le_div_of_hasRegretBound` and `OnlineLearner.dualityGap_le_of_hasRegretBound`
  [Ora, Chapter 15]: if two online learners have regret guarantees, the averages of their
  plays against each other (`OnlineLearner.gameRun`) satisfy the bounds above with the
  guarantees in place of the regrets. For learners whose regret grows sublinearly, the averages
  are approximate saddle points (`LMLExplore.isApproxSaddlePointOn_of_dualityGap_le`) of
  vanishing gap.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {X : Set E} {Y : Set F} {f : E → F → ℝ} {xs : ℕ → E} {ys : ℕ → F} {n : ℕ}

/-- **No-regret dynamics** [Ora, Theorem 15.12]. Let the minimizing player play `xs t ∈ X` and the
maximizing player `ys t ∈ Y`, with the losses `f · (ys t)` and `-f (xs t) ·`. If `f · y` is convex
on `X` and `f x` is concave on `Y`, then the average plays `xa = (∑ t < n, xs t) / n` and
`ya = (∑ t < n, ys t) / n` satisfy `f xa y - f x ya ≤ (regret^X_n(x) + regret^Y_n(y)) / n`.
No property of the plays other than membership is used. -/
theorem sub_le_regret_add_regret_div {x : E} {y : F} (hfx : ConvexOn ℝ X fun x ↦ f x y)
    (hfy : ConcaveOn ℝ Y (f x)) (hxs : ∀ t < n, xs t ∈ X) (hys : ∀ t < n, ys t ∈ Y) (hn : 0 < n) :
    f ((n : ℝ)⁻¹ • ∑ t ∈ range n, xs t) y - f x ((n : ℝ)⁻¹ • ∑ t ∈ range n, ys t) ≤
      (regret (fun t a ↦ f a (ys t)) xs x n + regret (fun t b ↦ -f (xs t) b) ys y n) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hw₀ : ∀ t ∈ range n, (0 : ℝ) ≤ (n : ℝ)⁻¹ := fun _ _ ↦ inv_nonneg.2 hn'.le
  have hw₁ : ∑ _t ∈ range n, (n : ℝ)⁻¹ = 1 := by
    rw [sum_const, card_range, nsmul_eq_mul, mul_inv_cancel₀ hn'.ne']
  -- Jensen's inequality for the convex `f · y` and for the concave `f x`.
  have hX := hfx.map_sum_le hw₀ hw₁ fun t ht ↦ hxs t (mem_range.1 ht)
  have hY := hfy.le_map_sum hw₀ hw₁ fun t ht ↦ hys t (mem_range.1 ht)
  simp only [← smul_sum, smul_eq_mul, ← mul_sum] at hX hY
  -- The sum of the two regrets is `∑ t < n, (f (xs t) y - f x (ys t))`.
  have hR : regret (fun t a ↦ f a (ys t)) xs x n + regret (fun t b ↦ -f (xs t) b) ys y n =
      ∑ t ∈ range n, f (xs t) y - ∑ t ∈ range n, f x (ys t) := by
    rw [regret_def, regret_def, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ ↦ by ring
  rw [hR, div_eq_inv_mul, mul_sub]
  linarith

/-- **The duality gap of the average plays** is at most the sum of bounds on the regrets of the
two players against all comparators, divided by the number of rounds [Ora, Theorem 15.12]. -/
theorem dualityGap_le_of_regret_le (hfx : ∀ y ∈ Y, ConvexOn ℝ X fun x ↦ f x y)
    (hfy : ∀ x ∈ X, ConcaveOn ℝ Y (f x)) (hxs : ∀ t < n, xs t ∈ X) (hys : ∀ t < n, ys t ∈ Y)
    (hn : 0 < n) {RX RY : ℝ} (hRX : ∀ x ∈ X, regret (fun t a ↦ f a (ys t)) xs x n ≤ RX)
    (hRY : ∀ y ∈ Y, regret (fun t b ↦ -f (xs t) b) ys y n ≤ RY) :
    dualityGap X Y f ((n : ℝ)⁻¹ • ∑ t ∈ range n, xs t) ((n : ℝ)⁻¹ • ∑ t ∈ range n, ys t) ≤
      ((RX + RY) / n : ℝ) := by
  refine dualityGap_le_coe_iff.2 fun x hx y hy ↦
    (sub_le_regret_add_regret_div (hfx y hy) (hfy x hx) hxs hys hn).trans ?_
  gcongr
  exacts [hRX x hx, hRY y hy]

/-- **No-regret dynamics against approximate best responses** [Ora, Chapter 15]. If the
maximizing player plays at each round an `ε t`-approximate best response `ys t` to the play
`xs t` of the minimizing player, then the duality gap of the average plays is at most
`(RX + ∑ t < n, ε t) / n`, for a bound `RX` on the regret of the minimizing player. Exact best
responses are the case `ε = 0`. -/
theorem dualityGap_le_of_regret_le_of_le_add (hfx : ∀ y ∈ Y, ConvexOn ℝ X fun x ↦ f x y)
    (hfy : ∀ x ∈ X, ConcaveOn ℝ Y (f x)) (hxs : ∀ t < n, xs t ∈ X) (hys : ∀ t < n, ys t ∈ Y)
    (hn : 0 < n) {RX : ℝ} (hRX : ∀ x ∈ X, regret (fun t a ↦ f a (ys t)) xs x n ≤ RX)
    {ε : ℕ → ℝ} (hε : ∀ t < n, ∀ y ∈ Y, f (xs t) y ≤ f (xs t) (ys t) + ε t) :
    dualityGap X Y f ((n : ℝ)⁻¹ • ∑ t ∈ range n, xs t) ((n : ℝ)⁻¹ • ∑ t ∈ range n, ys t) ≤
      ((RX + ∑ t ∈ range n, ε t) / n : ℝ) :=
  dualityGap_le_of_regret_le hfx hfy hxs hys hn hRX fun y hy ↦
    regret_le_sum_of_le_add fun t ht ↦ by linarith [hε t ht y hy]

namespace OnlineLearner

variable {C D : Type*} {A : OnlineLearner C F E} {B : OnlineLearner D E F} (c : ℕ → C)
  (d : ℕ → D) {BA : ℕ → (ℕ → C) → (ℕ → F) → E → ℝ}
  {BB : ℕ → (ℕ → D) → (ℕ → E) → F → ℝ}

/-- **Two no-regret learners against each other** [Ora, Chapter 15]. In the game of the learners
`A` and `B`, let `A` play in `X`, with the regret guarantee `BA` for the losses `f · y` against
plays `y` of the opponent in `Y`, and let `B` play in `Y`, with the regret guarantee `BB` for the
losses `-f x ·` against plays `x` in `X`. Then the average plays `xa`, `ya` of their game satisfy
`f xa y - f x ya ≤ (BA n c ys x + BB n d xs y) / n` for `x ∈ X` and `y ∈ Y` such that `f · y` is
convex on `X` and `f x` is concave on `Y`. -/
theorem sub_le_div_of_hasRegretBound {x : E} {y : F} (hfx : ConvexOn ℝ X fun x ↦ f x y)
    (hfy : ConcaveOn ℝ Y (f x)) (hxs : ∀ t < n, (A.gameRun B c d t).1 ∈ X)
    (hys : ∀ t < n, (A.gameRun B c d t).2 ∈ Y)
    (hA : A.HasRegretBound (fun y x ↦ f x y) (fun _ y ↦ y ∈ Y) X BA)
    (hB : B.HasRegretBound (fun x y ↦ -f x y) (fun _ x ↦ x ∈ X) Y BB) (hn : 0 < n)
    (hx : x ∈ X) (hy : y ∈ Y) :
    f ((n : ℝ)⁻¹ • ∑ t ∈ range n, (A.gameRun B c d t).1) y -
        f x ((n : ℝ)⁻¹ • ∑ t ∈ range n, (A.gameRun B c d t).2) ≤
      (BA n c (fun t ↦ (A.gameRun B c d t).2) x + BB n d (fun t ↦ (A.gameRun B c d t).1) y) /
        n := by
  refine (sub_le_regret_add_regret_div hfx hfy hxs hys hn).trans ?_
  have hrA := hA.regret_le (c := c) hys hx
  have hrB := hB.regret_le (c := d) hxs hy
  rw [← funext (fst_gameRun A B c d)] at hrA
  rw [← funext (snd_gameRun A B c d)] at hrB
  gcongr

/-- **The duality gap of two no-regret learners against each other** [Ora, Chapter 15]. If
the learners `A` and `B` have the worst-case regret guarantees `RA n` and `RB n` after `n` rounds,
the average plays of their game have duality gap at most `(RA n + RB n) / n`. -/
theorem dualityGap_le_of_hasRegretBound (hfx : ∀ y ∈ Y, ConvexOn ℝ X fun x ↦ f x y)
    (hfy : ∀ x ∈ X, ConcaveOn ℝ Y (f x)) (hxs : ∀ t < n, (A.gameRun B c d t).1 ∈ X)
    (hys : ∀ t < n, (A.gameRun B c d t).2 ∈ Y) {RA RB : ℕ → ℝ}
    (hA : A.HasRegretBound (fun y x ↦ f x y) (fun _ y ↦ y ∈ Y) X fun n _ _ _ ↦ RA n)
    (hB : B.HasRegretBound (fun x y ↦ -f x y) (fun _ x ↦ x ∈ X) Y fun n _ _ _ ↦ RB n)
    (hn : 0 < n) :
    dualityGap X Y f ((n : ℝ)⁻¹ • ∑ t ∈ range n, (A.gameRun B c d t).1)
        ((n : ℝ)⁻¹ • ∑ t ∈ range n, (A.gameRun B c d t).2) ≤ ((RA n + RB n) / n : ℝ) :=
  dualityGap_le_coe_iff.2 fun x hx y hy ↦
    sub_le_div_of_hasRegretBound c d (hfx y hy) (hfy x hx) hxs hys hA hB hn hx hy

end OnlineLearner

end LMLExplore.OnlineLearning
