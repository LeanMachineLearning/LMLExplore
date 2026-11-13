/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Bregman.Euclidean
public import LMLExplore.Analysis.Convex.Bregman.Projection
public import LMLExplore.Analysis.Convex.Bregman.StrongConvex
public import LMLExplore.OnlineLearning.FTRL.Equality
public import Mathlib.Topology.Order.Compact

/-!
# Follow the regularized leader

Online linear optimization on a set `K` of a real normed space `E`, with losses in the dual of
`E`: at each round `t`, the learner plays `a t ∈ K`, then the loss `y t : E →L[ℝ] ℝ` is revealed
and the learner suffers the loss `y t (a t)`. The regret against `u ∈ K` after `n` rounds is
`∑ t < n, y t (a t - u)`. All statements hold for every sequence of losses, in particular for
losses chosen adaptively from the past plays.

Follow the regularized leader (FTRL) with regularizers `ψ t` plays at round `t` a minimizer over
`K` of the cumulative loss plus the regularizer, `b ↦ ∑ s < t, y s b + ψ t b`. With a potential
`F` and a learning rate `η > 0`, it plays a minimizer of `b ↦ η ∑ s < t, y s b + F b`
[LS, (28.3)]. The learning rate may change over the rounds: with nonincreasing learning rates
`η t`, the play of round `t` uses `η t`, which is FTRL with the regularizers
`(F - F (a 0)) / η t`. These are nondecreasing in `t` on `K` since the first play `a 0` minimizes
`F` over `K`, and the regret bounds hold for every horizon, without tuning the rates to it. The
bounds for a constant learning rate are their constant cases.

The norm of `E` only enters through strong convexity: the bound for an `m`-strongly convex
potential measures the losses in the operator norm, the dual norm of the norm of `E`. Choosing the
norm of `E` chooses the pair of dual norms; for example `PiLp 1 (fun _ : α ↦ ℝ)` carries the `ℓ¹`
norm, whose dual norm is the sup norm.

The regret analysis of FTRL rests on the FTRL equality of
`LMLExplore.OnlineLearning.FTRL.Equality`, which needs no structure at all
[Ora, Lemma 7.1]. The bounds for linear losses on a normed space below are derived from it.

## Main definitions

* `IsFTRLPlay K F η y t x`: `x` is a play of FTRL on `K` at round `t`, with potential `F`,
  learning rate `η` and losses `y`.

## Main statements

* `sum_apply_sub_le_ftrl`: the **FTRL lemma** for linear losses on a normed space, for
  regularizers that may change over the rounds: the regret is at most `ψ n u - ψ 0 (a 0)` plus
  the sum of the stability terms `y t (a t) - (m (t + 1) - m t)`, where `m t` is the value of the
  objective of round `t` at its play.
* `ftrl_regret_le_of_isMinOn`: for a convex `K` and regularizers `ψ t` with derivatives `ψ' t`
  within `K` at the plays, the regret is at most
  `ψ n u - ψ 0 (a 0) - ∑ t < n, (ψ (t + 1) - ψ t) (a (t + 1))
    + ∑ t < n, (y t (a t - a (t + 1)) - D_{ψ t}(a (t + 1), a t))`, with `D_ψ` the Bregman
  divergence [Ora, Lemma 7.1].
* `ftrl_regret_le_of_monotone`: its case of regularizers `ψ t` nondecreasing in `t` on `K`, with
  the bound `ψ n u - ψ 0 (a 0) + ∑ t < n, (y t (a t - a (t + 1)) - D_{ψ t}(a (t + 1), a t))`.
* `ftrl_regret_le_of_antitone`: the anytime form of [LS, Theorem 28.5]. With nonincreasing
  learning rates `η t` and a potential `F` with a derivative `F' t` within `K` at each play, the
  regret is at most
  `(F u - F (a 0)) / η n + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
  The potential need not be convex.
* `ftrl_regret_le`: [LS, Theorem 28.5], its case of a constant learning rate `η`.
* `ftrl_regret_succ_le_sum_inv_sub_inv`: for positive learning rates, not necessarily monotone,
  the regret after `n + 1` rounds with the penalty of each change of rate at the play of its
  round, `(F u - F (a 0)) / η 0 + ∑ t < n, (1 / η (t + 1) - 1 / η t) (F u - F (a (t + 1)))`, the
  comparator `u` taking the place of a play of round `n + 1` in the last stability term.
* `ftrl_regret_succ_le_of_antitone`: its case of nonincreasing learning rates, with the penalty
  `(F u - F (a 0)) / η n` of the rate `η n` of the last play.
* `apply_sub_sub_div_le_of_mul_norm_sq_le`: the stability term of one round is at most
  `η / (2 m) * ‖y‖ ^ 2` when the Bregman divergence dominates `m / 2` times the squared distance,
  with `‖y‖` the operator norm.
* `ftrl_regret_le_of_strongConvexOn_of_antitone`: [Ora, Corollary 7.6]. For an `m`-strongly
  convex potential with respect to the norm of `E` and nonincreasing learning rates, the regret is
  at most `(F u - F (a 0)) / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2`, from
  `ftrl_regret_succ_le_of_antitone` and the stability bound of each round.
* `ftrl_regret_le_of_strongConvexOn`: [LS, Corollary 28.8], its case of a constant learning
  rate, with the bound `(F u - F (a 0)) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2`.
* `sum_apply_sub_sub_bregDiv_le_of_strongConvexOn`: the summed stability bound for a strongly
  convex potential and a constant learning rate, used by mirror descent. It follows from
  `sum_apply_sub_sub_bregDiv_le_of_mul_norm_sq_le`, which allows a strong convexity modulus that
  changes over the rounds.
* `exists_ftrl`: on a nonempty compact set, FTRL with a potential continuous on that set has
  plays.
* `ftrl_regret_le_sqrt_of_closedBall`: [LS, Proposition 28.6] for FTRL. On the closed unit ball
  of a real inner product space, with the potential `‖b‖ ^ 2 / 2` and the learning rate `1 / √n`,
  the regret after `n` rounds against every point of the ball is at most `√n` for the losses
  `⟪g t, ·⟫` of vectors of norm at most `1`.

## Implementation notes

The FTRL lemma is adapted from the LMLPapers project (same author), where it is stated for gains
on the probability simplex. Its telescoping proof, also adapted from there, now proves the FTRL
equality for losses on any type, in `LMLExplore.OnlineLearning.FTRL.Equality`; this file states
the case of linear losses on a subset `K` of a real normed space `E`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/
public section

open Finset Metric
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {n : ℕ} {u : E}

/-- `x` is a play of **follow the regularized leader** [LS, (28.3)] on `K` at round `t`, with
potential `F`, learning rate `η` and losses `y`: `x ∈ K` minimizes the objective
`b ↦ η ∑ s < t, y s b + F b` over `K`. -/
structure IsFTRLPlay (K : Set E) (F : E → ℝ) (η : ℝ) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) (x : E) :
    Prop where
  /-- The play lies in `K`. -/
  mem : x ∈ K
  /-- The play minimizes the FTRL objective of round `t` over `K`. -/
  isMinOn : IsMinOn (fun b ↦ η * ∑ s ∈ range t, y s b + F b) K x

/-- **FTRL lemma for linear losses** [Ora, Lemma 7.1], the case of `regret_le_ftrl` for linear
losses on a normed space. Let the point `a n` of round `n` do at least as well as `u`
on the objective `b ↦ ∑ s < n, y s b + ψ n b`, for instance a minimizer of it over a set containing
`u`. Then the regret against `u` after `n` rounds is at most `ψ n u - ψ 0 (a 0)` plus the sum over
the rounds of the stability terms `y t (a t) - (m (t + 1) - m t)`, where
`m t = ∑ s < t, y s (a t) + ψ t (a t)` is the value of the objective of round `t` at `a t`. -/
theorem sum_apply_sub_le_ftrl (ψ : ℕ → E → ℝ) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : ∑ s ∈ range n, y s (a n) + ψ n (a n) ≤ ∑ s ∈ range n, y s u + ψ n u) :
    ∑ t ∈ range n, y t (a t - u) ≤ ψ n u - ψ 0 (a 0) + ∑ t ∈ range n, (y t (a t) -
      ((∑ s ∈ range (t + 1), y s (a (t + 1)) + ψ (t + 1) (a (t + 1))) -
        (∑ s ∈ range t, y s (a t) + ψ t (a t)))) := by
  have h := regret_le_ftrl ψ (fun t ↦ y t) a a (u := u) (by linarith)
  rw [regret_eq_sum_apply_sub] at h
  refine h.trans_eq (congrArg (_ + ·) (sum_congr rfl fun t _ ↦ ?_))
  ring

/-- **Regret of FTRL with the penalties of the changes of regularizer** [Ora, Lemma 7.1]. Let `K`
be convex. Let each `a t`, for `t < n`, minimize over `K` the objective
`b ↦ ∑ s < t, y s b + ψ t b`, where `ψ t` has derivative `ψ' t` within `K` at `a t`, and let
`a n ∈ K` do at least as well as `u` on the objective of round `n`. Then, with `D_ψ` the Bregman
divergence,
`∑ t < n, y t (a t - u) ≤ ψ n u - ψ 0 (a 0) - ∑ t < n, (ψ (t + 1) (a (t + 1)) - ψ t (a (t + 1)))
  + ∑ t < n, (y t (a t - a (t + 1)) - D_{ψ t}(a (t + 1), a t))`.
The regularizers need not be monotone: the increments `ψ (t + 1) - ψ t` at the next plays are
kept. For regularizers that grow with `t` they are nonnegative, and `ftrl_regret_le_of_monotone`
drops them; keeping them is what bounds the regret of Tsallis-INF in stochastic environments. -/
theorem ftrl_regret_le_of_isMinOn (hK : Convex ℝ K) (ψ : ℕ → E → ℝ) (y : ℕ → E →L[ℝ] ℝ)
    (a : ℕ → E) (ha : ∀ t < n, IsMinOn (fun b ↦ ∑ s ∈ range t, y s b + ψ t b) K (a t))
    (haK : ∀ t ≤ n, a t ∈ K)
    (han : ∑ s ∈ range n, y s (a n) + ψ n (a n) ≤ ∑ s ∈ range n, y s u + ψ n u)
    (ψ' : ℕ → E →L[ℝ] ℝ) (hψ' : ∀ t < n, HasFDerivWithinAt (ψ t) (ψ' t) K (a t)) :
    ∑ t ∈ range n, y t (a t - u) ≤ ψ n u - ψ 0 (a 0) -
      ∑ t ∈ range n, (ψ (t + 1) (a (t + 1)) - ψ t (a (t + 1))) +
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv (ψ t) (a (t + 1)) (a t) (ψ' t)) := by
  -- the objective of round `t` increases from `a t` to `a (t + 1)` by at least the Bregman
  -- divergence of `ψ t`
  have h_term : ∑ t ∈ range n, (y t (a t) -
      ((∑ s ∈ range (t + 1), y s (a (t + 1)) + ψ (t + 1) (a (t + 1))) -
        (∑ s ∈ range t, y s (a t) + ψ t (a t)))) ≤
      ∑ t ∈ range n, ((y t (a t - a (t + 1)) - bregDiv (ψ t) (a (t + 1)) (a t) (ψ' t)) -
        (ψ (t + 1) (a (t + 1)) - ψ t (a (t + 1)))) := by
    refine sum_le_sum fun t ht ↦ ?_
    have ht' := mem_range.mp ht
    have h_min : IsMinOn (fun c ↦ (∑ s ∈ range t, y s) c + ψ t c) K (a t) := by
      simpa using ha t ht'
    have h_breg := bregDiv_le_sub_of_isMinOn
      (hK.segment_subset (haK t ht'.le) (haK (t + 1) ht')) h_min (hψ' t ht')
    simp only [FunLike.coe_sum, Finset.sum_apply] at h_breg
    rw [sum_range_succ, map_sub]
    linarith
  have e := sum_sub_distrib (s := range n)
    (fun t ↦ y t (a t - a (t + 1)) - bregDiv (ψ t) (a (t + 1)) (a t) (ψ' t))
    (fun t ↦ ψ (t + 1) (a (t + 1)) - ψ t (a (t + 1)))
  linarith [sum_apply_sub_le_ftrl ψ y a han]

/-- **Regret of FTRL with time-varying regularizers** [Ora, Lemma 7.1]. Let `K` be convex and let
the regularizers `ψ t` be nondecreasing in `t` on `K`. Let each `a t`, for `t < n`, minimize over
`K` the objective `b ↦ ∑ s < t, y s b + ψ t b`, where `ψ t` has derivative `ψ' t` within `K` at
`a t`, and let `a n ∈ K` do at least as well as `u` on the objective of round `n`. Then, with
`D_ψ` the Bregman divergence,
`∑ t < n, y t (a t - u)
  ≤ ψ n u - ψ 0 (a 0) + ∑ t < n, (y t (a t - a (t + 1)) - D_{ψ t}(a (t + 1), a t))`.
The last point `a n` is typically the minimizer of the objective of round `n` over `K`, for
`u ∈ K`; the regularizer `ψ n` may also be any regularizer that keeps the sequence nondecreasing
on `K`, for example `ψ n = ψ (n - 1)` with `a n = u`. -/
theorem ftrl_regret_le_of_monotone (hK : Convex ℝ K) (ψ : ℕ → E → ℝ) (y : ℕ → E →L[ℝ] ℝ)
    (a : ℕ → E) (ha : ∀ t < n, IsMinOn (fun b ↦ ∑ s ∈ range t, y s b + ψ t b) K (a t))
    (haK : ∀ t ≤ n, a t ∈ K)
    (han : ∑ s ∈ range n, y s (a n) + ψ n (a n) ≤ ∑ s ∈ range n, y s u + ψ n u)
    (hψ : ∀ b ∈ K, Monotone fun t ↦ ψ t b) (ψ' : ℕ → E →L[ℝ] ℝ)
    (hψ' : ∀ t < n, HasFDerivWithinAt (ψ t) (ψ' t) K (a t)) :
    ∑ t ∈ range n, y t (a t - u) ≤ ψ n u - ψ 0 (a 0) +
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv (ψ t) (a (t + 1)) (a t) (ψ' t)) := by
  have h := ftrl_regret_le_of_isMinOn hK ψ y a ha haK han ψ' hψ'
  have h_pen : 0 ≤ ∑ t ∈ range n, (ψ (t + 1) (a (t + 1)) - ψ t (a (t + 1))) :=
    sum_nonneg fun t ht ↦
      sub_nonneg.mpr (hψ _ (haK (t + 1) (mem_range.mp ht)) (Nat.le_succ t))
  linarith

/-- A play of FTRL with potential `F` and learning rate `η > 0` minimizes the objective with the
regularizer `(F - c) / η`, for any constant `c`. -/
lemma IsFTRLPlay.isMinOn_sum_add_sub_div {F : E → ℝ} {η : ℝ} {y : ℕ → E →L[ℝ] ℝ} {t : ℕ}
    {x : E} (h : IsFTRLPlay K F η y t x) (hη : 0 < η) (c : ℝ) :
    IsMinOn (fun b ↦ ∑ s ∈ range t, y s b + (F b - c) / η) K x := by
  have h_obj (b : E) :
      ∑ s ∈ range t, y s b + (F b - c) / η = (η * ∑ s ∈ range t, y s b + F b - c) / η := by
    field_simp
    ring
  refine isMinOn_iff.mpr fun b hb ↦ ?_
  rw [h_obj, h_obj]
  exact div_le_div_of_nonneg_right (sub_le_sub_right (isMinOn_iff.mp h.isMinOn b hb) c) hη.le

/-- The first play of FTRL minimizes the potential. -/
lemma IsFTRLPlay.isMinOn_zero {F : E → ℝ} {η : ℝ} {y : ℕ → E →L[ℝ] ℝ} {x : E}
    (h : IsFTRLPlay K F η y 0 x) : IsMinOn F K x := by
  simpa using h.isMinOn

/-- FTRL with nonincreasing learning rates `η t` is FTRL with the nondecreasing regularizers
`(F - c) / η t`, for any `c ≤ F` on `K`: `ftrl_regret_le_of_monotone` for these regularizers, with
a last point `a n ∈ K` that only needs to do at least as well as `u`. -/
private lemma ftrl_regret_le_of_antitone_aux {F : E → ℝ} (hK : Convex ℝ K) {η : ℕ → ℝ}
    (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) {c : ℝ} (hc : ∀ b ∈ K, c ≤ F b)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (ha : ∀ t < n, IsFTRLPlay K F (η t) y t (a t))
    (haK : a n ∈ K)
    (han : ∑ s ∈ range n, y s (a n) + (F (a n) - c) / η n ≤
      ∑ s ∈ range n, y s u + (F u - c) / η n)
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) :
    ∑ t ∈ range n, y t (a t - u) ≤ (F u - c) / η n - (F (a 0) - c) / η 0 +
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) := by
  have h := ftrl_regret_le_of_monotone hK (fun t b ↦ (F b - c) / η t) y a
    (fun t ht ↦ (ha t ht).isMinOn_sum_add_sub_div (hη t) c)
    (fun t ht ↦ by rcases ht.lt_or_eq with ht | rfl; exacts [(ha t ht).mem, haK]) han
    (fun b hb t₁ t₂ ht ↦ div_le_div_of_nonneg_left (sub_nonneg.mpr (hc b hb)) (hη t₂) (hη_anti ht))
    (fun t ↦ (η t)⁻¹ • F' t) fun t ht ↦ by
      simpa only [div_eq_mul_inv] using ((hF' t ht).sub_const c).mul_const (η t)⁻¹
  have h_breg (t : ℕ) : bregDiv (fun b ↦ (F b - c) / η t) (a (t + 1)) (a t) ((η t)⁻¹ • F' t) =
      bregDiv F (a (t + 1)) (a t) (F' t) / η t := by
    simp only [bregDiv, smul_apply, smul_eq_mul]
    ring
  simpa only [h_breg] using h

/-- **Regret of FTRL with nonincreasing learning rates**, the anytime form of
[LS, Theorem 28.5]. Let `K` be convex and let the learning rates `η t > 0` be nonincreasing. Let
each `a t`, for `t ≤ n`, be a play of FTRL on `K` with potential `F` and learning rate `η t`
(`IsFTRLPlay`), where `F` has derivative `F' t` within `K` at `a t` for `t < n`. Then for every
`u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n, y t (a t - u)
  ≤ (F u - F (a 0)) / η n + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
The potential need not be convex or nonnegative: FTRL with rates `η t` is FTRL with the
regularizers `(F - F (a 0)) / η t`, which are nondecreasing in `t` on `K` since `a 0` minimizes
`F` over `K`. -/
theorem ftrl_regret_le_of_antitone {F : E → ℝ} (hK : Convex ℝ K) {η : ℕ → ℝ}
    (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : ∀ t ≤ n, IsFTRLPlay K F (η t) y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ (F u - F (a 0)) / η n +
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) := by
  have h := ftrl_regret_le_of_antitone_aux hK hη hη_anti
    (fun b hb ↦ isMinOn_iff.mp (ha 0 n.zero_le).isMinOn_zero b hb) y a (fun t ht ↦ ha t ht.le)
    (ha n le_rfl).mem (isMinOn_iff.mp ((ha n le_rfl).isMinOn_sum_add_sub_div (hη n) _) u hu) F' hF'
  rwa [sub_self, zero_div, sub_zero] at h

/-- **Regret of FTRL with changing learning rates, with the penalties of the changes of rate.**
Let `K` be convex and let the learning rates `η t` be positive. Let each `a t`, for `t ≤ n`, be a
play of FTRL on `K` with potential `F` and learning rate `η t` (`IsFTRLPlay`), where `F` has
derivative `F' t` within `K` at `a t`. Then for every `u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n + 1, y t (a t - u) ≤ (F u - F (a 0)) / η 0
  + ∑ t < n, (1 / η (t + 1) - 1 / η t) * (F u - F (a (t + 1)))
  + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)
  + (y n (a n - u) - D_F(u, a n) / η n)`.
The learning rates need not be monotone. The penalty of round `t + 1` is the change
`1 / η (t + 1) - 1 / η t` of the inverse rate times the gap `F u - F (a (t + 1))` at the play of
that round, which the minimax bounds replace by its maximum over `K`; the comparator `u` takes the
place of a play of round `n + 1` in the last stability term. -/
theorem ftrl_regret_succ_le_sum_inv_sub_inv {F : E → ℝ} (hK : Convex ℝ K) {η : ℕ → ℝ}
    (hη : ∀ t, 0 < η t) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : ∀ t ≤ n, IsFTRLPlay K F (η t) y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range (n + 1), y t (a t - u) ≤ (F u - F (a 0)) / η 0 +
      ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * (F u - F (a (t + 1))) +
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) +
      (y n (a n - u) - bregDiv F u (a n) (F' n) / η n) := by
  -- the learning rate after the last round is free: keep `η n` and take `u` as the last point, so
  -- that the last point does as well as `u` and the last stability term is between `a n` and `u`
  set a' := Function.update a (n + 1) u with ha'_def
  have ha' (t : ℕ) (ht : t < n + 1) : a' t = a t := Function.update_of_ne ht.ne _ _
  have h_last : a' (n + 1) = u := by simp [ha'_def]
  have hmin (t : ℕ) (ht : t < n + 1) : min t n = t := min_eq_left (Nat.le_of_lt_succ ht)
  have h := ftrl_regret_le_of_isMinOn hK (n := n + 1) (u := u)
    (fun t b ↦ F b / η (min t n)) y a'
    (fun t ht ↦ by
      rw [ha' t ht, hmin t ht]
      simpa only [sub_zero] using (ha t (Nat.le_of_lt_succ ht)).isMinOn_sum_add_sub_div (hη t) 0)
    (fun t ht ↦ by
      rcases ht.lt_or_eq with ht | rfl
      · rw [ha' t ht]
        exact (ha t (Nat.le_of_lt_succ ht)).mem
      · rwa [h_last])
    (by rw [h_last]) (fun t ↦ (η t)⁻¹ • F' t) fun t ht ↦ by
      rw [ha' t ht, hmin t ht]
      simpa only [div_eq_mul_inv] using
        (hF' t (Nat.le_of_lt_succ ht)).mul_const (η t)⁻¹
  -- rewrite the bound in terms of `a`, `F` and `η`
  have h_breg (t : ℕ) (b c : E) :
      bregDiv (fun b ↦ F b / η t) b c ((η t)⁻¹ • F' t) = bregDiv F b c (F' t) / η t := by
    simp only [bregDiv, smul_apply, smul_eq_mul]
    ring
  have e_lhs : ∑ t ∈ range (n + 1), y t (a' t - u) = ∑ t ∈ range (n + 1), y t (a t - u) :=
    sum_congr rfl fun t ht ↦ by rw [ha' t (mem_range.mp ht)]
  have e_pen : ∑ t ∈ range (n + 1), (F (a' (t + 1)) / η (min (t + 1) n) -
      F (a' (t + 1)) / η (min t n)) =
      ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * F (a (t + 1)) := by
    rw [sum_range_succ, min_eq_right n.le_succ, min_self, sub_self, add_zero]
    refine sum_congr rfl fun t ht ↦ ?_
    have ht := mem_range.mp ht
    rw [ha' (t + 1) (Nat.succ_lt_succ ht), hmin (t + 1) (Nat.succ_lt_succ ht),
      hmin t (ht.trans n.lt_succ_self)]
    ring
  have e_stab : ∑ t ∈ range (n + 1), (y t (a' t - a' (t + 1)) -
      bregDiv (fun b ↦ F b / η (min t n)) (a' (t + 1)) (a' t) ((η t)⁻¹ • F' t)) =
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) +
      (y n (a n - u) - bregDiv F u (a n) (F' n) / η n) := by
    rw [sum_range_succ, ha' n n.lt_succ_self, h_last, min_self, h_breg]
    congr 1
    refine sum_congr rfl fun t ht ↦ ?_
    have ht := mem_range.mp ht
    rw [ha' t (ht.trans n.lt_succ_self), ha' (t + 1) (Nat.succ_lt_succ ht),
      hmin t (ht.trans n.lt_succ_self), h_breg]
  rw [e_lhs, e_pen, e_stab, ha' 0 n.succ_pos, min_eq_right n.le_succ, Nat.zero_min] at h
  -- the penalty `F u / η n - F (a 0) / η 0` telescopes along the inverse rates
  have h_tel : ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * F u = ((η n)⁻¹ - (η 0)⁻¹) * F u := by
    rw [← sum_mul, sum_range_sub (fun t ↦ (η t)⁻¹)]
  have h_split : ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * (F u - F (a (t + 1))) =
      ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * F u -
        ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * F (a (t + 1)) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun t _ ↦ by ring
  rw [h_split, h_tel]
  simp only [div_eq_mul_inv] at h ⊢
  linarith

/-- **Regret of FTRL with nonincreasing learning rates, with the rate of the last play.** Let `K`
be convex and let the learning rates `η t > 0` be nonincreasing. Let each `a t`, for `t ≤ n`, be a
play of FTRL on `K` with potential `F` and learning rate `η t` (`IsFTRLPlay`), where `F` has
derivative `F' t` within `K` at `a t`. Then for every `u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n + 1, y t (a t - u) ≤ (F u - F (a 0)) / η n
  + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)
  + (y n (a n - u) - D_F(u, a n) / η n)`.
Unlike `ftrl_regret_le_of_antitone`, the penalty term uses the rate `η n` of the last play rather
than a rate after the last round, and no play of round `n + 1` is needed: the comparator `u` takes
the place of that play in the last stability term. -/
theorem ftrl_regret_succ_le_of_antitone {F : E → ℝ} (hK : Convex ℝ K) {η : ℕ → ℝ}
    (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : ∀ t ≤ n, IsFTRLPlay K F (η t) y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range (n + 1), y t (a t - u) ≤ (F u - F (a 0)) / η n +
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) +
      (y n (a n - u) - bregDiv F u (a n) (F' n) / η n) := by
  refine (ftrl_regret_succ_le_sum_inv_sub_inv hK hη y a ha F' hF' hu).trans ?_
  -- the inverse rates grow and `a 0` minimizes `F` over `K`, so each penalty is at most
  -- `(1 / η (t + 1) - 1 / η t) * (F u - F (a 0))`, and these telescope
  have h_pen : ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * (F u - F (a (t + 1))) ≤
      ((η n)⁻¹ - (η 0)⁻¹) * (F u - F (a 0)) := by
    rw [← sum_range_sub (fun t ↦ (η t)⁻¹), sum_mul]
    refine sum_le_sum fun t ht ↦ mul_le_mul_of_nonneg_left ?_
      (sub_nonneg.mpr (inv_anti₀ (hη _) (hη_anti t.le_succ)))
    have := isMinOn_iff.mp (ha 0 n.zero_le).isMinOn_zero (a (t + 1))
      (ha (t + 1) (mem_range.mp ht)).mem
    linarith
  have h_eq : (F u - F (a 0)) / η 0 + ((η n)⁻¹ - (η 0)⁻¹) * (F u - F (a 0)) =
      (F u - F (a 0)) / η n := by
    ring
  linarith

/-- **Regret of follow the regularized leader** [LS, Theorem 28.5]. Let `K` be convex and
`η > 0`. Let each `a t`, for `t ≤ n`, be a play of FTRL on `K` with potential `F` and learning
rate `η` (`IsFTRLPlay`), where `F` has derivative `F' t` within `K` at `a t` for `t < n`.
Then for every `u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η + ∑ t < n, y t (a t - a (t + 1))
  - (∑ t < n, D_F(a (t + 1), a t)) / η`.
[LS] assumes the potential convex; the proof only uses the derivatives at the plays. This is the
case of constant learning rates of `ftrl_regret_le_of_antitone`. -/
theorem ftrl_regret_le {F : E → ℝ} (hK : Convex ℝ K) {η : ℝ} (hη : 0 < η)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (ha : ∀ t ≤ n, IsFTRLPlay K F η y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ (F u - F (a 0)) / η +
      ∑ t ∈ range n, y t (a t - a (t + 1)) -
        (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
  have h := ftrl_regret_le_of_antitone hK (fun _ ↦ hη) antitone_const y a ha F' hF' hu
  rwa [sum_sub_distrib, ← sum_div, ← add_sub_assoc] at h

/-- **Stability of one round.** Let `m > 0` and `η > 0`. If `D` dominates `m / 2 * ‖b - a‖ ^ 2`,
then `y (a - b) - D / η ≤ η / (2 m) * ‖y‖ ^ 2`, where `‖y‖` is the operator norm of the loss, the
dual norm of the norm of `E`. With `D = D_F(b, a)` the Bregman divergence of a potential `F`, this
bounds the stability term of a round of FTRL or mirror descent [LS, Corollary 28.8]; the
modulus `m` may depend on the base point `a`. -/
lemma apply_sub_sub_div_le_of_mul_norm_sq_le {m η D : ℝ} (hm : 0 < m) (hη : 0 < η)
    (y : E →L[ℝ] ℝ) {a b : E} (h : m / 2 * ‖b - a‖ ^ 2 ≤ D) :
    y (a - b) - D / η ≤ η / (2 * m) * ‖y‖ ^ 2 := by
  have h_apply : y (a - b) ≤ ‖b - a‖ * ‖y‖ := by
    rw [norm_sub_rev, mul_comm]
    exact (Real.le_norm_self _).trans (y.le_opNorm _)
  -- `x z - m x² / (2 η) ≤ η z² / (2 m)`, a square completion
  set x := ‖b - a‖
  set z := ‖y‖
  have h_sq : η / (2 * m) * z ^ 2 - (x * z - m / 2 * x ^ 2 / η) =
      (m * x - η * z) ^ 2 / (2 * m * η) := by
    field_simp
    ring
  have h_nonneg : 0 ≤ (m * x - η * z) ^ 2 / (2 * m * η) := by positivity
  have h_div := div_le_div_of_nonneg_right h hη.le
  linarith

/-- **Stability terms for a local strong convexity modulus.** Let `η > 0` and, for `t < n`, let
`m t > 0` be such that the Bregman divergence `D_F(a (t + 1), a t)` dominates
`m t / 2 * ‖a (t + 1) - a t‖ ^ 2`. Then
`∑ t < n, y t (a t - a (t + 1)) - (∑ t < n, D_F(a (t + 1), a t)) / η
  ≤ ∑ t < n, η / (2 m t) * ‖y t‖ ^ 2`,
where `‖y t‖` is the operator norm of the loss, the dual norm of the norm of `E`. -/
theorem sum_apply_sub_sub_bregDiv_le_of_mul_norm_sq_le {F : E → ℝ} {η : ℝ} (hη : 0 < η)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) {m : ℕ → ℝ} (hm : ∀ t < n, 0 < m t)
    (h : ∀ t < n, m t / 2 * ‖a (t + 1) - a t‖ ^ 2 ≤ bregDiv F (a (t + 1)) (a t) (F' t)) :
    ∑ t ∈ range n, y t (a t - a (t + 1)) -
        (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η ≤
      ∑ t ∈ range n, η / (2 * m t) * ‖y t‖ ^ 2 := by
  rw [sum_div, ← sum_sub_distrib]
  refine sum_le_sum fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  exact apply_sub_sub_div_le_of_mul_norm_sq_le (hm t ht') hη (y t) (h t ht')

/-- **Stability terms for a strongly convex potential and a constant learning rate**, the
stability step of mirror descent in [LS, Corollary 28.8]. Let `F` be `m`-strongly convex on `K`
for the norm of `E`, with `m > 0`, let `η > 0`, let `a t ∈ K` for `t ≤ n`, and let `F` have
derivative `F' t` within `K` at `a t` for `t < n`. Then
`∑ t < n, y t (a t - a (t + 1)) - (∑ t < n, D_F(a (t + 1), a t)) / η
  ≤ η / (2 m) ∑ t < n, ‖y t‖ ^ 2`,
where `D_F` is the Bregman divergence and `‖y t‖` the operator norm of the loss, the dual norm of
the norm of `E`. -/
theorem sum_apply_sub_sub_bregDiv_le_of_strongConvexOn {F : E → ℝ} {m : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) {η : ℝ} (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ)
    (a : ℕ → E) (ha : ∀ t ≤ n, a t ∈ K) (F' : ℕ → E →L[ℝ] ℝ)
    (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) :
    ∑ t ∈ range n, y t (a t - a (t + 1)) -
        (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η ≤
      η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 := by
  rw [mul_sum]
  exact sum_apply_sub_sub_bregDiv_le_of_mul_norm_sq_le hη y a F' (fun _ _ ↦ hm) fun t ht ↦
    hF.mul_norm_sub_sq_le_bregDiv (ha t ht.le) (ha (t + 1) ht) (hF' t ht)

/-- **Regret of FTRL with nonincreasing learning rates and a strongly convex potential**
[Ora, Corollary 7.6]. Let `K` be convex, let the learning rates `η t > 0` be nonincreasing, and
let the potential `F` be `m`-strongly convex on `K` for the norm of `E`, with `m > 0`. Let each
`a t`, for `t < n` and for `t = 0`, be a play of FTRL on `K` with potential `F` and learning rate
`η t` (`IsFTRLPlay`), where `F` has derivative `F' t` within `K` at `a t` for `t < n`. Then for
every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2`,
where `‖y t‖` is the operator norm of the loss, the dual norm of the norm of `E`. The bound holds
for every horizon `n`, without tuning the learning rates to it. -/
theorem ftrl_regret_le_of_strongConvexOn_of_antitone {F : E → ℝ} {m : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha0 : IsFTRLPlay K F (η 0) y 0 (a 0)) (ha : ∀ t < n, IsFTRLPlay K F (η t) y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (F u - F (a 0)) / η (n - 1) + ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2 := by
  rcases n with _ | n
  · simpa using div_nonneg (sub_nonneg.mpr (isMinOn_iff.mp ha0.isMinOn_zero u hu)) (hη 0).le
  have ha' (t : ℕ) (ht : t ≤ n) : IsFTRLPlay K F (η t) y t (a t) := ha t (Nat.lt_succ_of_le ht)
  refine (ftrl_regret_succ_le_of_antitone hF.1 hη hη_anti y a ha' F'
    (fun t ht ↦ hF' t (Nat.lt_succ_of_le ht)) hu).trans ?_
  rw [Nat.add_sub_cancel, sum_range_succ, ← add_assoc]
  -- each stability term is bounded through the strong convexity of `F`
  refine add_le_add (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_)) ?_
  · have ht := mem_range.mp ht
    exact apply_sub_sub_div_le_of_mul_norm_sq_le hm (hη t) (y t)
      (hF.mul_norm_sub_sq_le_bregDiv (ha' t ht.le).mem (ha' (t + 1) ht).mem
        (hF' t (ht.trans n.lt_succ_self)))
  · exact apply_sub_sub_div_le_of_mul_norm_sq_le hm (hη n) (y n)
      (hF.mul_norm_sub_sq_le_bregDiv (ha' n le_rfl).mem hu (hF' n n.lt_succ_self))

/-- **Regret of FTRL with a strongly convex potential** [LS, Corollary 28.8]. Under the
assumptions of `ftrl_regret_le`, if the potential `F` is `m`-strongly convex on `K` for the norm
of `E`, with `m > 0`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2`,
where `‖y t‖` is the operator norm of the loss, the dual norm of the norm of `E`. [LS] states it
with the diameter of `K` for `F` in place of `F u - F (a 0)`. This is the case of constant
learning rates of `ftrl_regret_le_of_strongConvexOn_of_antitone`. -/
theorem ftrl_regret_le_of_strongConvexOn {F : E → ℝ} {m : ℝ} (hF : StrongConvexOn K m F)
    (hm : 0 < m) {η : ℝ} (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : ∀ t ≤ n, IsFTRLPlay K F η y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (F u - F (a 0)) / η + η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 := by
  have h := ftrl_regret_le_of_strongConvexOn_of_antitone hF hm (fun _ ↦ hη) antitone_const y a
    (ha 0 n.zero_le) (fun t ht ↦ ha t ht.le) F' hF' hu
  rwa [← mul_sum] at h

/-- **Existence of FTRL plays.** On a nonempty compact set `K`, with a potential `F` continuous
on `K`, there is a sequence `a` such that each `a t` is a play of FTRL on `K` at round `t`, with
potential `F`, learning rate `η` and losses `y`. -/
theorem exists_ftrl {F : E → ℝ} (hK : IsCompact K) (hK_ne : K.Nonempty) (hF : ContinuousOn F K)
    (η : ℝ) (y : ℕ → E →L[ℝ] ℝ) :
    ∃ a : ℕ → E, ∀ t, IsFTRLPlay K F η y t (a t) := by
  have h_cont (t : ℕ) : ContinuousOn (fun b ↦ η * ∑ s ∈ range t, y s b + F b) K :=
    (by fun_prop : Continuous fun b ↦ η * ∑ s ∈ range t, y s b).continuousOn.add hF
  choose a ha using fun t ↦ hK.exists_isMinOn hK_ne (h_cont t)
  exact ⟨a, fun t ↦ ⟨(ha t).1, (ha t).2⟩⟩

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} {u : E}

/-- **FTRL on the unit ball** [LS, Proposition 28.6], which [LS] states for mirror descent and
notes for FTRL. Let the losses be `⟪g t, ·⟫` for vectors `g t` of norm at most `1`, and let each
`a t`, for `t ≤ n`, be a play of FTRL on the closed unit ball with the potential `‖b‖ ^ 2 / 2` and
the learning rate `1 / √n`, that is, a minimizer over the ball of
`b ↦ (√n)⁻¹ ∑ s < t, ⟪g s, b⟫ + ‖b‖ ^ 2 / 2`. Then the regret after `n` rounds against every
point of the ball is at most `√n`. -/
theorem ftrl_regret_le_sqrt_of_closedBall (g a : ℕ → E) (hg : ∀ t < n, ‖g t‖ ≤ 1)
    (ha : ∀ t ≤ n, IsFTRLPlay (closedBall 0 1) (fun b ↦ ‖b‖ ^ 2 / 2) (√n)⁻¹
      (fun s ↦ innerSL ℝ (g s)) t (a t))
    (hu : u ∈ closedBall (0 : E) 1) :
    ∑ t ∈ range n, ⟪g t, a t - u⟫ ≤ √n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hsqrt : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h := ftrl_regret_le_of_strongConvexOn
    (strongConvexOn_norm_sq_div_two (convex_closedBall 0 1)) one_pos (inv_pos.mpr hsqrt) _ a ha _
    (fun t _ ↦ (hasFDerivAt_norm_sq_div_two (a t)).hasFDerivWithinAt) hu
  simp only [innerSL_apply_apply, innerSL_apply_norm] at h
  -- the penalty is at most `√n / 2` and the stability terms add up to at most `√n / 2`
  have hu' : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
  have h_pen : (‖u‖ ^ 2 / 2 - ‖a 0‖ ^ 2 / 2) / (√n)⁻¹ ≤ √n / 2 := by
    rw [div_inv_eq_mul]
    have : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg u) hu'
    nlinarith [sq_nonneg ‖a 0‖]
  have h_sum : ∑ t ∈ range n, ‖g t‖ ^ 2 ≤ n := by
    calc ∑ t ∈ range n, ‖g t‖ ^ 2
    _ ≤ ∑ t ∈ range n, (1 : ℝ) :=
      sum_le_sum fun t ht ↦ pow_le_one₀ (norm_nonneg _) (hg t (mem_range.mp ht))
    _ = n := by simp
  have h_stab : (√n)⁻¹ / (2 * 1) * ∑ t ∈ range n, ‖g t‖ ^ 2 ≤ √n / 2 := by
    calc (√n)⁻¹ / (2 * 1) * ∑ t ∈ range n, ‖g t‖ ^ 2
    _ ≤ (√n)⁻¹ / (2 * 1) * n := by gcongr
    _ = √n / 2 := by
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  linarith

end InnerProductSpace

end LMLExplore.OnlineLearning
