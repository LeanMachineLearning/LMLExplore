/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Order.Compact
public import TauCeti.Analysis.Convex.Strong

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
[LS, (28.3)].

The norm of `E` only enters through strong convexity: the bound for an `m`-strongly convex
potential measures the losses in the operator norm, the dual norm of the norm of `E`. Choosing the
norm of `E` chooses the pair of dual norms; for example `PiLp 1 (fun _ : α ↦ ℝ)` carries the `ℓ¹`
norm, whose dual norm is the sup norm.

## Main definitions

* `IsFTRLPlay K F η y t x`: `x` is a play of FTRL on `K` at round `t`, with potential `F`,
  learning rate `η` and losses `y`.

## Main statements

* `sum_apply_sub_le_ftrl`: the **FTRL lemma** [Ora, Lemma 7.1], for regularizers that may change
  over the rounds: the regret is at most `ψ n u - ψ 0 (a 0)` plus the sum of the stability terms
  `y t (a t) - (m (t + 1) - m t)`, where `m t` is the value of the objective of round `t` at its
  play.
* `ftrl_regret_le`: [LS, Theorem 28.5]. For a convex `K` and a potential `F` with a derivative
  `F' t` within `K` at each play, the regret is at most
  `(F u - F (a 0)) / η + ∑ t < n, y t (a t - a (t + 1)) - (∑ t < n, D_F(a (t + 1), a t)) / η`,
  with `D_F` the Bregman divergence. The potential need not be convex.
* `ftrl_regret_le_of_strongConvexOn`: [LS, Corollary 28.8]. For an `m`-strongly convex potential
  with respect to the norm of `E`, the regret is at most
  `(F u - F (a 0)) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2`, with `‖y t‖` the operator norm.
* `exists_ftrl`: on a nonempty compact set, FTRL with a potential continuous on that set has
  plays.
* `ftrl_regret_le_sqrt_of_closedBall`: [LS, Proposition 28.6] for FTRL. On the closed unit ball
  of a real inner product space, with the potential `‖b‖ ^ 2 / 2` and the learning rate `1 / √n`,
  the regret after `n` rounds against every point of the ball is at most `√n` for the losses
  `⟪g t, ·⟫` of vectors of norm at most `1`.

## Implementation notes

The FTRL lemma and its telescoping proof are adapted from the LMLPapers project (same author),
where they are stated for gains on the probability simplex; here they hold for losses on any set.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213, 2019.
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

/-- **FTRL lemma** [Ora, Lemma 7.1]. Let the play `a n` of round `n` minimize over `K` the
objective `b ↦ ∑ s < n, y s b + ψ n b`. For every `u ∈ K`, the regret against `u` after `n`
rounds is at most `ψ n u - ψ 0 (a 0)` plus the sum over the rounds of the stability terms
`y t (a t) - (m (t + 1) - m t)`, where `m t = ∑ s < t, y s (a t) + ψ t (a t)` is the value of
the objective of round `t` at its play. -/
theorem sum_apply_sub_le_ftrl (ψ : ℕ → E → ℝ) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : IsMinOn (fun b ↦ ∑ s ∈ range n, y s b + ψ n b) K (a n)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ ψ n u - ψ 0 (a 0) + ∑ t ∈ range n, (y t (a t) -
      ((∑ s ∈ range (t + 1), y s (a (t + 1)) + ψ (t + 1) (a (t + 1))) -
        (∑ s ∈ range t, y s (a t) + ψ t (a t)))) := by
  -- the values of the objectives at the plays telescope, and `a n` beats `u` at round `n`
  have h_tele := sum_range_sub (fun t ↦ ∑ s ∈ range t, y s (a t) + ψ t (a t)) n
  have h_min : ∑ s ∈ range n, y s (a n) + ψ n (a n) ≤ ∑ s ∈ range n, y s u + ψ n u :=
    isMinOn_iff.mp ha u hu
  simp only [range_zero, sum_empty, zero_add] at h_tele
  rw [sum_sub_distrib, h_tele]
  simp only [map_sub, sum_sub_distrib]
  linarith

/-- Let `a` minimize over `K` the function `c ↦ L c + F c`, where `L` is a continuous linear
functional and `F` has derivative `F'` within `K` at `a`. If the segment from `a` to `b` lies in
`K`, then this function increases from `a` to `b` by at least the Bregman divergence
`D_F(b, a)`. -/
lemma bregDiv_le_sub_of_isMinOn {F : E → ℝ} {L F' : E →L[ℝ] ℝ} {a b : E}
    (h_seg : segment ℝ a b ⊆ K) (ha : IsMinOn (fun c ↦ L c + F c) K a)
    (hF' : HasFDerivWithinAt F F' K a) :
    bregDiv F b a F' ≤ L b + F b - (L a + F a) := by
  -- the function has derivative `L + F'` within `K` at `a`, nonnegative towards `b`
  have h_seg' : segment ℝ a (a + (b - a)) ⊆ K := by rwa [add_sub_cancel]
  have h_nonneg := ha.isLocalMinOn.hasFDerivWithinAt_nonneg (L.hasFDerivWithinAt.add hF')
    (mem_posTangentConeAt_of_segment_subset h_seg')
  simp only [add_apply, map_sub] at h_nonneg
  simp only [bregDiv, map_sub]
  linarith

/-- **Regret of follow the regularized leader** [LS, Theorem 28.5]. Let `K` be convex and
`η > 0`. Let each `a t`, for `t ≤ n`, be a play of FTRL on `K` with potential `F` and learning
rate `η` (`IsFTRLPlay`), where `F` has derivative `F' t` within `K` at `a t` for `t < n`.
Then for every `u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η + ∑ t < n, y t (a t - a (t + 1))
  - (∑ t < n, D_F(a (t + 1), a t)) / η`.
[LS] assumes the potential convex; the proof only uses the derivatives at the plays. -/
theorem ftrl_regret_le {F : E → ℝ} (hK : Convex ℝ K) {η : ℝ} (hη : 0 < η)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (ha : ∀ t ≤ n, IsFTRLPlay K F η y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ (F u - F (a 0)) / η +
      ∑ t ∈ range n, y t (a t - a (t + 1)) -
        (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
  -- FTRL with potential `F` and learning rate `η` is FTRL with the regularizers `F / η`
  have h_obj (t : ℕ) (b : E) :
      ∑ s ∈ range t, y s b + F b / η = (η * ∑ s ∈ range t, y s b + F b) / η := by
    field_simp
  have h_ftrl := sum_apply_sub_le_ftrl (fun _ b ↦ F b / η) y a (n := n) (K := K)
    (isMinOn_iff.mpr fun b hb ↦ by
      rw [h_obj, h_obj]
      exact div_le_div_of_nonneg_right (isMinOn_iff.mp (ha n le_rfl).isMinOn b hb) hη.le) hu
  -- each stability term is at most `y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η`
  have h_stab (t : ℕ) (ht : t ∈ range n) :
      y t (a t) - ((∑ s ∈ range (t + 1), y s (a (t + 1)) + F (a (t + 1)) / η) -
        (∑ s ∈ range t, y s (a t) + F (a t) / η)) ≤
      y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η := by
    have ht' := mem_range.mp ht
    have h_min : IsMinOn (fun c ↦ (η • ∑ s ∈ range t, y s) c + F c) K (a t) := by
      simpa using (ha t ht'.le).isMinOn
    have h_breg := bregDiv_le_sub_of_isMinOn (hK.segment_subset (ha t ht'.le).mem
      (ha (t + 1) ht').mem) h_min (hF' t ht')
    simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
      smul_eq_mul] at h_breg
    rw [sum_range_succ, map_sub]
    have : bregDiv F (a (t + 1)) (a t) (F' t) / η ≤
        ∑ s ∈ range t, y s (a (t + 1)) - ∑ s ∈ range t, y s (a t) +
          F (a (t + 1)) / η - F (a t) / η := by
      refine (div_le_div_of_nonneg_right h_breg hη.le).trans_eq ?_
      field_simp
      ring
    linarith
  calc ∑ t ∈ range n, y t (a t - u)
  _ ≤ F u / η - F (a 0) / η + ∑ t ∈ range n, (y t (a t) -
      ((∑ s ∈ range (t + 1), y s (a (t + 1)) + F (a (t + 1)) / η) -
        (∑ s ∈ range t, y s (a t) + F (a t) / η))) := h_ftrl
  _ ≤ F u / η - F (a 0) / η + ∑ t ∈ range n,
      (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η) := by
    exact (add_le_add_iff_left _).mpr (sum_le_sum h_stab)
  _ = (F u - F (a 0)) / η + ∑ t ∈ range n, y t (a t - a (t + 1)) -
      (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
    rw [sum_sub_distrib, sum_div, sub_div]
    ring

/-- **Regret of FTRL with a strongly convex potential** [LS, Corollary 28.8]. Under the
assumptions of `ftrl_regret_le`, if the potential `F` is `m`-strongly convex on `K` for the norm
of `E`, with `m > 0`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2`,
where `‖y t‖` is the operator norm of the loss, the dual norm of the norm of `E`. [LS] states it
with the diameter of `K` for `F` in place of `F u - F (a 0)`. -/
theorem ftrl_regret_le_of_strongConvexOn {F : E → ℝ} {m : ℝ} (hF : StrongConvexOn K m F)
    (hm : 0 < m) {η : ℝ} (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : ∀ t ≤ n, IsFTRLPlay K F η y t (a t))
    (F' : ℕ → E →L[ℝ] ℝ) (hF' : ∀ t < n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (F u - F (a 0)) / η + η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 := by
  refine (ftrl_regret_le hF.1 hη y a ha F' hF' hu).trans ?_
  rw [add_sub_assoc, add_le_add_iff_left, sum_div, ← sum_sub_distrib, mul_sum]
  refine sum_le_sum fun t ht ↦ ?_
  have ht' := mem_range.mp ht
  -- the Bregman divergence of `F` is at least `m / 2` times the squared distance
  have h_breg : m / 2 * ‖a (t + 1) - a t‖ ^ 2 ≤ bregDiv F (a (t + 1)) (a t) (F' t) := by
    have := hF.add_add_le_of_hasFDerivWithinAt (ha t ht'.le).mem (ha (t + 1) ht').mem
      (hF' t ht')
    simp only [bregDiv]
    linarith
  have h_apply : y t (a t - a (t + 1)) ≤ ‖a (t + 1) - a t‖ * ‖y t‖ := by
    rw [norm_sub_rev, mul_comm]
    exact (Real.le_norm_self _).trans ((y t).le_opNorm _)
  -- `x z - m x² / (2 η) ≤ η z² / (2 m)`, a square completion
  set x := ‖a (t + 1) - a t‖
  set z := ‖y t‖
  have h_sq : η / (2 * m) * z ^ 2 - (x * z - m / 2 * x ^ 2 / η) =
      (m * x - η * z) ^ 2 / (2 * m * η) := by
    field_simp
    ring
  have h_nonneg : 0 ≤ (m * x - η * z) ^ 2 / (2 * m * η) := by positivity
  have h_div : -(bregDiv F (a (t + 1)) (a t) (F' t) / η) ≤ -(m / 2 * x ^ 2 / η) :=
    neg_le_neg (div_le_div_of_nonneg_right h_breg hη.le)
  linarith

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
  -- `‖·‖ ^ 2 / 2` is `1`-strongly convex, with derivative `⟪b, ·⟫` at `b`
  have hF : StrongConvexOn (closedBall (0 : E) 1) 1 fun b ↦ ‖b‖ ^ 2 / 2 := by
    refine strongConvexOn_iff_convex.mpr ?_
    convert convexOn_const (0 : ℝ) (convex_closedBall (0 : E) 1) using 2 with b
    ring
  have hF' (t : ℕ) : HasFDerivWithinAt (fun b ↦ ‖b‖ ^ 2 / 2)
      ((2 : ℝ)⁻¹ • (2 • innerSL ℝ (a t))) (closedBall 0 1) (a t) := by
    simpa only [div_eq_mul_inv, mul_comm _ (2 : ℝ)⁻¹] using
      ((hasStrictFDerivAt_norm_sq (a t)).hasFDerivAt.const_mul (2 : ℝ)⁻¹).hasFDerivWithinAt
  have h := ftrl_regret_le_of_strongConvexOn hF one_pos (inv_pos.mpr hsqrt) _ a ha _
    (fun t _ ↦ hF' t) hu
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
