/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Bregman.Euclidean
public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.NumberTheory.Harmonic.Bounds
public import LMLExplore.Analysis.InnerProductSpace.Projection.Minimal
public import LMLExplore.OnlineLearning.MirrorDescent.Learner
public import LMLExplore.OnlineLearning.Regret

/-!
# Online convex optimization and projected online subgradient descent

In online convex optimization, the learner plays `a t` in a set `K` and then suffers the loss
`f t (a t)` of a function `f t : E → ℝ`; the regret against `u ∈ K` after `n` rounds is
`∑ t < n, (f t (a t) - f t u)`. If `g t` is a subgradient of `f t` within `K` at `a t`, this regret
is at most the regret `∑ t < n, g t (a t - u)` of the linear losses `g t` [Ora, Section 2.3]. The
bounds of follow-the-regularized-leader and mirror descent for linear losses chosen from the past
plays therefore apply to convex losses, run on the linearized losses.

On a real inner product space, mirror descent with the potential `‖b‖ ^ 2 / 2` is **projected
online subgradient descent** [Zin03; Ora, Section 2.2]: the next play is the point of `K` nearest
to the gradient step `a t - η t • g t`. Each such step satisfies
`⟪g t, a t - u⟫ ≤ (‖u - a t‖ ^ 2 - ‖u - a (t + 1)‖ ^ 2) / (2 η t) + η t / 2 * ‖g t‖ ^ 2`
[Ora, Lemma 2.12], so that:

* with a constant learning rate `η`, the regret against `u` is at most
  `(‖u - a 0‖ ^ 2 - ‖u - a n‖ ^ 2) / (2 η) + η / 2 * ∑ t < n, ‖g t‖ ^ 2`, on any convex set, bounded
  or not [Ora, Theorem 2.13];
* with nonincreasing learning rates and plays at distance at most `D` from `u`, it is at most
  `(D ^ 2 - ‖u - a n‖ ^ 2) / (2 η (n - 1)) + ∑ t < n, η t / 2 * ‖g t‖ ^ 2`, and the anytime
  learning rate `η t = D / (G √(t + 1))` gives the bound `3 / 2 * D * G * √n` on a set of
  diameter `D`, for subgradients of norm at most `G`;
* for losses `f t` that are `μ t`-strongly convex, the learning rates `η t = 1 / ∑ s ≤ t, μ s`
  give the bound `∑ t < n, ‖g t‖ ^ 2 / (2 ∑ s ≤ t, μ s)` [HAK07; Ora, Theorem 4.7], hence
  `L ^ 2 / (2 μ) * (1 + log n)` for `μ t = μ` and `‖g t‖ ≤ L` [Ora, Corollary 4.8]. On the
  guessing game of the squared losses `(a - y t) ^ 2` on `[0, 1]`, this is `1 + log n`
  [Ora, Example 4.11].

The learner `OnlineLearner.onlineSubgradientDescent K η x₀` runs the algorithm: it is the mirror
descent learner of `LMLExplore.OnlineLearning.MirrorDescent.Learner` for the potential
`‖b‖ ^ 2 / 2`, fed the vectors `g t`. Its plays are the projections of the gradient steps onto a
nonempty complete convex set `K`, and it has the regret guarantees of [Ora, Theorem 2.13] with a
constant and with nonincreasing learning rates.

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner.onlineSubgradientDescent K η x₀`: the projected online
  subgradient descent learner.

## Main statements

* `sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt`: the regret of losses with subgradients
  at the plays is at most the regret of the linearized losses.
* `isMirrorDescentStep_norm_sq_div_two_iff`: the mirror descent steps for the potential
  `‖b‖ ^ 2 / 2` and the loss `⟪g, ·⟫` from `a` are the points of `K` nearest to `a - η • g`.
* `exists_isMirrorDescentStep_norm_sq_div_two`: in a Hilbert space, these steps exist on nonempty
  complete convex sets.
* `inner_sub_sub_norm_sq_div_le`: the stability term of one step of projected online
  subgradient descent.
* `inner_sub_le_of_isMinOn_norm_sub`: [Ora, Lemmas 2.12 and 2.31] one step of projected online
  subgradient descent.
* `onlineSubgradientDescent_regret_le_norm_sub_sq_div`: [Ora, Theorem 2.13] the regret with a
  constant learning rate, with no bound on the diameter.
* `onlineSubgradientDescent_regret_le_of_antitone`: [Ora, Theorem 2.13] the regret with
  nonincreasing learning rates, keeping the last distance `‖u - a n‖`.
* `onlineSubgradientDescent_regret_le`: its form on a set of diameter at most `D`.
* `onlineSubgradientDescent_regret_le_sqrt`: with `η t = D / (G √(t + 1))`, the regret is at most
  `3 / 2 * D * G * √n`.
* `onlineSubgradientDescent_regret_le_sum_norm_sq_div`: [Ora, Theorem 4.7] the regret on losses
  that are strongly convex at the plays, and `onlineSubgradientDescent_regret_le_of_strongConvexOn`
  its form for strongly convex losses.
* `onlineSubgradientDescent_regret_le_mul_one_add_log`: [Ora, Corollary 4.8] logarithmic regret
  for `μ`-strongly convex losses with bounded subgradients.
* `onlineSubgradientDescent_regret_add_one_mul_le_sum_norm_sq_div`: [Ora, Theorem 4.7] with the
  weights `t + 1` and the learning rates `2 / ((t + 2) μ)`, the regret of the weighted losses
  `(t + 1) * f t` is at most `∑ t < n, ‖g t‖ ^ 2 / μ`, as in [Ora, Example 4.12].
* `onlineSubgradientDescent_regret_sq_sub_le_one_add_log`: [Ora, Example 4.11] the guessing game.
* `OnlineLearner.isMinOn_run_onlineSubgradientDescent_of_complete_convex`: the plays of the
  learner are the projections of the gradient steps.
* `OnlineLearner.run_onlineSubgradientDescent_univ_succ`: on the whole space, they are the
  gradient steps themselves.
* `OnlineLearner.hasRegretBound_onlineSubgradientDescent`,
  `OnlineLearner.hasRegretBound_onlineSubgradientDescent_of_antitone`: the regret guarantees of
  the learner [Ora, Theorem 2.13].

## References

* [HAK07] E. Hazan, A. Agarwal and S. Kale, *Logarithmic regret algorithms for online convex
  optimization*, Machine Learning 69 (2007).
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [Zin03] M. Zinkevich, *Online convex programming and generalized infinitesimal gradient ascent*,
  ICML 2003.
-/

public section

open Finset
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

variable {n : ℕ}

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {u : E}

/-- **Linearization of convex losses** [Ora, Section 2.3]. If, for each `t < n`, `g t` is a
subgradient of `f t` within `K` at `a t`, then for every `u ∈ K` the regret of the losses `f t`
against `u` is at most the regret of the linear losses `g t`:
`∑ t < n, (f t (a t) - f t u) ≤ ∑ t < n, g t (a t - u)`. -/
theorem sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt (f : ℕ → E → ℝ)
    (g : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (hg : ∀ t < n, HasSubgradientWithinAt (f t) (g t) K (a t))
    (hu : u ∈ K) :
    ∑ t ∈ range n, (f t (a t) - f t u) ≤ ∑ t ∈ range n, g t (a t - u) := by
  refine sum_le_sum fun t ht ↦ ?_
  have := hasSubgradientWithinAt_iff_le.mp (hg t (mem_range.mp ht)) u hu
  rw [map_sub] at this ⊢
  linarith

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {u : E}

/-- **Mirror descent with the Euclidean potential is projected gradient descent.** For the
potential `‖b‖ ^ 2 / 2`, with derivative `⟪a, ·⟫` at `a`, and the loss `⟪g, ·⟫`, the mirror
descent steps on `K` from `a` with learning rate `η` are the points of `K` nearest to the gradient
step `a - η • g`. -/
theorem isMirrorDescentStep_norm_sq_div_two_iff {η : ℝ} {g a x : E} :
    IsMirrorDescentStep K (fun b : E ↦ ‖b‖ ^ 2 / 2) η (innerSL ℝ g) a (innerSL ℝ a) x ↔
      x ∈ K ∧ IsMinOn (fun b ↦ ‖b - (a - η • g)‖) K x := by
  have hG : innerSL ℝ (a - η • g) = innerSL ℝ a - η • innerSL ℝ g := by
    ext v
    simp
  rw [isMirrorDescentStep_iff_isMinOn_bregDiv hG a (a - η • g) x]
  simp only [bregDiv_norm_sq_div_two, isMinOn_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun c _ ↦ ?_
  rw [div_le_div_iff_of_pos_right two_pos, sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

/-- **Existence of mirror descent steps with the Euclidean potential.** In a real Hilbert space,
on a nonempty complete convex set `K`, there is a mirror descent step on `K` from every point `a`
for the potential `‖b‖ ^ 2 / 2`, with derivative `⟪a, ·⟫` at `a`, for every learning rate `η` and
every loss `y` in the dual: the point of `K` nearest to the gradient step from `a` along the
vector representing `y`. -/
theorem exists_isMirrorDescentStep_norm_sq_div_two [CompleteSpace E] (hK_ne : K.Nonempty)
    (hKc : IsComplete K) (hK : Convex ℝ K) (η : ℝ) (y : E →L[ℝ] ℝ) (a : E) :
    ∃ x, IsMirrorDescentStep K (fun b : E ↦ ‖b‖ ^ 2 / 2) η y a (innerSL ℝ a) x := by
  have hy : innerSL ℝ ((InnerProductSpace.toDual ℝ E).symm y) = y := by
    ext v
    simp [InnerProductSpace.toDual_symm_apply]
  obtain ⟨x, hx, hmin⟩ := exists_isMinOn_norm_sub_of_complete_convex hK_ne hKc hK
    (a - η • (InnerProductSpace.toDual ℝ E).symm y)
  exact ⟨x, hy ▸ isMirrorDescentStep_norm_sq_div_two_iff.mpr ⟨hx, hmin⟩⟩

/-- **Stability of one step of projected online subgradient descent.** For `η > 0`,
`⟪g, a - b⟫ - ‖b - a‖ ^ 2 / 2 / η ≤ η / 2 * ‖g‖ ^ 2`: the linear gain of a step from `a` to `b`
minus its Bregman divergence for the potential `‖·‖ ^ 2 / 2`, divided by `η`, is at most
`η / 2 * ‖g‖ ^ 2`. -/
theorem inner_sub_sub_norm_sq_div_le {η : ℝ} (hη : 0 < η) (g a b : E) :
    ⟪g, a - b⟫ - ‖b - a‖ ^ 2 / 2 / η ≤ η / 2 * ‖g‖ ^ 2 := by
  have h := apply_sub_sub_div_le_of_mul_norm_sq_le one_pos hη (innerSL ℝ g)
    (one_div_mul_eq_div 2 (‖b - a‖ ^ 2)).le
  rwa [mul_one, innerSL_apply_norm, innerSL_apply_apply] at h

/-- **One step of projected online subgradient descent** [Ora, Lemmas 2.12 and 2.31]. Let `K` be
convex, let `η > 0`, and let `x ∈ K` be a point of `K` nearest to the gradient step `a - η • g`.
Then for every `u ∈ K`,
`⟪g, a - u⟫ ≤ (‖u - a‖ ^ 2 - ‖u - x‖ ^ 2) / (2 η) + η / 2 * ‖g‖ ^ 2`.
The point `a` need not lie in `K`. -/
theorem inner_sub_le_of_isMinOn_norm_sub (hK : Convex ℝ K) {η : ℝ} (hη : 0 < η) {g a x : E}
    (hx : x ∈ K) (hmin : IsMinOn (fun b ↦ ‖b - (a - η • g)‖) K x) (hu : u ∈ K) :
    ⟪g, a - u⟫ ≤ (‖u - a‖ ^ 2 - ‖u - x‖ ^ 2) / (2 * η) + η / 2 * ‖g‖ ^ 2 := by
  -- the one-step inequality of mirror descent with the potential `‖b‖ ^ 2 / 2`
  have h := (isMirrorDescentStep_norm_sq_div_two_iff.mpr ⟨hx, hmin⟩).apply_sub_le hK hη
    (hasFDerivAt_norm_sq_div_two x).hasFDerivWithinAt hu
  -- its stability term
  have h_stab := inner_sub_sub_norm_sq_div_le hη g a x
  simp only [bregDiv_norm_sq_div_two, innerSL_apply_apply] at h
  have h_eq : (‖u - a‖ ^ 2 / 2 - ‖u - x‖ ^ 2 / 2 - ‖x - a‖ ^ 2 / 2) / η =
      (‖u - a‖ ^ 2 - ‖u - x‖ ^ 2) / (2 * η) - ‖x - a‖ ^ 2 / 2 / η := by
    field_simp
  linarith

/-- **Regret of projected online subgradient descent with a constant learning rate**
[Ora, Theorem 2.13, second bound]. Let `K` be convex and `η > 0`. Let `g t` be a subgradient of
the loss `f t` within `K` at `a t`, and let `a (t + 1)` be a point of `K` nearest to
`a t - η • g t`, for `t < n`. Then for every `u ∈ K`,
`regret f a u n ≤ (‖u - a 0‖ ^ 2 - ‖u - a n‖ ^ 2) / (2 η) + η / 2 * ∑ t < n, ‖g t‖ ^ 2`.
No bound on the diameter of `K` is needed, so this applies on unbounded sets. -/
theorem onlineSubgradientDescent_regret_le_norm_sub_sq_div (hK : Convex ℝ K) {η : ℝ}
    (hη : 0 < η) (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t))
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn (fun b ↦ ‖b - (a t - η • g t)‖) K (a (t + 1)))
    (hu : u ∈ K) :
    regret f a u n ≤
      (‖u - a 0‖ ^ 2 - ‖u - a n‖ ^ 2) / (2 * η) + η / 2 * ∑ t ∈ range n, ‖g t‖ ^ 2 := by
  rw [regret_def]
  refine (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f _ a hg hu).trans ?_
  -- each round is bounded by its one-step inequality, and the distances to `u` telescope
  have h_step (t : ℕ) (ht : t ∈ range n) : innerSL ℝ (g t) (a t - u) ≤
      (‖u - a t‖ ^ 2 - ‖u - a (t + 1)‖ ^ 2) / (2 * η) + η / 2 * ‖g t‖ ^ 2 := by
    have ht' := mem_range.mp ht
    simpa using inner_sub_le_of_isMinOn_norm_sub hK hη (ha t ht').1 (ha t ht').2 hu
  refine (sum_le_sum h_step).trans_eq ?_
  rw [sum_add_distrib, ← sum_div, sum_range_sub' (fun t ↦ ‖u - a t‖ ^ 2), mul_sum]

/-- **Regret of projected online subgradient descent with nonincreasing learning rates**
[Ora, Theorem 2.13, first bound]. Let `K` be convex and let the learning rates `η t > 0` be
nonincreasing. Let `g t` be a subgradient of the loss `f t` within `K` at `a t`, and let
`a (t + 1)` be a point of `K` nearest to `a t - η t • g t`, for `t < n`. If `n > 0` and
`‖u - a t‖ ≤ D` for `t < n`, then for `u ∈ K`,
`regret f a u n ≤ (D ^ 2 - ‖u - a n‖ ^ 2) / (2 η (n - 1)) + ∑ t < n, η t / 2 * ‖g t‖ ^ 2`.
Only the distances from the plays to `u` are bounded, not the diameter of `K`; the bound keeps
the term `- ‖u - a n‖ ^ 2 / (2 η (n - 1))`. -/
theorem onlineSubgradientDescent_regret_le_of_antitone (hK : Convex ℝ K) {η : ℕ → ℝ}
    (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t))
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn (fun b ↦ ‖b - (a t - η t • g t)‖) K (a (t + 1)))
    (hn : 0 < n) {D : ℝ} (hD : ∀ t < n, ‖u - a t‖ ≤ D) (hu : u ∈ K) :
    regret f a u n ≤
      (D ^ 2 - ‖u - a n‖ ^ 2) / (2 * η (n - 1)) + ∑ t ∈ range n, η t / 2 * ‖g t‖ ^ 2 := by
  have ha' (t : ℕ) (ht : t < n) := isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  -- the Bregman divergences to `u` are `‖u - a t‖ ^ 2 / 2 ≤ D ^ 2 / 2`
  have hDu (t : ℕ) (ht : t < n) :
      bregDiv (fun b : E ↦ ‖b‖ ^ 2 / 2) u (a t) (innerSL ℝ (a t)) ≤ D ^ 2 / 2 := by
    rw [bregDiv_norm_sq_div_two]
    gcongr
    exact hD t ht
  have h := sum_apply_sub_le_mirrorDescent_of_antitone hK hη hη_anti (fun t ↦ innerSL ℝ (g t)) a
    (fun t ↦ innerSL ℝ (a t)) ha' (fun t _ ↦ (hasFDerivAt_norm_sq_div_two _).hasFDerivWithinAt)
    hn hDu hu
  -- the stability term of round `t` is at most `η t / 2 * ‖g t‖ ^ 2`
  have h_stab : ∑ t ∈ range n, (innerSL ℝ (g t) (a t - a (t + 1)) -
      bregDiv (fun b : E ↦ ‖b‖ ^ 2 / 2) (a (t + 1)) (a t) (innerSL ℝ (a t)) / η t) ≤
        ∑ t ∈ range n, η t / 2 * ‖g t‖ ^ 2 := by
    refine sum_le_sum fun t _ ↦ ?_
    rw [bregDiv_norm_sq_div_two, innerSL_apply_apply]
    exact inner_sub_sub_norm_sq_div_le (hη t) (g t) (a t) (a (t + 1))
  rw [bregDiv_norm_sq_div_two] at h
  have h_eq : (D ^ 2 / 2 - ‖u - a n‖ ^ 2 / 2) / η (n - 1) =
      (D ^ 2 - ‖u - a n‖ ^ 2) / (2 * η (n - 1)) := by
    field_simp
  rw [regret_def]
  refine (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f _ a hg hu).trans ?_
  linarith

/-- **Regret of projected online subgradient descent** [Ora, Section 2.2]. Let `K` be convex with
`‖x - y‖ ≤ D` for `x, y ∈ K`, and let the learning rates `η t > 0` be nonincreasing. Let `g t` be
a subgradient of the loss `f t` within `K` at `a t`, for `t < n`, let `a 0 ∈ K`, and let each
`a (t + 1)` be a point of `K` nearest to `a t - η t • g t`. Then for every `u ∈ K`,
`∑ t < n, (f t (a t) - f t u) ≤ D ^ 2 / (2 η (n - 1)) + ∑ t < n, η t / 2 * ‖g t‖ ^ 2`.
The losses may be chosen adaptively from the past plays. -/
theorem onlineSubgradientDescent_regret_le (hK : Convex ℝ K) {η : ℕ → ℝ} (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) {D : ℝ} (hKD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (f : ℕ → E → ℝ)
    (g a : ℕ → E) (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t))
    (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn (fun b ↦ ‖b - (a t - η t • g t)‖) K (a (t + 1)))
    (hu : u ∈ K) :
    ∑ t ∈ range n, (f t (a t) - f t u) ≤
      D ^ 2 / (2 * η (n - 1)) + ∑ t ∈ range n, η t / 2 * ‖g t‖ ^ 2 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa using div_nonneg (sq_nonneg D) (mul_pos two_pos (hη _)).le
  have h_mem := mem_of_isMirrorDescentStep ha0 fun t ht ↦
    isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  have h := onlineSubgradientDescent_regret_le_of_antitone hK hη hη_anti f g a hg ha hn
    (fun t ht ↦ hKD u hu (a t) (h_mem t ht.le)) hu
  -- the last distance `‖u - a n‖` only decreases the bound
  have h_last : 0 ≤ ‖u - a n‖ ^ 2 / (2 * η (n - 1)) := by
    have := hη (n - 1)
    positivity
  rw [regret_def, sub_div] at h
  linarith

/-- **Projected online subgradient descent with an anytime learning rate** [Ora, Section 2.2].
Let `K` be convex with `‖x - y‖ ≤ D` for `x, y ∈ K`, and let `g t` be a subgradient of the loss
`f t` within `K` at `a t` with `‖g t‖ ≤ G`, for `t < n`. Let `a 0 ∈ K` and let each `a (t + 1)`
be a point of `K` nearest to `a t - η t • g t`, for the learning rate
`η t = D / (G √(t + 1))`, which does not depend on the horizon. Then for every `u ∈ K`,
`∑ t < n, (f t (a t) - f t u) ≤ 3 / 2 * D * G * √n`. -/
theorem onlineSubgradientDescent_regret_le_sqrt (hK : Convex ℝ K) {D G : ℝ}
    (hKD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t))
    (hgG : ∀ t < n, ‖g t‖ ≤ G) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧
      IsMinOn (fun b ↦ ‖b - (a t - (D / (G * √((t : ℝ) + 1))) • g t)‖) K (a (t + 1)))
    (hu : u ∈ K) :
    ∑ t ∈ range n, (f t (a t) - f t u) ≤ 3 / 2 * D * G * √n := by
  rcases n with _ | n
  · simp
  have h_mem := mem_of_isMirrorDescentStep (η := fun t ↦ D / (G * √((t : ℝ) + 1))) ha0
    fun t ht ↦ isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  have hD : 0 ≤ D := (norm_nonneg _).trans (hKD u hu u hu)
  have hG : 0 ≤ G := (norm_nonneg _).trans (hgG 0 n.succ_pos)
  have h_lin := sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f _ a hg hu
  rcases hD.eq_or_lt with hD0 | hD0
  · -- if `D = 0`, then `K` is the single point `u` and every round has zero regret
    refine h_lin.trans ?_
    simp only [← hD0, mul_zero, zero_mul]
    refine sum_nonpos fun t ht ↦ ?_
    have h_dist := hKD (a t) (h_mem t (mem_range.mp ht).le) u hu
    rw [← hD0, norm_le_zero_iff, sub_eq_zero] at h_dist
    simp [h_dist]
  rcases hG.eq_or_lt with hG0 | hG0
  · -- if `G = 0`, then every subgradient vanishes and every round has zero regret
    refine h_lin.trans ?_
    simp only [← hG0, mul_zero, zero_mul]
    refine sum_nonpos fun t ht ↦ ?_
    have h_norm := hgG t (mem_range.mp ht)
    rw [← hG0, norm_le_zero_iff] at h_norm
    simp [h_norm]
  set η : ℕ → ℝ := fun t ↦ D / (G * √((t : ℝ) + 1)) with hη_def
  have hη (t : ℕ) : 0 < η t := by positivity
  have hη_anti : Antitone η := fun s t hst ↦
    div_le_div_of_nonneg_left hD (by positivity) (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hst 1)) hG)
  have h := onlineSubgradientDescent_regret_le hK hη hη_anti hKD f g a hg ha0 ha hu
  -- the penalty is `D G √n / 2`, and the stability terms add up to at most `D G √n`
  have h_pen : D ^ 2 / (2 * η (n + 1 - 1)) = D * G * √((n : ℝ) + 1) / 2 := by
    simp only [hη_def, Nat.add_sub_cancel]
    field_simp
  have h_stab : ∑ t ∈ range (n + 1), η t / 2 * ‖g t‖ ^ 2 ≤
      D * G / 2 * ∑ t ∈ range (n + 1), (√((t : ℝ) + 1))⁻¹ := by
    rw [mul_sum]
    refine sum_le_sum fun t ht ↦ ?_
    have h_sq : ‖g t‖ ^ 2 ≤ G ^ 2 := by
      gcongr
      exact hgG t (mem_range.mp ht)
    calc η t / 2 * ‖g t‖ ^ 2 ≤ η t / 2 * G ^ 2 := by gcongr
      _ = D * G / 2 * (√((t : ℝ) + 1))⁻¹ := by
        simp only [hη_def]
        field_simp
  have h_sum := Real.sum_range_inv_sqrt_add_one_le (n + 1)
  have h_DG : 0 ≤ D * G / 2 := by positivity
  rw [Nat.cast_succ] at h_sum ⊢
  have := mul_le_mul_of_nonneg_left h_sum h_DG
  linarith

/-- **Regret of projected online subgradient descent on strongly convex losses**
[Ora, Theorem 4.7]. Let `K` be convex, and let the moduli `μ t` have positive partial sums
`0 < ∑ s ≤ t, μ s`, for `t < n`. Let each loss `f t` lie above the paraboloid
`f t (a t) + ⟪g t, · - a t⟫ + μ t / 2 * ‖· - a t‖ ^ 2` on `K` (strong convexity at the plays), and
let `a (t + 1)` be a point of `K` nearest to `a t - η t • g t` for the learning rate
`η t = 1 / ∑ s ≤ t, μ s`, for `t < n`. Then for every `u ∈ K`,
`regret f a u n ≤ ∑ t < n, ‖g t‖ ^ 2 / (2 ∑ s ≤ t, μ s)`.
The moduli `μ t` need not be nonnegative, and `a 0` need not lie in `K`. -/
theorem onlineSubgradientDescent_regret_le_sum_norm_sq_div (hK : Convex ℝ K) (f : ℕ → E → ℝ)
    (g a : ℕ → E) {μ : ℕ → ℝ} (hμ : ∀ t < n, 0 < ∑ s ∈ range (t + 1), μ s)
    (hf : ∀ t < n, ∀ v ∈ K, f t (a t) + ⟪g t, v - a t⟫ + μ t / 2 * ‖v - a t‖ ^ 2 ≤ f t v)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧
      IsMinOn (fun b ↦ ‖b - (a t - (∑ s ∈ range (t + 1), μ s)⁻¹ • g t)‖) K (a (t + 1)))
    (hu : u ∈ K) :
    regret f a u n ≤ ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * ∑ s ∈ range (t + 1), μ s) := by
  set S : ℕ → ℝ := fun t ↦ ∑ s ∈ range t, μ s with hS_def
  have hS (t : ℕ) : S (t + 1) = S t + μ t := sum_range_succ μ t
  -- the potential `S t / 2 * ‖u - a t‖ ^ 2` decreases by the regret of round `t`, up to the
  -- stability term `‖g t‖ ^ 2 / (2 S (t + 1))`
  have h_step (t : ℕ) (ht : t ∈ range n) : f t (a t) - f t u ≤
      (S t / 2 * ‖u - a t‖ ^ 2 - S (t + 1) / 2 * ‖u - a (t + 1)‖ ^ 2) +
        ‖g t‖ ^ 2 / (2 * S (t + 1)) := by
    have ht' := mem_range.mp ht
    have hpos : 0 < S (t + 1) := hμ t ht'
    have h_one := inner_sub_le_of_isMinOn_norm_sub hK (inv_pos.mpr hpos) (ha t ht').1
      (ha t ht').2 hu
    have h_f := hf t ht' u hu
    have h_inner : ⟪g t, u - a t⟫ = -⟪g t, a t - u⟫ := by rw [← inner_neg_right, neg_sub]
    have h_eq₁ : (‖u - a t‖ ^ 2 - ‖u - a (t + 1)‖ ^ 2) / (2 * (S (t + 1))⁻¹) =
        S (t + 1) / 2 * ‖u - a t‖ ^ 2 - S (t + 1) / 2 * ‖u - a (t + 1)‖ ^ 2 := by
      field_simp
    have h_eq₂ : (S (t + 1))⁻¹ / 2 * ‖g t‖ ^ 2 = ‖g t‖ ^ 2 / (2 * S (t + 1)) := by
      field_simp
    have h_eq₃ : S (t + 1) / 2 * ‖u - a t‖ ^ 2 =
        S t / 2 * ‖u - a t‖ ^ 2 + μ t / 2 * ‖u - a t‖ ^ 2 := by
      rw [hS]
      ring
    linarith
  rw [regret_def]
  refine (sum_le_sum h_step).trans ?_
  rw [sum_add_distrib, sum_range_sub' (fun t ↦ S t / 2 * ‖u - a t‖ ^ 2)]
  -- the final potential `S n / 2 * ‖u - a n‖ ^ 2` is nonnegative
  have h_last : 0 ≤ S n / 2 * ‖u - a n‖ ^ 2 := by
    rcases n with _ | m
    · simp [hS_def]
    · have := hμ m m.lt_succ_self
      positivity
  simp only [hS_def, sum_range_zero, zero_div, zero_mul, zero_sub] at h_last ⊢
  linarith

/-- **Regret of projected online subgradient descent on strongly convex losses**
[Ora, Theorem 4.7]. Let `K` be convex, let the loss `f t` be `μ t`-strongly convex on `K`, with
positive partial sums `0 < ∑ s ≤ t, μ s`, and let `g t` be a subgradient of `f t` within `K` at
`a t`, for `t < n`. Let `a 0 ∈ K`, and let `a (t + 1)` be a point of `K` nearest to
`a t - η t • g t` for the learning rate `η t = 1 / ∑ s ≤ t, μ s`, for `t < n`. Then for every
`u ∈ K`, `regret f a u n ≤ ∑ t < n, ‖g t‖ ^ 2 / (2 ∑ s ≤ t, μ s)`. -/
theorem onlineSubgradientDescent_regret_le_of_strongConvexOn (hK : Convex ℝ K) (f : ℕ → E → ℝ)
    (g a : ℕ → E) {μ : ℕ → ℝ} (hμ : ∀ t < n, 0 < ∑ s ∈ range (t + 1), μ s)
    (hf : ∀ t < n, StrongConvexOn K (μ t) (f t))
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t)) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧
      IsMinOn (fun b ↦ ‖b - (a t - (∑ s ∈ range (t + 1), μ s)⁻¹ • g t)‖) K (a (t + 1)))
    (hu : u ∈ K) :
    regret f a u n ≤ ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * ∑ s ∈ range (t + 1), μ s) := by
  have h_mem := mem_of_isMirrorDescentStep ha0 fun t ht ↦
    isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  refine onlineSubgradientDescent_regret_le_sum_norm_sq_div hK f g a hμ (fun t ht v hv ↦ ?_) ha hu
  simpa using (hf t ht).add_add_le_of_hasSubgradientWithinAt (h_mem t ht.le) hv (hg t ht)

/-- **Logarithmic regret of projected online subgradient descent on strongly convex losses**
[Ora, Corollary 4.8]. Let `K` be convex and `μ > 0`. Let the loss `f t` be `μ`-strongly convex
on `K`, and let `g t` be a subgradient of `f t` within `K` at `a t` with `‖g t‖ ≤ L`, for `t < n`.
Let `a 0 ∈ K`, and let `a (t + 1)` be a point of `K` nearest to `a t - η t • g t` for the learning
rate `η t = 1 / ((t + 1) μ)`, for `t < n`. Then for every `u ∈ K`,
`regret f a u n ≤ L ^ 2 / (2 μ) * (1 + log n)`. -/
theorem onlineSubgradientDescent_regret_le_mul_one_add_log (hK : Convex ℝ K) (f : ℕ → E → ℝ)
    (g a : ℕ → E) {μ L : ℝ} (hμ : 0 < μ) (hf : ∀ t < n, StrongConvexOn K μ (f t))
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t))
    (hgL : ∀ t < n, ‖g t‖ ≤ L) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧
      IsMinOn (fun b ↦ ‖b - (a t - (((t : ℝ) + 1) * μ)⁻¹ • g t)‖) K (a (t + 1)))
    (hu : u ∈ K) :
    regret f a u n ≤ L ^ 2 / (2 * μ) * (1 + Real.log n) := by
  have h_sum (t : ℕ) : ∑ s ∈ range (t + 1), μ = ((t : ℝ) + 1) * μ := by simp
  have h := onlineSubgradientDescent_regret_le_of_strongConvexOn hK f g a (μ := fun _ ↦ μ)
    (fun t _ ↦ by rw [h_sum]; positivity) hf hg ha0 (fun t ht ↦ by rw [h_sum]; exact ha t ht) hu
  simp only [h_sum] at h
  refine h.trans ?_
  -- each stability term is at most `L ^ 2 / (2 μ) * (t + 1)⁻¹`
  have h_term : ∀ t ∈ range n, ‖g t‖ ^ 2 / (2 * (((t : ℝ) + 1) * μ)) ≤
      L ^ 2 / (2 * μ) * ((t : ℝ) + 1)⁻¹ := by
    intro t ht
    have h_sq : ‖g t‖ ^ 2 ≤ L ^ 2 := by
      gcongr
      exact hgL t (mem_range.mp ht)
    calc ‖g t‖ ^ 2 / (2 * (((t : ℝ) + 1) * μ)) ≤ L ^ 2 / (2 * (((t : ℝ) + 1) * μ)) := by gcongr
      _ = L ^ 2 / (2 * μ) * ((t : ℝ) + 1)⁻¹ := by field_simp
  refine (sum_le_sum h_term).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (Real.sum_range_inv_add_one_le n) (by positivity)

/-- **Projected online subgradient descent with the weights `t + 1`** [Ora, Theorem 4.7,
Example 4.12]. Let `K` be convex and `μ > 0`, and let each loss `f t` lie above the paraboloid
`f t (a t) + ⟪g t, · - a t⟫ + μ / 2 * ‖· - a t‖ ^ 2` on `K`, for `t < n`. Let `a (t + 1)` be a
point of `K` nearest to `a t - (2 / ((t + 2) μ)) • g t`, for `t < n`. Then for every `u ∈ K`, the
weighted losses `(t + 1) * f t` have regret at most `∑ t < n, ‖g t‖ ^ 2 / μ`. These weighted
losses are `(t + 1) μ`-strongly convex at the plays, with the subgradients `(t + 1) • g t`, and the
steps are those of `onlineSubgradientDescent_regret_le_sum_norm_sq_div` for them. -/
theorem onlineSubgradientDescent_regret_add_one_mul_le_sum_norm_sq_div (hK : Convex ℝ K)
    (f : ℕ → E → ℝ) (g a : ℕ → E) {μ : ℝ} (hμ : 0 < μ)
    (hf : ∀ t < n, ∀ v ∈ K, f t (a t) + ⟪g t, v - a t⟫ + μ / 2 * ‖v - a t‖ ^ 2 ≤ f t v)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧
      IsMinOn (fun b ↦ ‖b - (a t - (2 / (((t : ℝ) + 2) * μ)) • g t)‖) K (a (t + 1)))
    (hu : u ∈ K) :
    regret (fun t y ↦ ((t : ℝ) + 1) * f t y) a u n ≤ ∑ t ∈ range n, ‖g t‖ ^ 2 / μ := by
  -- the partial sums of the moduli `(s + 1) μ` of the weighted losses
  have h_sum (t : ℕ) : ∑ s ∈ range (t + 1), ((s : ℝ) + 1) * μ = (t + 1) * (t + 2) / 2 * μ := by
    have h := two_mul_sum_range_cast_add_one (α := ℝ) (t + 1)
    push_cast at h
    rw [← sum_mul]
    linear_combination μ / 2 * h
  have h_osd := onlineSubgradientDescent_regret_le_sum_norm_sq_div hK
    (fun t y ↦ ((t : ℝ) + 1) * f t y) (fun t ↦ ((t : ℝ) + 1) • g t) a
    (μ := fun t ↦ ((t : ℝ) + 1) * μ) (fun t _ ↦ by rw [h_sum]; positivity)
    (fun t ht v hv ↦ by
      have := mul_le_mul_of_nonneg_left (hf t ht v hv) (by positivity : (0 : ℝ) ≤ t + 1)
      rw [real_inner_smul_left]
      linarith)
    (fun t ht ↦ by
      have h_rate : (∑ s ∈ range (t + 1), ((s : ℝ) + 1) * μ)⁻¹ • ((t : ℝ) + 1) • g t =
          (2 / (((t : ℝ) + 2) * μ)) • g t := by
        rw [h_sum, smul_smul]
        congr 1
        field_simp
      rw [h_rate]
      exact ha t ht)
    hu
  refine h_osd.trans (sum_le_sum fun t _ ↦ ?_)
  rw [h_sum, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ t + 1),
    div_le_div_iff₀ (by positivity) hμ]
  have h0 : 0 ≤ ‖g t‖ ^ 2 * μ * ((t : ℝ) + 1) := by positivity
  nlinarith [h0]

/-- **Online subgradient descent on the guessing game** [Ora, Example 4.11]. Let the outcomes
`y t` lie in `[0, 1]`, and let the plays start at `x 0 ∈ [0, 1]` and follow
`x (t + 1) = x t - (x t - y t) / (t + 1)` for `t < n`: this is projected online subgradient descent
on `[0, 1]` for the `2`-strongly convex squared losses `(a - y t) ^ 2`, with gradient
`2 (x t - y t)` and learning rate `1 / (2 (t + 1))`, whose steps stay in `[0, 1]`. Then the
regret of the squared losses against every `u ∈ [0, 1]` is at most `1 + log n`. -/
theorem onlineSubgradientDescent_regret_sq_sub_le_one_add_log (x y : ℕ → ℝ) {u : ℝ} {n : ℕ}
    (hy : ∀ t < n, y t ∈ Set.Icc 0 1) (hx0 : x 0 ∈ Set.Icc 0 1)
    (hx : ∀ t < n, x (t + 1) = x t - (x t - y t) / (t + 1)) (hu : u ∈ Set.Icc 0 1) :
    regret (fun t a ↦ (a - y t) ^ 2) x u n ≤ 1 + Real.log n := by
  -- the plays are convex combinations of the previous play and outcome, so they stay in `[0, 1]`
  have h_mem (t : ℕ) : t ≤ n → x t ∈ Set.Icc 0 1 := by
    induction t with
    | zero => exact fun _ ↦ hx0
    | succ t ih =>
      intro ht
      have ⟨h0, h1⟩ := ih (Nat.le_of_succ_le ht)
      have ⟨hy0, hy1⟩ := hy t ht
      have h_eq : x (t + 1) = (t * x t + y t) / (t + 1) := by
        rw [hx t ht]
        field_simp
        ring
      rw [h_eq]
      constructor
      · positivity
      · rw [div_le_one (by positivity)]
        nlinarith
  -- the gradients `2 (x t - y t)` of the squared losses are bounded by `2`
  have hgL (t : ℕ) (ht : t < n) : ‖2 * (x t - y t)‖ ≤ 2 := by
    have ⟨h0, h1⟩ := h_mem t ht.le
    have ⟨hy0, hy1⟩ := hy t ht
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- the gradient steps are the plays, so they are their own nearest points in `[0, 1]`
  have ha (t : ℕ) (ht : t < n) : x (t + 1) ∈ Set.Icc 0 1 ∧ IsMinOn
      (fun b ↦ ‖b - (x t - (((t : ℝ) + 1) * 2)⁻¹ • (2 * (x t - y t)))‖) (Set.Icc 0 1)
      (x (t + 1)) := by
    refine ⟨h_mem (t + 1) ht, isMinOn_iff.mpr fun b _ ↦ ?_⟩
    have h_step : x t - (((t : ℝ) + 1) * 2)⁻¹ • (2 * (x t - y t)) = x (t + 1) := by
      rw [hx t ht, smul_eq_mul]
      field_simp
    rw [h_step, sub_self, norm_zero]
    exact norm_nonneg _
  have h := onlineSubgradientDescent_regret_le_mul_one_add_log (convex_Icc (0 : ℝ) 1) _
    (fun t ↦ 2 * (x t - y t)) x two_pos (fun t _ ↦ strongConvexOn_sq_sub (convex_Icc 0 1) (y t))
    (fun t _ ↦ hasSubgradientWithinAt_sq_sub _ (x t) (y t)) hgL hx0 ha hu
  norm_num at h
  exact h

namespace OnlineLearner

variable {C : Type*} {η : ℕ → ℝ} {x₀ : E}

/-- The **projected online subgradient descent learner** on `K` with learning rates `η` and first
play `x₀` [Zin03; Ora, Section 2.2]. Its feedback at round `t` is a vector `g t`: the gradient of
the linear loss `⟪g t, ·⟫`, or a subgradient of a convex loss at the play. At round `t + 1` it
plays a point of `K` nearest to the gradient step `x t - η t • g t` from its play `x t` of round
`t` when there is one (`isMinOn_run_onlineSubgradientDescent`), and `x t` otherwise. It is the
mirror descent learner for the potential `‖b‖ ^ 2 / 2`, whose mirror descent steps are these
nearest points (`isMirrorDescentStep_norm_sq_div_two_iff`), fed the losses `⟪g t, ·⟫`. It ignores
the contexts. -/
noncomputable def onlineSubgradientDescent (K : Set E) (η : ℕ → ℝ) (x₀ : E) :
    OnlineLearner C E E :=
  ofUpdate x₀ fun t g a ↦
    mirrorDescentStep K (fun b ↦ ‖b‖ ^ 2 / 2) (η t) (innerSL ℝ g) a (innerSL ℝ a)

/-- The first play of the projected online subgradient descent learner is `x₀`. -/
@[simp]
lemma run_onlineSubgradientDescent_zero (c : ℕ → C) (g : ℕ → E) :
    (onlineSubgradientDescent K η x₀).run c g 0 = x₀ :=
  run_ofUpdate_zero c g

/-- The play of round `t + 1` of the projected online subgradient descent learner is the chosen
mirror descent step from its play of round `t` for the potential `‖b‖ ^ 2 / 2` and the loss
`⟪g t, ·⟫`. -/
@[simp]
lemma run_onlineSubgradientDescent_succ (c : ℕ → C) (g : ℕ → E) (t : ℕ) :
    (onlineSubgradientDescent K η x₀).run c g (t + 1) =
      mirrorDescentStep K (fun b ↦ ‖b‖ ^ 2 / 2) (η t) (innerSL ℝ (g t))
        ((onlineSubgradientDescent K η x₀).run c g t)
        (innerSL ℝ ((onlineSubgradientDescent K η x₀).run c g t)) :=
  run_ofUpdate_succ c g t

/-- The plays of the projected online subgradient descent learner started in `K` lie in `K`. -/
lemma run_onlineSubgradientDescent_mem (hx₀ : x₀ ∈ K) (c : ℕ → C) (g : ℕ → E) (t : ℕ) :
    (onlineSubgradientDescent K η x₀).run c g t ∈ K :=
  run_ofUpdate_mem hx₀ (fun _ _ _ ↦ mirrorDescentStep_mem) c g t

/-- **The projected online subgradient descent learner projects the gradient steps.** At every
round `t` where `K` has a point nearest to the gradient step `x t - η t • g t` from the play `x t`
of the learner, its next play is such a point. -/
theorem isMinOn_run_onlineSubgradientDescent (c : ℕ → C) (g : ℕ → E) {t : ℕ}
    (h : ∃ x ∈ K, IsMinOn
      (fun b ↦ ‖b - ((onlineSubgradientDescent K η x₀).run c g t - η t • g t)‖) K x) :
    IsMinOn (fun b ↦ ‖b - ((onlineSubgradientDescent K η x₀).run c g t - η t • g t)‖) K
      ((onlineSubgradientDescent K η x₀).run c g (t + 1)) := by
  obtain ⟨x, hx, hmin⟩ := h
  rw [run_onlineSubgradientDescent_succ]
  exact (isMirrorDescentStep_norm_sq_div_two_iff.mp (isMirrorDescentStep_mirrorDescentStep
    ⟨x, isMirrorDescentStep_norm_sq_div_two_iff.mpr ⟨hx, hmin⟩⟩)).2

/-- On a nonempty complete convex set `K`, for instance a nonempty closed convex set of a Hilbert
space, each play of the projected online subgradient descent learner after the first is the point
of `K` nearest to the gradient step from the previous play. -/
theorem isMinOn_run_onlineSubgradientDescent_of_complete_convex (hK_ne : K.Nonempty)
    (hKc : IsComplete K) (hK : Convex ℝ K) (c : ℕ → C) (g : ℕ → E) (t : ℕ) :
    IsMinOn (fun b ↦ ‖b - ((onlineSubgradientDescent K η x₀).run c g t - η t • g t)‖) K
      ((onlineSubgradientDescent K η x₀).run c g (t + 1)) :=
  isMinOn_run_onlineSubgradientDescent c g <|
    exists_isMinOn_norm_sub_of_complete_convex hK_ne hKc hK _

/-- **Unprojected online subgradient descent.** On the whole space, each play of the online
subgradient descent learner after the first is the gradient step `x t - η t • g t` from the
previous play. -/
@[simp high]
theorem run_onlineSubgradientDescent_univ_succ (c : ℕ → C) (g : ℕ → E) (t : ℕ) :
    (onlineSubgradientDescent Set.univ η x₀).run c g (t + 1) =
      (onlineSubgradientDescent Set.univ η x₀).run c g t - η t • g t := by
  set z := (onlineSubgradientDescent Set.univ η x₀).run c g t - η t • g t with hz
  -- the gradient step `z` itself is the point of the whole space nearest to `z`
  have h := isMinOn_iff.mp (isMinOn_run_onlineSubgradientDescent (K := Set.univ) (η := η)
    (x₀ := x₀) (t := t) c g
    ⟨z, Set.mem_univ z, isMinOn_iff.mpr fun b _ ↦ by simp [z]⟩) z (Set.mem_univ z)
  rwa [← hz, sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] at h

/-- **Regret guarantee of the projected online subgradient descent learner with a constant learning
rate** [Ora, Theorem 2.13]. Let `K` be a complete convex set, for instance a closed convex set of
a Hilbert space, let `x₀ ∈ K` and `η > 0`. For every sequence of vectors `g` and every horizon `n`,
the regret of the linear losses `⟪g t, ·⟫` of the plays `x` of the learner with the constant
learning rate `η` against every `u ∈ K` is at most
`(‖u - x₀‖ ^ 2 - ‖u - x n‖ ^ 2) / (2 η) + η / 2 * ∑ t < n, ‖g t‖ ^ 2`.
No bound on the diameter of `K` is needed, so this applies on unbounded sets. -/
theorem hasRegretBound_onlineSubgradientDescent (hKc : IsComplete K) (hK : Convex ℝ K)
    (hx₀ : x₀ ∈ K) {η : ℝ} (hη : 0 < η) :
    (onlineSubgradientDescent (C := C) K (fun _ ↦ η) x₀).HasRegretBound (fun g x ↦ ⟪g, x⟫)
      (fun _ _ ↦ True) K (fun n c g u ↦
        (‖u - x₀‖ ^ 2 - ‖u - (onlineSubgradientDescent K (fun _ ↦ η) x₀).run c g n‖ ^ 2) /
          (2 * η) + η / 2 * ∑ t ∈ range n, ‖g t‖ ^ 2) := by
  refine hasRegretBound_iff.mpr fun c g n _ u hu ↦ ?_
  have h := onlineSubgradientDescent_regret_le_norm_sub_sq_div (n := n) hK hη
    (fun t ↦ innerSL ℝ (g t)) g
    ((onlineSubgradientDescent K (fun _ ↦ η) x₀).run c g)
    (fun t _ ↦ hasSubgradientWithinAt_linear _)
    (fun t _ ↦ ⟨run_onlineSubgradientDescent_mem hx₀ c g (t + 1),
      isMinOn_run_onlineSubgradientDescent_of_complete_convex ⟨x₀, hx₀⟩ hKc hK c g t⟩) hu
  rw [run_onlineSubgradientDescent_zero] at h
  simpa only [regret_def, innerSL_apply_apply] using h

/-- **Anytime regret guarantee of the projected online subgradient descent learner**
[Ora, Theorem 2.13]. Let `K` be a complete convex set with `‖x - y‖ ≤ D` for `x, y ∈ K`, let
`x₀ ∈ K`, and let the learning rates `η t > 0` be nonincreasing. For every sequence of vectors `g`
and every horizon `n`, the regret of the linear losses `⟪g t, ·⟫` of the plays of the learner
against every `u ∈ K` is at most `D ^ 2 / (2 η (n - 1)) + ∑ t < n, η t / 2 * ‖g t‖ ^ 2`. -/
theorem hasRegretBound_onlineSubgradientDescent_of_antitone (hKc : IsComplete K)
    (hK : Convex ℝ K) (hx₀ : x₀ ∈ K) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) {D : ℝ}
    (hKD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) :
    (onlineSubgradientDescent (C := C) K η x₀).HasRegretBound (fun g x ↦ ⟪g, x⟫)
      (fun _ _ ↦ True) K
      (fun n _ g _ ↦ D ^ 2 / (2 * η (n - 1)) + ∑ t ∈ range n, η t / 2 * ‖g t‖ ^ 2) := by
  refine hasRegretBound_iff.mpr fun c g n _ u hu ↦ ?_
  have h := onlineSubgradientDescent_regret_le (n := n) hK hη hη_anti hKD
    (fun t ↦ innerSL ℝ (g t)) g
    ((onlineSubgradientDescent K η x₀).run c g) (fun t _ ↦ hasSubgradientWithinAt_linear _)
    (run_onlineSubgradientDescent_mem hx₀ c g 0)
    (fun t _ ↦ ⟨run_onlineSubgradientDescent_mem hx₀ c g (t + 1),
      isMinOn_run_onlineSubgradientDescent_of_complete_convex ⟨x₀, hx₀⟩ hKc hK c g t⟩) hu
  simpa only [regret_def, innerSL_apply_apply] using h

end OnlineLearner

end InnerProductSpace

end LMLExplore.OnlineLearning
