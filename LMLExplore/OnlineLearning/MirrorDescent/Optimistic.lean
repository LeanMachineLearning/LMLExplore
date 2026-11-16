/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.MirrorDescent.Basic

/-!
# Optimistic mirror descent

Online linear optimization on a set `K` of a real normed space `E`, with losses
`y t : E →L[ℝ] ℝ`, as in `LMLExplore.OnlineLearning.MirrorDescent.Basic`. **Optimistic mirror
descent** [Ora, §6.11, Algorithm 6.6] receives, before the loss `y t` of round `t` is revealed, a
hint `h t : E →L[ℝ] ℝ` guessing it, with `h 0 = 0`. After the loss `y t` and the next hint
`h (t + 1)`, it plays the mirror descent step from `a t` for the loss `y t - h t + h (t + 1)`: it
removes the hint used for the current play and adds the hint for the next one. How the hints are
produced does not matter: they may be any sequence chosen from the past, and the statements hold
for every sequence of losses.

The algorithm is mirror descent with other losses, so its analysis is that of mirror descent: the
regret against the true losses differs from the regret against the losses
`y t - h t + h (t + 1)` by a telescoping sum (`sum_apply_sub_eq_optimistic`). The resulting bounds
replace the loss `y t` in the stability term of round `t` by its prediction error `y t - h t`: the
regret is small when the hints are good. When the losses and the hints are all bounded in dual
norm by `L`, so that `‖y t - h t‖ ≤ 2 L`, each stability term of the strongly convex bound is at
most `4` times the worst-case term `η t / (2 m) * L ^ 2` of mirror descent.

The hint `h n` of the last round only affects the analysis point `a n`. The bounds keep it in a
boundary term `h n (u - a n)`, which vanishes for the book's choice `h n = 0`.

## Main statements

* `sum_apply_sub_eq_optimistic`: for any losses, hints and plays, the regret against the losses
  `y t` is the regret against `y t - h t + h (t + 1)`, plus `∑ t < n, h (t + 1) (a (t + 1) - a t)`
  and the boundary terms `h 0 (a 0 - u) - h n (a n - u)`.
* `optimisticMirrorDescent_regret_le_of_antitone`: [Ora, Theorem 6.38, first bound] with
  nonincreasing learning rates and divergences `D_F(u, a t) ≤ D` for `t < n`, the regret is at most
  `D / η (n - 1) + h n (u - a n)
    + ∑ t < n, ((y t - h t) (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
* `optimisticMirrorDescent_regret_le_bregDiv_div`: [Ora, Theorem 6.38, second bound] its form
  with `D_F(u, a 0) / η` for a constant learning rate `η`.
* `IsMirrorDescentStep.apply_sub_sub_bregDiv_div_le_mul_min`: [Ora, Theorem 6.38, last bound]
  for an `m`-strongly convex potential, the stability term of a mirror descent step for the loss
  `z`, measured with any `g`, is at most `η / (2 m) * ‖g‖ * min ‖g‖ (2 ‖z‖)`.
* `optimisticMirrorDescent_regret_le_of_strongConvexOn_of_antitone`,
  `optimisticMirrorDescent_regret_le_of_strongConvexOn`: the resulting bounds
  `D / η (n - 1) + h n (u - a n) + ∑ t < n, η t / (2 m) * ‖y t - h t‖ * min ‖y t - h t‖
    (2 ‖y t - h t + h (t + 1)‖)` and its constant-rate form.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ} {η : ℝ}
  {n : ℕ} {u : E}

/-- **The regret of optimistic mirror descent through the regret on the modified losses**
[Ora, proof of Theorem 6.38]. For any losses `y t`, hints `h t`, points `a t` and comparator `u`,
`∑ t < n, y t (a t - u) = ∑ t < n, (y t - h t + h (t + 1)) (a t - u)
  + ∑ t < n, h (t + 1) (a (t + 1) - a t) + h 0 (a 0 - u) - h n (a n - u)`.
No property of the points is used: this is the identity that reduces the analysis of optimistic
mirror descent to that of mirror descent on the losses `y t - h t + h (t + 1)`. -/
theorem sum_apply_sub_eq_optimistic (y h : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (u : E) (n : ℕ) :
    ∑ t ∈ range n, y t (a t - u) =
      ∑ t ∈ range n, (y t - h t + h (t + 1)) (a t - u) +
        ∑ t ∈ range n, h (t + 1) (a (t + 1) - a t) + h 0 (a 0 - u) - h n (a n - u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ]
    simp only [add_apply, sub_apply, map_sub]
    ring

/-- The stability terms of mirror descent on the losses `y t - h t + h (t + 1)`, plus the terms
`h (t + 1) (a (t + 1) - a t)` of `sum_apply_sub_eq_optimistic`, are the stability terms measured
with the prediction errors `y t - h t`. -/
private lemma sum_apply_sub_sub_add_sum_eq (y h : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (d : ℕ → ℝ)
    (n : ℕ) :
    ∑ t ∈ range n, ((y t - h t + h (t + 1)) (a t - a (t + 1)) - d t) +
        ∑ t ∈ range n, h (t + 1) (a (t + 1) - a t) =
      ∑ t ∈ range n, ((y t - h t) (a t - a (t + 1)) - d t) := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun t _ ↦ ?_
  simp only [add_apply, sub_apply, map_sub]
  ring

/-- **Regret of optimistic mirror descent with a constant learning rate** [Ora, Theorem 6.38,
second bound]. Let `F` be convex on `K` and `η > 0`. Let the hints satisfy `h 0 = 0`, let
`a 0 ∈ K`, and let each `a (t + 1)`, for `t < n`, be a mirror descent step on `K` from `a t` with
derivative `F' t`, for the loss `y t - h t + h (t + 1)`, where `F` has derivative `F' t` within
`K` at `a t` for `t ≤ n`. Then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ D_F(u, a 0) / η + h n (u - a n)
  + ∑ t < n, ((y t - h t) (a t - a (t + 1)) - D_F(a (t + 1), a t) / η)`.
The boundary term vanishes when the last hint `h n` is `0`, as in [Ora]. -/
theorem optimisticMirrorDescent_regret_le_bregDiv_div (hF : ConvexOn ℝ K F) (hη : 0 < η)
    (y h : ℕ → E →L[ℝ] ℝ) (hh0 : h 0 = 0) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F η (y t - h t + h (t + 1)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ bregDiv F u (a 0) (F' 0) / η + h n (u - a n) +
      ∑ t ∈ range n, ((y t - h t) (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η) := by
  have h_md := mirrorDescent_regret_le_bregDiv_div (y := fun t ↦ y t - h t + h (t + 1)) hF hη
    a F' ha0K ha hF' hu
  rw [sum_div, add_sub_assoc, ← sum_sub_distrib] at h_md
  rw [sum_apply_sub_eq_optimistic y h, hh0, zero_apply, ← sum_apply_sub_sub_add_sum_eq y h a]
  have h_bd : h n (u - a n) = -h n (a n - u) := by rw [← map_neg, neg_sub]
  linarith

/-- **Regret of optimistic mirror descent with nonincreasing learning rates** [Ora, Theorem 6.38,
first bound]. Let `F` be convex on `K` and let the learning rates `η t > 0` be nonincreasing. Let
the hints satisfy `h 0 = 0`, let `a 0 ∈ K`, and let each `a (t + 1)`, for `t < n`, be a mirror
descent step on `K` from `a t` with derivative `F' t` and learning rate `η t`, for the loss
`y t - h t + h (t + 1)`, where `F` has derivative `F' t` within `K` at `a t` for `t ≤ n`. If
`D ≥ 0` bounds the Bregman divergences `D_F(u, a t)` for `t < n`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ D / η (n - 1) + h n (u - a n)
  + ∑ t < n, ((y t - h t) (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
The boundary term vanishes when the last hint `h n` is `0`, as in [Ora]. -/
theorem optimisticMirrorDescent_regret_le_of_antitone {η : ℕ → ℝ} (hF : ConvexOn ℝ K F)
    (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (y h : ℕ → E →L[ℝ] ℝ) (hh0 : h 0 = 0)
    (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n,
      IsMirrorDescentStep K F (η t) (y t - h t + h (t + 1)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) {D : ℝ} (hD : 0 ≤ D)
    (hDu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ D) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ D / η (n - 1) + h n (u - a n) +
      ∑ t ∈ range n,
        ((y t - h t) (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) := by
  have h_md := mirrorDescent_regret_le_of_antitone (y := fun t ↦ y t - h t + h (t + 1)) hF hη
    hη_anti a F' ha0K ha hF' hD hDu hu
  rw [sum_apply_sub_eq_optimistic y h, hh0, zero_apply, ← sum_apply_sub_sub_add_sum_eq y h a]
  have h_bd : h n (u - a n) = -h n (a n - u) := by rw [← map_neg, neg_sub]
  linarith

/-- **Stability of a mirror descent step for a strongly convex potential, against any linear
map** [Ora, Theorem 6.38, last bound]. Let `F` be `m`-strongly convex on `K`, with `m > 0`, let
`F'` be a subgradient of `F` within `K` at `a ∈ K` (a derivative of `F` within `K` at `a`, for
convex `F`), let `η > 0`, and let `x` be a mirror descent step on `K` from `a` with `F'`, for the
loss `z`. Then for every continuous linear map `g`,
`g (a - x) - D_F(x, a) / η ≤ η / (2 m) * (‖g‖ * min ‖g‖ (2 ‖z‖))`.
With `z = g` it is the stability bound `η / (2 m) * ‖g‖ ^ 2` of mirror descent; for optimistic
mirror descent, `g = y - h` is the prediction error and `z = y - h + h'` the loss of the step, so
the bound is small when the prediction error or the step is. -/
theorem IsMirrorDescentStep.apply_sub_sub_bregDiv_div_le_mul_min {m : ℝ} {z F' : E →L[ℝ] ℝ}
    {a x : E} (h : IsMirrorDescentStep K F η z a F' x) (hF : StrongConvexOn K m F) (hm : 0 < m)
    (hη : 0 < η) (ha : a ∈ K) (hF'a : HasSubgradientWithinAt F F' K a) (g : E →L[ℝ] ℝ) :
    g (a - x) - bregDiv F x a F' / η ≤ η / (2 * m) * (‖g‖ * min ‖g‖ (2 * ‖z‖)) := by
  -- the divergence dominates the quadratic term with modulus `m / η`, and the step is at most
  -- `η / m * ‖z‖` long
  have h_div : m / η / 2 * ‖a - x‖ ^ 2 ≤ bregDiv F x a F' / η := by
    have h_breg := hF.add_add_le_of_hasSubgradientWithinAt ha h.mem hF'a
    rw [norm_sub_rev, le_div_iff₀ hη, bregDiv]
    have h_eq : m / η / 2 * ‖x - a‖ ^ 2 * η = m / 2 * ‖x - a‖ ^ 2 := by field_simp
    linarith
  have h_lam : m / η * ‖a - x‖ ≤ ‖z‖ := by
    have h_step := h.mul_norm_sub_le hF hη.le ha hF'a
    rw [norm_sub_rev, div_mul_eq_mul_div, div_le_iff₀ hη]
    linarith
  have h_key := apply_sub_sub_mul_norm_sq_le_mul_min (div_pos hm hη) g h_lam
  have h_eq : ‖g‖ * min ‖g‖ (2 * ‖z‖) / (2 * (m / η)) =
      η / (2 * m) * (‖g‖ * min ‖g‖ (2 * ‖z‖)) := by
    field_simp
  linarith

/-- **Regret of optimistic mirror descent with nonincreasing learning rates and a strongly convex
potential** [Ora, Theorem 6.38]. Under the assumptions of
`optimisticMirrorDescent_regret_le_of_antitone`, if the potential `F` is `m`-strongly convex on
`K` for the norm of `E`, with `m > 0`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ D / η (n - 1) + h n (u - a n)
  + ∑ t < n, η t / (2 m) * (‖y t - h t‖ * min ‖y t - h t‖ (2 ‖y t - h t + h (t + 1)‖))`,
where the norms are dual norms. Each summand is at most `η t / (2 m) * ‖y t - h t‖ ^ 2`: the
regret is governed by the prediction errors of the hints. -/
theorem optimisticMirrorDescent_regret_le_of_strongConvexOn_of_antitone {η : ℕ → ℝ} {m : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    (y h : ℕ → E →L[ℝ] ℝ) (hh0 : h 0 = 0) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n,
      IsMirrorDescentStep K F (η t) (y t - h t + h (t + 1)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) {D : ℝ} (hD : 0 ≤ D)
    (hDu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ D) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ D / η (n - 1) + h n (u - a n) +
      ∑ t ∈ range n,
        η t / (2 * m) * (‖y t - h t‖ * min ‖y t - h t‖ (2 * ‖y t - h t + h (t + 1)‖)) := by
  have hF_cvx := strongConvexOn_zero.mp (hF.mono hm.le)
  refine (optimisticMirrorDescent_regret_le_of_antitone hF_cvx hη hη_anti y h hh0 a F' ha0K ha
    hF' hD hDu hu).trans (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  have ht := mem_range.mp ht
  have h_mem := mem_of_isMirrorDescentStep ha0K ha
  exact (ha t ht).apply_sub_sub_bregDiv_div_le_mul_min hF hm (hη t) (h_mem t ht.le)
    ((hF' t ht.le).hasSubgradientWithinAt hF_cvx (h_mem t ht.le)) (y t - h t)

/-- **Regret of optimistic mirror descent with a constant learning rate and a strongly convex
potential** [Ora, Theorem 6.38]. Under the assumptions of
`optimisticMirrorDescent_regret_le_bregDiv_div`, if the potential `F` is `m`-strongly convex on
`K` for the norm of `E`, with `m > 0`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ D_F(u, a 0) / η + h n (u - a n)
  + η / (2 m) * ∑ t < n, ‖y t - h t‖ * min ‖y t - h t‖ (2 ‖y t - h t + h (t + 1)‖)`,
where the norms are dual norms. -/
theorem optimisticMirrorDescent_regret_le_of_strongConvexOn {m : ℝ} (hF : StrongConvexOn K m F)
    (hm : 0 < m) (hη : 0 < η) (y h : ℕ → E →L[ℝ] ℝ) (hh0 : h 0 = 0) (a : ℕ → E)
    (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F η (y t - h t + h (t + 1)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ bregDiv F u (a 0) (F' 0) / η + h n (u - a n) +
      η / (2 * m) *
        ∑ t ∈ range n, ‖y t - h t‖ * min ‖y t - h t‖ (2 * ‖y t - h t + h (t + 1)‖) := by
  have hF_cvx := strongConvexOn_zero.mp (hF.mono hm.le)
  refine (optimisticMirrorDescent_regret_le_bregDiv_div hF_cvx hη y h hh0 a F' ha0K ha hF'
    hu).trans (add_le_add le_rfl ?_)
  rw [mul_sum]
  refine sum_le_sum fun t ht ↦ ?_
  have ht := mem_range.mp ht
  have h_mem := mem_of_isMirrorDescentStep ha0K ha
  exact (ha t ht).apply_sub_sub_bregDiv_div_le_mul_min hF hm hη (h_mem t ht.le)
    ((hF' t ht.le).hasSubgradientWithinAt hF_cvx (h_mem t ht.le)) (y t - h t)

end LMLExplore.OnlineLearning
