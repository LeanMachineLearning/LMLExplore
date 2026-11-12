/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Bregman.Taylor
public import LMLExplore.OnlineLearning.MirrorDescent

/-!
# Local-norm regret bounds through the unconstrained step

The regret bounds of follow the regularized leader and of mirror descent with a potential `F`
(`LMLExplore.OnlineLearning.FTRL`, `LMLExplore.OnlineLearning.MirrorDescent`) are sums of
stability terms `y (a - b) - D_F(b, a) / η`, where `a` is the play of a round, `y` its loss, `η`
its learning rate and `b` the next play (or the comparator). Strong convexity bounds such a term
by `η / (2 m) * ‖y‖ ^ 2`, which is useless for losses with a large dual norm, such as the
importance-weighted estimates of bandit algorithms. The local-norm bounds measure `y` instead
through the second derivative `F''` of the potential at a point near `a`.

This file proves the local-norm bound through the **unconstrained step** [Ora, Lemma 6.32 and
Lemma 7.15, second forms]. Let `F` be convex on a set `D`, and at every point `z` of a convex set
`U ⊆ D` let `F` have derivative `F' z` within `D` and `F'` have derivative `F'' z` within `U`. Let
`x ∈ U` be the unconstrained step from `a ∈ U`: the point with `F' x = F' a - η y`. Then `x`
minimizes `b ↦ η y b + D_F(b, a)` over `D`, so the stability term at every `b ∈ D` is at most its
value at `x` (`apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt`, in
`LMLExplore.OnlineLearning.MirrorDescent`). Taylor's theorem along the segment `[a, x]` bounds
the latter by `η / 2 * c` for every `c ≥ 0` with `y (x - a) ^ 2 ≤ c * F'' z (x - a) (x - a)`, at
some `z ∈ [a, x]`. Any `c` bounding the squared dual local norm of `y` for the quadratic form
`F'' z` qualifies.

Unlike a bound along the segment from the play to the next play, the segment `[a, x]` is
determined by the play, the loss and the learning rate of the round alone, not by the feasible
set. The set `D` of convexity may be larger than `U`: for FTRL with the ½-Tsallis potential
`-∑ a, √(p a)` on the simplex (Tsallis-INF), `U` is the open positive orthant, where the plays
lie, and `D` is the nonnegative orthant, which contains the vertices of the simplex as
comparators. For nonnegative losses the unconstrained step of that potential decreases every
coordinate, so the second derivative on `[a, x]` dominates its value at `a`.

## Main statements

* `exists_mem_segment_apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt`: the local-norm bound of
  one round through the unconstrained step [Ora, Lemma 6.32 and Lemma 7.15, second forms].
* `ftrl_regret_le_of_localNorm_of_antitone`: for FTRL with nonincreasing learning rates `η t`, the
  regret is at most `(F u - F (a 0)) / η (n - 1) + ∑ t < n, η t / 2 * c t`, for local norms
  `c t` of the losses along the segments from the plays to the unconstrained steps
  [Ora, Lemma 7.15, second form].
* `mirrorDescent_regret_le_of_localNorm_of_antitone`: the same bound for mirror descent with
  nonincreasing learning rates and divergences `D_F(u, a t) ≤ B`, with `B` in place of
  `F u - F (a 0)` [Ora, Lemma 6.32, second form].

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K D U : Set E} {F : E → ℝ}
  {F' : E → E →L[ℝ] ℝ} {F'' : E → E →L[ℝ] E →L[ℝ] ℝ} {n : ℕ} {u : E}

/-- **Local-norm bound of one round through the unconstrained step** [Ora, Lemma 6.32 and
Lemma 7.15, second forms]. Let `F` be convex on `D`, and at every point `z` of a convex set
`U ⊆ D` let `F` have derivative `F' z` within `D` and `F'` have derivative `F'' z` within `U`.
Let `η > 0`, `a ∈ U`, and let `x ∈ U` be the unconstrained step from `a` for the loss `y`:
`F' x = F' a - η y`. There is a point `z` of the segment `[a, x]` such that for every `c ≥ 0` with
`y (x - a) ^ 2 ≤ c * F'' z (x - a) (x - a)` and every `b ∈ D`,
`y (a - b) - D_F(b, a) / η ≤ η / 2 * c`. -/
theorem exists_mem_segment_apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt
    (hF : ConvexOn ℝ D F) (hUc : Convex ℝ U) (hUD : U ⊆ D)
    (hF' : ∀ z ∈ U, HasFDerivWithinAt F (F' z) D z)
    (hF'' : ∀ z ∈ U, HasFDerivWithinAt F' (F'' z) U z) {η : ℝ} (hη : 0 < η) (y : E →L[ℝ] ℝ)
    {a x : E} (ha : a ∈ U) (hx : x ∈ U) (hxa : F' x = F' a - η • y) :
    ∃ z ∈ segment ℝ a x, ∀ c, 0 ≤ c → y (x - a) ^ 2 ≤ c * F'' z (x - a) (x - a) →
      ∀ b ∈ D, y (a - b) - bregDiv F b a (F' a) / η ≤ η / 2 * c := by
  have h_seg : segment ℝ a x ⊆ U := hUc.segment_subset ha hx
  -- Taylor's theorem along `[a, x]` bounds the stability term at the unconstrained step `x`
  have h_conv : ConvexOn ℝ (segment ℝ a x) F := hF.subset (h_seg.trans hUD) (convex_segment a x)
  obtain ⟨z, hz, h_taylor⟩ := h_conv.exists_mem_segment_apply_sub_sub_bregDiv_div_le
      (fun w hw ↦ (hF' w (h_seg hw)).mono (h_seg.trans hUD))
      (fun w hw ↦ (hF'' w (h_seg hw)).mono h_seg)
      (right_mem_segment ℝ a x) (left_mem_segment ℝ a x)
  refine ⟨z, segment_symm ℝ x a ▸ hz, fun c hc hcy b hb ↦ ?_⟩
  have h_neg : y (a - x) = (-y) (x - a) := by
    rw [neg_apply, ← map_neg, neg_sub]
  have h_x := h_taylor η hη (-y) c hc (by rwa [neg_apply, neg_sq])
  rw [← h_neg] at h_x
  -- the stability term at `b` is at most the one at the unconstrained step
  refine (apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt hF hη y (F' a) a hb (hUD hx) ?_).trans
    h_x
  rw [← hxa]
  exact hF' x hx

/-- **Regret of FTRL with local norms through the unconstrained steps** [Ora, Lemma 7.15, second
form]. Let `K` be convex and let the potential `F` be convex on a set `D ⊇ K`, and at every point
`z` of a convex set `U ⊆ D` let `F` have derivative `F' z` within `D` and `F'` have derivative
`F'' z` within `U`. Let the learning rates `η t > 0` be nonincreasing, and let each `a t`, for
`t < n` and for `t = 0`, be a play of FTRL on `K` with potential `F` and learning rate `η t`
(`IsFTRLPlay`), with `a t ∈ U` for `t < n`. Let `x t ∈ U` be the unconstrained step from `a t`,
with `F' (x t) = F' (a t) - η t y t`, and let `c t ≥ 0` bound the squared local norm of the loss
along `[a t, x t]`: `y t (x t - a t) ^ 2 ≤ c t * F'' z (x t - a t) (x t - a t)` for every
`z ∈ [a t, x t]`. Then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η (n - 1) + ∑ t < n, η t / 2 * c t`.
The bound holds for every horizon `n`, without tuning the learning rates to it. -/
theorem ftrl_regret_le_of_localNorm_of_antitone (hF : ConvexOn ℝ D F) (hK : Convex ℝ K)
    (hKD : K ⊆ D) (hUc : Convex ℝ U) (hUD : U ⊆ D)
    (hF' : ∀ z ∈ U, HasFDerivWithinAt F (F' z) D z)
    (hF'' : ∀ z ∈ U, HasFDerivWithinAt F' (F'' z) U z)
    {η : ℕ → ℝ} (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (y : ℕ → E →L[ℝ] ℝ) (a x : ℕ → E)
    (ha0 : IsFTRLPlay K F (η 0) y 0 (a 0)) (ha : ∀ t < n, IsFTRLPlay K F (η t) y t (a t))
    (haU : ∀ t < n, a t ∈ U) (hxU : ∀ t < n, x t ∈ U)
    (hxa : ∀ t < n, F' (x t) = F' (a t) - η t • y t) (c : ℕ → ℝ) (hc : ∀ t < n, 0 ≤ c t)
    (hcy : ∀ t < n, ∀ z ∈ segment ℝ (a t) (x t),
      y t (x t - a t) ^ 2 ≤ c t * F'' z (x t - a t) (x t - a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (F u - F (a 0)) / η (n - 1) + ∑ t ∈ range n, η t / 2 * c t := by
  rcases n with _ | n
  · simpa using div_nonneg (sub_nonneg.mpr (isMinOn_iff.mp ha0.isMinOn_zero u hu)) (hη 0).le
  -- each stability term, against any point of `D`, is bounded through the unconstrained step
  have h_stab (t : ℕ) (ht : t < n + 1) (b : E) (hb : b ∈ D) :
      y t (a t - b) - bregDiv F b (a t) (F' (a t)) / η t ≤ η t / 2 * c t := by
    obtain ⟨z, hz, h⟩ := exists_mem_segment_apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt
      hF hUc hUD hF' hF'' (hη t) (y t) (haU t ht) (hxU t ht) (hxa t ht)
    exact h (c t) (hc t ht) (hcy t ht z hz) b hb
  have ha' (t : ℕ) (ht : t ≤ n) : IsFTRLPlay K F (η t) y t (a t) := ha t (Nat.lt_succ_of_le ht)
  refine (ftrl_regret_succ_le_of_antitone hK hη hη_anti y a ha' (fun t ↦ F' (a t))
    (fun t ht ↦ (hF' _ (haU t (Nat.lt_succ_of_le ht))).mono hKD) hu).trans ?_
  rw [Nat.add_sub_cancel, sum_range_succ, ← add_assoc]
  refine add_le_add (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
    (h_stab n n.lt_succ_self u (hKD hu))
  have ht := mem_range.mp ht
  exact h_stab t (ht.trans n.lt_succ_self) _ (hKD (ha' (t + 1) ht).mem)

/-- **Regret of mirror descent with local norms through the unconstrained steps**
[Ora, Lemma 6.32, second form]. Let `K` be convex and let the potential `F` be convex on a set
`D ⊇ K`, and at every point `z` of a convex set `U ⊆ D` let `F` have derivative `F' z` within `D`
and `F'` have derivative `F'' z` within `U`. Let the learning rates `η t > 0` be nonincreasing,
let `a 0 ∈ K`, and let each `a (t + 1)`, for `t < n`, be a mirror descent step on `K` from `a t`
with derivative `F' (a t)` and learning rate `η t`, for the loss `y t`, with `a t ∈ U` for
`t ≤ n`. Let `x t ∈ U` be the unconstrained step from `a t`, with
`F' (x t) = F' (a t) - η t y t`, and let `c t ≥ 0` bound the squared local norm of the loss along
`[a t, x t]`: `y t (x t - a t) ^ 2 ≤ c t * F'' z (x t - a t) (x t - a t)` for every
`z ∈ [a t, x t]`. If
`B ≥ 0` bounds the Bregman divergences `D_F(u, a t)` for `t < n`, then
`∑ t < n, y t (a t - u) ≤ B / η (n - 1) + ∑ t < n, η t / 2 * c t`. -/
theorem mirrorDescent_regret_le_of_localNorm_of_antitone (hF : ConvexOn ℝ D F) (hK : Convex ℝ K)
    (hKD : K ⊆ D) (hUc : Convex ℝ U) (hUD : U ⊆ D)
    (hF' : ∀ z ∈ U, HasFDerivWithinAt F (F' z) D z)
    (hF'' : ∀ z ∈ U, HasFDerivWithinAt F' (F'' z) U z)
    {η : ℕ → ℝ} (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (y : ℕ → E →L[ℝ] ℝ) (a x : ℕ → E)
    (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F (η t) (y t) (a t) (F' (a t)) (a (t + 1)))
    (haU : ∀ t ≤ n, a t ∈ U) (hxU : ∀ t < n, x t ∈ U)
    (hxa : ∀ t < n, F' (x t) = F' (a t) - η t • y t) (c : ℕ → ℝ) (hc : ∀ t < n, 0 ≤ c t)
    (hcy : ∀ t < n, ∀ z ∈ segment ℝ (a t) (x t),
      y t (x t - a t) ^ 2 ≤ c t * F'' z (x t - a t) (x t - a t))
    {B : ℝ} (hB : 0 ≤ B) (hBu : ∀ t < n, bregDiv F u (a t) (F' (a t)) ≤ B) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ B / η (n - 1) + ∑ t ∈ range n, η t / 2 * c t := by
  refine (mirrorDescent_regret_le_of_antitone (hF.subset hKD hK) hη hη_anti y a
    (fun t ↦ F' (a t)) ha0K ha (fun t ht ↦ (hF' _ (haU t ht)).mono hKD) hB hBu
    hu).trans (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  have ht := mem_range.mp ht
  -- the stability term of round `t` is bounded through the unconstrained step from `a t`
  obtain ⟨z, hz, h⟩ := exists_mem_segment_apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt hF
    hUc hUD hF' hF'' (hη t) (y t) (haU t ht.le) (hxU t ht) (hxa t ht)
  exact h (c t) (hc t ht) (hcy t ht z hz) _ (hKD (mem_of_isMirrorDescentStep ha0K ha (t + 1) ht))

end LMLExplore.OnlineLearning
