/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.OnlineLearning.MirrorDescent

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
to the gradient step `a t - η t • g t`. With a nonincreasing learning rate, its regret on a set of
diameter at most `D`, for subgradients of norm at most `G`, is at most
`D ^ 2 / (2 η (n - 1)) + ∑ t < n, η t / 2 * ‖g t‖ ^ 2`, and the anytime learning rate
`η t = D / (G √(t + 1))` gives the bound `3 / 2 * D * G * √n` for every horizon `n`.

## Main statements

* `sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt`: the regret of losses with subgradients
  at the plays is at most the regret of the linearized losses.
* `isMirrorDescentStep_norm_sq_div_two_iff`: the mirror descent steps for the potential
  `‖b‖ ^ 2 / 2` and the loss `⟪g, ·⟫` from `a` are the points of `K` nearest to `a - η • g`.
* `onlineSubgradientDescent_regret_le`: the regret of projected online subgradient descent with
  nonincreasing learning rates.
* `onlineSubgradientDescent_regret_le_sqrt`: with `η t = D / (G √(t + 1))`, the regret is at most
  `3 / 2 * D * G * √n`.

## References

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
  have ha' (t : ℕ) (ht : t < n) := isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  have h_mem := mem_of_isMirrorDescentStep ha0 ha'
  have hD : 0 ≤ D := (norm_nonneg _).trans (hKD u hu u hu)
  -- the Bregman divergences to `u` are at most `D ^ 2 / 2`
  have hDu (t : ℕ) (ht : t < n) :
      bregDiv (fun b : E ↦ ‖b‖ ^ 2 / 2) u (a t) (innerSL ℝ (a t)) ≤ D ^ 2 / 2 := by
    rw [bregDiv_norm_sq_div_two]
    gcongr
    exact hKD u hu (a t) (h_mem t ht.le)
  have h := mirrorDescent_regret_le_of_strongConvexOn_of_antitone
    (strongConvexOn_norm_sq_div_two hK) one_pos hη hη_anti (fun t ↦ innerSL ℝ (g t)) a
    (fun t ↦ innerSL ℝ (a t)) ha0 ha'
    (fun t _ ↦ (hasFDerivAt_norm_sq_div_two (a t)).hasFDerivWithinAt) (by positivity) hDu hu
  simp only [innerSL_apply_norm, mul_one] at h
  rw [div_div] at h
  exact (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f _ a hg hu).trans h

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

end InnerProductSpace

end LMLExplore.OnlineLearning
