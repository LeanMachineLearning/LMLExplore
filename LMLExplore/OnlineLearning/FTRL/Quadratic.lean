/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Bregman.Euclidean
public import LMLExplore.NumberTheory.Harmonic.Bounds
public import LMLExplore.OnlineLearning.FTRL.Stability

/-!
# FTRL-Proximal and follow-the-leader on quadratized losses

On a real inner product space `E`, two algorithms of follow the regularized leader (FTRL) add to
their objectives quadratic terms `c / 2 * ‖a - x s‖ ^ 2` centered at their own past plays `x s`.

* **FTRL-Proximal** [Ora, Example 7.9] plays at round `t` a minimizer over a set `V` of
  `∑ s < t, (σ s / 2 * ‖a - x s‖ ^ 2 + ℓ s a)`, with weights `σ s ≥ 0` that may be chosen after
  the loss of round `s`. Its regularizer `ψ t = ∑ s < t, σ s / 2 * ‖· - x s‖ ^ 2` is proximal: the
  play `x t` minimizes the increment `ψ (t + 1) - ψ t = σ t / 2 * ‖· - x t‖ ^ 2`. For convex
  losses with subgradients `g t` at the plays, its regret against every `u ∈ V` is at most
  `∑ t < n, σ t / 2 * ‖u - x t‖ ^ 2 + ∑ t < n, ‖g t‖ ^ 2 / (2 ∑ s ≤ t, σ s)`.
* **Follow-the-leader on the quadratized losses**
  `q t a = g t a + μ t / 2 * ‖a - x t‖ ^ 2` [Ora, Algorithm 7.5, (7.9)] has, for losses
  that lie above these quadratics at the plays (strong convexity at the plays), the bound
  `∑ t < n, ‖g t‖ ^ 2 / (2 ∑ s ≤ t, μ s)` of follow-the-leader on strongly convex losses, while
  each of its plays is a projection onto `V` of an explicit point: for `g s = ⟪v s, ·⟫`, the
  minimizers over `V` of `∑ s < t, q s` are the points of `V` nearest to
  `(∑ s < t, μ s)⁻¹ • ∑ s < t, (μ s • x s - v s)`.

Follow-the-leader on the squared losses `(a - y t) ^ 2` of the guessing game on `[0, 1]`, which
are `2`-strongly convex, has regret at most `1 + log n` [Ora, Example 7.26], an improvement on the
bound `4 + 4 log n` of [Ora, Theorem 1.3].

## Main statements

* `regret_le_ftrl_proximal`: [Ora, Example 7.9] the regret of FTRL-Proximal for convex losses.
* `regret_le_ftl_quadratized`: [Ora, Corollary 7.25, Algorithm 7.5] the regret of
  follow-the-leader on the quadratized losses.
* `isMinOn_sum_inner_add_div_two_mul_norm_sub_sq_iff`: the minimizers of a sum of quadratics
  `⟪v i, ·⟫ + μ i / 2 * ‖· - x i‖ ^ 2` with positive total weight are the nearest points to an
  explicit center; in particular the plays of follow-the-leader on the quadratized losses
  [Ora, (7.9)].
* `regret_sq_sub_le_one_add_log`: [Ora, Example 7.26] the regret of follow-the-leader on the
  guessing game.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Theorem 1.3, Example 7.9, Corollary 7.25, Algorithm 7.5, (7.9),
  Example 7.26.
-/
public section

open Finset
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V : Set E}

/-- **The regret of FTRL-Proximal** [Ora, Example 7.9]. Let the losses `ℓ t` be convex on `V`, and
let the weights `σ t ≥ 0` have positive partial sums `0 < ∑ s ≤ t, σ s`, for `t < n`. Let
`x t ∈ V` minimize over `V` the objective `∑ s < t, (σ s / 2 * ‖a - x s‖ ^ 2 + ℓ s a)`, so that
`x 0` is any point of `V`, and let `g t` be a subgradient of `ℓ t` within `V` at `x t`, for
`t < n`. Then for every `u ∈ V`,
`regret ℓ x u n ≤ ∑ t < n, σ t / 2 * ‖u - x t‖ ^ 2 + ∑ t < n, ‖g t‖ ^ 2 / (2 ∑ s ≤ t, σ s)`,
where `‖g t‖` is the dual norm. The weight `σ t` may depend on the losses up to round `t`.
FTRL-Proximal is follow-the-leader on the `σ t`-strongly convex losses
`σ t / 2 * ‖· - x t‖ ^ 2 + ℓ t`, and the bound follows from `regret_le_ftl_of_strongConvexOn`. -/
theorem regret_le_ftrl_proximal (ℓ : ℕ → E → ℝ) (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) {σ : ℕ → ℝ}
    {u : E} {n : ℕ} (hσ : ∀ t < n, 0 ≤ σ t) (hσ_sum : ∀ t < n, 0 < ∑ s ∈ range (t + 1), σ s)
    (hℓ : ∀ t < n, ConvexOn ℝ V (ℓ t)) (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n,
      IsMinOn (fun a ↦ ∑ s ∈ range t, σ s / 2 * ‖a - x s‖ ^ 2 + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : ∀ t < n, HasSubgradientWithinAt (ℓ t) (g t) V (x t)) (hu : u ∈ V) :
    regret ℓ x u n ≤ ∑ t ∈ range n, σ t / 2 * ‖u - x t‖ ^ 2 +
      ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * ∑ s ∈ range (t + 1), σ s) := by
  -- FTRL-Proximal is follow-the-leader on the `σ t`-strongly convex losses
  -- `ℓ' t = σ t / 2 * ‖· - x t‖ ^ 2 + ℓ t`
  set ℓ' : ℕ → E → ℝ := fun t a ↦ σ t / 2 * ‖a - x t‖ ^ 2 + ℓ t a with hℓ'_def
  have hℓ' (t : ℕ) (ht : t < n) : StrongConvexOn V (σ t) (ℓ' t) :=
    (strongConvexOn_div_two_mul_norm_sub_sq (hℓ t ht).1 (σ t) (x t)).add_convexOn (hℓ t ht)
  -- `g t` is a subgradient of `ℓ' t` at `x t`, where the quadratic is nonnegative and vanishes
  have hg' (t : ℕ) (ht : t < n) : HasSubgradientWithinAt (ℓ' t) (g t) V (x t) := by
    refine hasSubgradientWithinAt_iff_le.mpr fun a ha ↦ ?_
    have h := hasSubgradientWithinAt_iff_le.mp (hg t ht) a ha
    have := hσ t ht
    simp only [hℓ'_def, sub_self, norm_zero, zero_pow two_ne_zero, mul_zero, zero_add]
    nlinarith [sq_nonneg ‖a - x t‖]
  have h := regret_le_ftl_of_strongConvexOn ℓ' x g hℓ' hσ_sum hx
    (fun t ht ↦ by simpa only [hℓ'_def, sum_add_distrib] using hmin t ht) hg' hu
  -- the regret of `ℓ'` is that of `ℓ` minus the quadratic terms at the comparator
  have h_reg : regret ℓ' x u n = regret ℓ x u n - ∑ t ∈ range n, σ t / 2 * ‖u - x t‖ ^ 2 := by
    simp only [regret_def, hℓ'_def, sub_self, norm_zero, zero_pow two_ne_zero, mul_zero,
      zero_add, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ ↦ by ring
  linarith

/-- **Follow-the-leader on quadratized losses** [Ora, Corollary 7.25, Algorithm 7.5]. Let the
weights `μ t ≥ 0` have positive partial sums `0 < ∑ s ≤ t, μ s`, and let each loss `ℓ t` lie
above the quadratic `ℓ t (x t) + g t (· - x t) + μ t / 2 * ‖· - x t‖ ^ 2` on `V` (for instance
if `ℓ t` is `μ t`-strongly convex on `V` and `g t` is a subgradient within `V` at `x t`), for
`t < n`. Let `x t ∈ V` minimize over `V` the cumulative quadratized loss
`∑ s < t, (g s a + μ s / 2 * ‖a - x s‖ ^ 2)`, so that `x 0` is any point of `V`. Then for every
`u ∈ V`, `regret ℓ x u n ≤ ∑ t < n, ‖g t‖ ^ 2 / (2 ∑ s ≤ t, μ s)`, where `‖g t‖` is the dual
norm. This is the bound of follow-the-leader on the losses `ℓ t`
(`regret_le_ftl_of_strongConvexOn`), with plays that are projections of explicit points
(`isMinOn_sum_inner_add_div_two_mul_norm_sub_sq_iff`). -/
theorem regret_le_ftl_quadratized (hV : Convex ℝ V) (ℓ : ℕ → E → ℝ) (x : ℕ → E)
    (g : ℕ → E →L[ℝ] ℝ) {μ : ℕ → ℝ} {u : E} {n : ℕ} (hμ : ∀ t < n, 0 ≤ μ t)
    (hμ_sum : ∀ t < n, 0 < ∑ s ∈ range (t + 1), μ s)
    (hℓ : ∀ t < n, ∀ a ∈ V, ℓ t (x t) + g t (a - x t) + μ t / 2 * ‖a - x t‖ ^ 2 ≤ ℓ t a)
    (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ∑ s ∈ range t, (g s a + μ s / 2 * ‖a - x s‖ ^ 2)) V (x t))
    (hu : u ∈ V) :
    regret ℓ x u n ≤ ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * ∑ s ∈ range (t + 1), μ s) := by
  -- the quadratized losses
  set ℓ' : ℕ → E → ℝ := fun t a ↦ g t a + μ t / 2 * ‖a - x t‖ ^ 2 with hℓ'_def
  -- `g t` is a subgradient of the `μ t`-strongly convex `ℓ' t` at `x t`
  have hg (t : ℕ) (ht : t < n) : HasSubgradientWithinAt (ℓ' t) (g t) V (x t) := by
    refine hasSubgradientWithinAt_iff_le.mpr fun a _ ↦ ?_
    simp only [hℓ'_def, sub_self, norm_zero, map_sub]
    have := hμ t ht
    nlinarith [sq_nonneg ‖a - x t‖]
  have hℓ' (t : ℕ) (_ : t < n) : StrongConvexOn V (μ t) (ℓ' t) := by
    convert (strongConvexOn_div_two_mul_norm_sub_sq hV (μ t) (x t)).add_convexOn
      ((g t).toLinearMap.convexOn hV) using 1
    ext a
    simp [hℓ'_def, add_comm]
  have h := regret_le_ftl_of_strongConvexOn ℓ' x g hℓ' hμ_sum hx hmin hg hu
  -- the regret of the losses is at most that of the quadratized losses
  refine le_trans ?_ h
  simp only [regret_def]
  refine sum_le_sum fun t ht ↦ ?_
  have h_le := hℓ t (mem_range.mp ht) u hu
  simp only [hℓ'_def, sub_self, norm_zero, map_sub] at h_le ⊢
  nlinarith

/-- **The minimizers of a sum of quadratics** [Ora, (7.9)]. For weights `μ i` with positive
sum `M = ∑ i ∈ t, μ i`, centers `x i` and linear terms `⟪v i, ·⟫`, the minimizers over any set `V`
of `∑ i ∈ t, (⟪v i, a⟫ + μ i / 2 * ‖a - x i‖ ^ 2)` are its points nearest to
`M⁻¹ • ∑ i ∈ t, (μ i • x i - v i)`. The individual weights may be negative. With
`g s = ⟪v s, ·⟫`, the plays of follow-the-leader on the quadratized losses of
`regret_le_ftl_quadratized` are thus the projections onto `V` of
`(∑ s < t, μ s)⁻¹ • ∑ s < t, (μ s • x s - v s)`. -/
theorem isMinOn_sum_inner_add_div_two_mul_norm_sub_sq_iff {ι : Type*} (t : Finset ι)
    (v x : ι → E) {μ : ι → ℝ} (hμ : 0 < ∑ i ∈ t, μ i) (V : Set E) (a : E) :
    IsMinOn (fun b ↦ ∑ i ∈ t, (⟪v i, b⟫ + μ i / 2 * ‖b - x i‖ ^ 2)) V a ↔
      IsMinOn (fun b ↦ ‖b - (∑ i ∈ t, μ i)⁻¹ • ∑ i ∈ t, (μ i • x i - v i)‖) V a := by
  set M := ∑ i ∈ t, μ i with hM
  set c := M⁻¹ • ∑ i ∈ t, (μ i • x i - v i) with hc
  -- completing the square: the objective is `M / 2 * ‖b - c‖ ^ 2` plus a constant
  have h_sq (b : E) : ∑ i ∈ t, (⟪v i, b⟫ + μ i / 2 * ‖b - x i‖ ^ 2) =
      M / 2 * ‖b - c‖ ^ 2 + (∑ i ∈ t, μ i / 2 * ‖x i‖ ^ 2 - M / 2 * ‖c‖ ^ 2) := by
    have h_inner : M * ⟪b, c⟫ = ∑ i ∈ t, (μ i * ⟪b, x i⟫ - ⟪v i, b⟫) := by
      rw [hc, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul, inner_sum]
      exact sum_congr rfl fun i _ ↦ by
        rw [inner_sub_right, inner_smul_right, real_inner_comm (v i) b]
    have h_lin : ∑ i ∈ t, μ i / 2 * (2 * ⟪b, x i⟫) = ∑ i ∈ t, μ i * ⟪b, x i⟫ :=
      sum_congr rfl fun i _ ↦ by ring
    rw [sum_sub_distrib] at h_inner
    simp only [norm_sub_sq_real, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, ← sum_mul,
      ← sum_div, ← hM]
    linear_combination (-1 : ℝ) * h_lin + h_inner
  simp only [isMinOn_iff, h_sq, add_le_add_iff_right]
  refine forall₂_congr fun b _ ↦ ?_
  rw [mul_le_mul_iff_of_pos_left (half_pos hμ), sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]

/-- **Follow-the-leader on the guessing game** [Ora, Example 7.26]. Let the outcomes `y t` and the
plays `x t` lie in `[0, 1]`, and let `x t` minimize over `[0, 1]` the cumulative squared loss
`∑ s < t, (a - y s) ^ 2` of the previous rounds, so that `x 0` is any point of `[0, 1]`, for
`t < n`. Then the regret of the squared losses against every `u ∈ [0, 1]` is at most `1 + log n`.
This improves the bound `4 + 4 log n` of [Ora, Theorem 1.3]. -/
theorem regret_sq_sub_le_one_add_log (x y : ℕ → ℝ) {u : ℝ} {n : ℕ}
    (hy : ∀ t < n, y t ∈ Set.Icc 0 1) (hx : ∀ t < n, x t ∈ Set.Icc 0 1)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ∑ s ∈ range t, (a - y s) ^ 2) (Set.Icc 0 1) (x t))
    (hu : u ∈ Set.Icc 0 1) :
    regret (fun t a ↦ (a - y t) ^ 2) x u n ≤ 1 + Real.log n := by
  -- the squared losses are `2`-strongly convex, with derivative `2 (x t - y t)` at `x t`
  have h := regret_le_ftl_of_strongConvexOn (fun t a ↦ (a - y t) ^ 2) x _
    (fun t _ ↦ strongConvexOn_sq_sub (convex_Icc 0 1) (y t))
    (fun t _ ↦ by simp only [sum_const, card_range, nsmul_eq_mul]; positivity) hx hmin
    (fun t _ ↦ hasSubgradientWithinAt_sq_sub _ (x t) (y t)) hu
  refine h.trans ((sum_le_sum fun t ht ↦ ?_).trans (Real.sum_range_inv_add_one_le n))
  -- each stability term is `(x t - y t) ^ 2 / (t + 1) ≤ 1 / (t + 1)`
  have ht := mem_range.mp ht
  have h_sq : (x t - y t) ^ 2 ≤ 1 := by
    nlinarith [(hx t ht).1, (hx t ht).2, (hy t ht).1, (hy t ht).2]
  simp only [innerSL_apply_norm, Real.norm_eq_abs, sum_const, card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  rw [sq_abs, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end LMLExplore.OnlineLearning
