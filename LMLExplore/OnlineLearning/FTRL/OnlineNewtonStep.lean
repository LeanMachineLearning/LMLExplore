/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.ExpConcave
public import LMLExplore.Analysis.Convex.Subgradient
public import LMLExplore.Analysis.InnerProductSpace.EllipticalPotential
public import LMLExplore.OnlineLearning.FTRL.Stability

/-!
# The Online Newton Step

On a real inner product space `E`, the **Online Newton Step** (ONS) [Ora, Algorithm 7.6] is
follow the regularized leader on a set `V` with the quadratic regularizer `⟪V₀ x, x⟫ / 2`, for a
positive definite operator `V₀`, and the quadratic surrogate losses
`q t x = ⟪g t, x⟫ + μ / 2 * ⟪g t, x - x t⟫ ^ 2`, where `g t` is a (sub)gradient of the loss
`ℓ t` at the play `x t` and `μ ≥ 0`. Its play at round `t` minimizes over `V` the objective
`F t x = ⟪V₀ x, x⟫ / 2 + ∑ s < t, (⟪g s, x⟫ + μ / 2 * ⟪g s, x - x s⟫ ^ 2)`. It is quadratic,
with Hessian the design operator `designOp V₀ (√μ • g) t = V₀ + μ ∑ s < t, g s ⊗ g s`, so the
cumulative objective `F t + q t` lies above its subgradient planes at `x t` by the squared norm
`⟪S_t (z - x t), z - x t⟫ / 2` of `S_t = designOp V₀ (√μ • g) (t + 1)` (the design operator
including the current gradient). The stability of FTRL with a quadratic divergence then bounds
the regret on the surrogate losses, and the losses that lie above their surrogates at the plays,

  `ℓ t u ≥ ℓ t (x t) + ⟪g t, u - x t⟫ + μ / 2 * ⟪g t, u - x t⟫ ^ 2` [Ora, (7.12)],

have regret at most `⟪V₀ u, u⟫ / 2 - ⟪V₀ (x 0), x 0⟫ / 2 + ∑ t < n, ‖g t‖²_{S_t⁻¹} / 2`
[Ora, (7.11)]. The first play `x 0` minimizes `⟪V₀ x, x⟫ / 2` over `V`. The log-determinant lemma
bounds the last sum by `log (det S_{n-1} / det V₀) / (2 μ)`, which is logarithmic in `n`: for
`V₀ = λ • 1` and `‖g t‖ ≤ L` the regret is at most
`λ / 2 * ‖u‖ ^ 2 - λ / 2 * ‖x 0‖ ^ 2 + d / (2 μ) * log (1 + μ n L ^ 2 / (λ d))`. Exp-concave losses
satisfy the quadratic lower bound with `μ = min α B⁻¹ / 2` [Ora, Example 7.39], hence have
logarithmic regret under the ONS.

Completing the square, the ONS play is the projection onto `V`, in the norm of
`designOp V₀ (√μ • g) t`, of the unconstrained minimizer
`c t = (designOp V₀ (√μ • g) t)⁻¹ (∑ s < t, (μ ⟪g s, x s⟫ • g s - g s))` [Ora, Problem 7.12].

Nothing in the regret bound needs finite dimension except the determinants. The losses need not
be convex or differentiable: only the quadratic lower bound at the comparator is used.

## Main statements

* `regret_le_onlineNewtonStep`: [Ora, (7.11)] the regret of the ONS through the weighted norms
  `‖g t‖²_{S_t⁻¹}`.
* `regret_le_onlineNewtonStep_log_det`: [Ora, Lemma 7.29] its log-determinant form.
* `regret_le_onlineNewtonStep_log_one_add`: the logarithmic regret for `V₀ = λ • 1` and bounded
  gradients.
* `regret_le_onlineNewtonStep_of_expConcaveOn`: the logarithmic regret of the ONS on exp-concave
  losses.
* `isMinOn_onlineNewtonStep_iff`: [Ora, Problem 7.12] the two-step form of the ONS, an
  unconstrained step followed by a projection in the norm of the design operator.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Section 7.10, Algorithm 7.6, (7.11), (7.12), Lemma 7.29,
  Example 7.39, Problem 7.12.
-/
public section

open Finset Real
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V : Set E} {V₀ : E →L[ℝ] E}
  {μ : ℝ}

/-- The inner products of the design operator of the vectors `√μ • g s`:
`⟪S v, w⟫ = ⟪V₀ v, w⟫ + ∑ s < t, μ ⟪g s, v⟫ ⟪g s, w⟫`. -/
private lemma inner_designOp_sqrt_smul_apply (hμ : 0 ≤ μ) (g : ℕ → E) (t : ℕ) (v w : E) :
    ⟪designOp V₀ (fun s ↦ √μ • g s) t v, w⟫ =
      ⟪V₀ v, w⟫ + ∑ s ∈ range t, μ * ⟪g s, v⟫ * ⟪g s, w⟫ := by
  rw [inner_designOp_apply]
  congr 1
  refine sum_congr rfl fun s _ ↦ ?_
  simp only [real_inner_smul_left]
  linear_combination (⟪g s, v⟫ * ⟪g s, w⟫) * mul_self_sqrt hμ

/-- **The ONS objective is quadratic.** For a symmetric `V₀` and `μ ≥ 0`, the objective
`F t y = ⟪V₀ y, y⟫ / 2 + ∑ s < t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2)` satisfies
`F t z = F t y + ⟪S y - b, z - y⟫ + ⟪S (z - y), z - y⟫ / 2` for the design operator
`S = designOp V₀ (√μ • g) t` and `b = ∑ s < t, (μ ⟪g s, x s⟫ • g s - g s)`. -/
private lemma onlineNewtonStep_objective_eq (hV₀ : (V₀ : E →ₗ[ℝ] E).IsSymmetric) (hμ : 0 ≤ μ)
    (g x : ℕ → E) (t : ℕ) (y z : E) :
    ⟪V₀ z, z⟫ / 2 + ∑ s ∈ range t, (⟪g s, z⟫ + μ / 2 * ⟪g s, z - x s⟫ ^ 2) =
      ⟪V₀ y, y⟫ / 2 + ∑ s ∈ range t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2) +
        ⟪designOp V₀ (fun s ↦ √μ • g s) t y -
          ∑ s ∈ range t, ((μ * ⟪g s, x s⟫) • g s - g s), z - y⟫ +
        ⟪designOp V₀ (fun s ↦ √μ • g s) t (z - y), z - y⟫ / 2 := by
  -- each surrogate is quadratic: expand it around `y`
  have h_sum : ∑ s ∈ range t, (⟪g s, z⟫ + μ / 2 * ⟪g s, z - x s⟫ ^ 2) =
      ∑ s ∈ range t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2) +
        ∑ s ∈ range t, μ * ⟪g s, y⟫ * ⟪g s, z - y⟫ -
        ∑ s ∈ range t, (μ * ⟪g s, x s⟫ * ⟪g s, z - y⟫ - ⟪g s, z - y⟫) +
        (∑ s ∈ range t, μ * ⟪g s, z - y⟫ * ⟪g s, z - y⟫) / 2 := by
    rw [sum_div, ← sum_add_distrib, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun s _ ↦ ?_
    simp only [inner_sub_right]
    ring
  -- and so is the regularizer, by the symmetry of `V₀`
  have h_V₀ : ⟪V₀ z, z⟫ = ⟪V₀ y, y⟫ + 2 * ⟪V₀ y, z - y⟫ + ⟪V₀ (z - y), z - y⟫ := by
    have h_symm : ⟪V₀ z, y⟫ = ⟪V₀ y, z⟫ := by
      rw [← ContinuousLinearMap.coe_coe, hV₀ z y, real_inner_comm, ContinuousLinearMap.coe_coe]
    simp only [map_sub, inner_sub_left, inner_sub_right]
    linarith
  have h_b (w : E) : ⟪∑ s ∈ range t, ((μ * ⟪g s, x s⟫) • g s - g s), w⟫ =
      ∑ s ∈ range t, (μ * ⟪g s, x s⟫ * ⟪g s, w⟫ - ⟪g s, w⟫) := by
    rw [sum_inner]
    exact sum_congr rfl fun s _ ↦ by rw [inner_sub_left, real_inner_smul_left]
  rw [h_sum, inner_sub_left, inner_designOp_sqrt_smul_apply hμ, inner_designOp_sqrt_smul_apply hμ,
    h_b, h_V₀]
  ring

/-- The surrogate loss `⟪g, ·⟫ + μ / 2 * ⟪g, · - x⟫ ^ 2` has the subgradient `⟪g, ·⟫` at `x`. -/
private lemma hasSubgradientWithinAt_inner_add_mul_sq (hμ : 0 ≤ μ) (g x : E) :
    HasSubgradientWithinAt (fun y ↦ ⟪g, y⟫ + μ / 2 * ⟪g, y - x⟫ ^ 2) (innerSL ℝ g) V x := by
  refine hasSubgradientWithinAt_iff_le.mpr fun y _ ↦ ?_
  simp only [innerSL_apply_apply, sub_self, inner_zero_right, inner_sub_right]
  nlinarith [sq_nonneg (⟪g, y⟫ - ⟪g, x⟫)]

/-- **The regret of the Online Newton Step** [Ora, (7.11), Algorithm 7.6]. Let `V` be convex, `V₀`
be positive definite (positive and invertible) and `μ ≥ 0`. Let the plays `x t ∈ V`, for
`t ≤ n`, minimize over `V` the ONS objective
`⟪V₀ y, y⟫ / 2 + ∑ s < t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2)`, and let the losses lie above
their quadratic surrogates at the comparator `u ∈ V`:
`ℓ t (x t) + ⟪g t, u - x t⟫ + μ / 2 * ⟪g t, u - x t⟫ ^ 2 ≤ ℓ t u` for `t < n` [Ora, (7.12)]. Then
`regret ℓ x u n ≤ ⟪V₀ u, u⟫ / 2 - ⟪V₀ (x 0), x 0⟫ / 2 + ∑ t < n, ‖g t‖²_{S_t⁻¹} / 2`
for the design operators `S_t = designOp V₀ (√μ • g) (t + 1) = V₀ + μ ∑ s ≤ t, g s ⊗ g s`. The
first play `x 0` minimizes `⟪V₀ y, y⟫ / 2` over `V`. -/
theorem regret_le_onlineNewtonStep (hV : Convex ℝ V) (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀)
    (hμ : 0 ≤ μ) (ℓ : ℕ → E → ℝ) (g x : ℕ → E) {u : E} {n : ℕ}
    (hℓ : ∀ t < n, ℓ t (x t) + ⟪g t, u - x t⟫ + μ / 2 * ⟪g t, u - x t⟫ ^ 2 ≤ ℓ t u)
    (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t ≤ n, IsMinOn
      (fun y ↦ ⟪V₀ y, y⟫ / 2 + ∑ s ∈ range t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2)) V (x t))
    (hu : u ∈ V) :
    regret ℓ x u n ≤ ⟪V₀ u, u⟫ / 2 - ⟪V₀ (x 0), x 0⟫ / 2 +
      ∑ t ∈ range n, ⟪g t, Ring.inverse (designOp V₀ (fun s ↦ √μ • g s) (t + 1)) (g t)⟫ / 2 := by
  -- the surrogate losses, and the constant regularizer
  set ℓ' : ℕ → E → ℝ := fun t y ↦ ⟪g t, y⟫ + μ / 2 * ⟪g t, y - x t⟫ ^ 2 with hℓ'
  set ψ : ℕ → E → ℝ := fun _ y ↦ ⟪V₀ y, y⟫ / 2 with hψ
  have hsymm : (V₀ : E →ₗ[ℝ] E).IsSymmetric := hV₀.isSymmetric
  -- Step 1: the regret of the losses is at most the regret of the surrogates
  have h_le : regret ℓ x u n ≤ regret ℓ' x u n := by
    simp only [regret_def, hℓ', sub_self, inner_zero_right]
    refine sum_le_sum fun t ht ↦ ?_
    have h := hℓ t (mem_range.mp ht)
    rw [inner_sub_right] at h ⊢
    nlinarith
  -- Step 2: the FTRL inequality for the surrogates
  have h_ftrl := regret_le_ftrl ψ ℓ' x x (u := u) (n := n) (isMinOn_iff.mp (hmin n le_rfl) u hu)
  refine h_le.trans (h_ftrl.trans ?_)
  simp only [hψ]
  gcongr with t ht
  have ht := mem_range.mp ht
  -- Step 3: the stability of each round, with the quadratic divergence of `S_t`
  have h := ftrl_stability_le_inner_ringInverse (ψ := ψ) (ℓ := ℓ') (x := x) (t := t)
    (z := x (t + 1)) (isPositive_designOp hV₀ (fun s ↦ √μ • g s) (t + 1))
    (isUnit_designOp hV₀ hV₀u (fun s ↦ √μ • g s) (t + 1))
    (hmin t ht.le) (hasSubgradientWithinAt_inner_add_mul_sq hμ (g t) (x t)) (fun h hh z hz ↦ ?_)
    (hx (t + 1) ht)
  · simpa only [hψ, add_sub_cancel_right] using h
  -- the objective of round `t + 1` is quadratic, with Hessian `S_t` and some gradient `w` at
  -- `x t`; every subgradient within `V` at `x t` is bounded by `w` along the directions into `V`
  have h_eq := onlineNewtonStep_objective_eq hsymm hμ g x (t + 1) (x t)
  set w := designOp V₀ (fun s ↦ √μ • g s) (t + 1) (x t) -
    ∑ s ∈ range (t + 1), ((μ * ⟪g s, x s⟫) • g s - g s)
  have hhw : h (z - x t) ≤ ⟪w, z - x t⟫ := by
    refine hh.apply_sub_le_of_le_add_mul_add_sq hV (hx t ht.le) hz
      (C := ⟪designOp V₀ (fun s ↦ √μ • g s) (t + 1) (z - x t), z - x t⟫ / 2) fun τ _ ↦ ?_
    simp only [hψ, hℓ']
    rw [h_eq (x t + τ • (z - x t))]
    simp only [add_sub_cancel_left, map_smul, real_inner_smul_left, real_inner_smul_right]
    linarith
  simp only [hψ, hℓ'] at hhw ⊢
  rw [h_eq z]
  linarith

/-- **The regret of the Online Newton Step, log-determinant form** [Ora, Algorithm 7.6,
Lemma 7.29]. Under the assumptions of `regret_le_onlineNewtonStep`, in finite dimension and with
`μ > 0`,
`regret ℓ x u n ≤ ⟪V₀ u, u⟫ / 2 - ⟪V₀ (x 0), x 0⟫ / 2 + log (det S_{n-1} / det V₀) / (2 μ)`,
where `S_{n-1} = designOp V₀ (√μ • g) n = V₀ + μ ∑ t < n, g t ⊗ g t`. -/
theorem regret_le_onlineNewtonStep_log_det [FiniteDimensional ℝ E] (hV : Convex ℝ V)
    (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (hμ : 0 < μ) (ℓ : ℕ → E → ℝ) (g x : ℕ → E) {u : E}
    {n : ℕ} (hℓ : ∀ t < n, ℓ t (x t) + ⟪g t, u - x t⟫ + μ / 2 * ⟪g t, u - x t⟫ ^ 2 ≤ ℓ t u)
    (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t ≤ n, IsMinOn
      (fun y ↦ ⟪V₀ y, y⟫ / 2 + ∑ s ∈ range t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2)) V (x t))
    (hu : u ∈ V) :
    regret ℓ x u n ≤ ⟪V₀ u, u⟫ / 2 - ⟪V₀ (x 0), x 0⟫ / 2 +
      log (LinearMap.det (designOp V₀ (fun s ↦ √μ • g s) n : E →ₗ[ℝ] E) /
        LinearMap.det (V₀ : E →ₗ[ℝ] E)) / (2 * μ) := by
  refine (regret_le_onlineNewtonStep hV hV₀ hV₀u hμ.le ℓ g x hℓ hx hmin hu).trans ?_
  have h := mul_sum_inner_ringInverse_designOp_sqrt_smul_succ_le_log_det hV₀ hV₀u hμ.le g n
  have h_eq : ∑ t ∈ range n,
      ⟪g t, Ring.inverse (designOp V₀ (fun s ↦ √μ • g s) (t + 1)) (g t)⟫ / 2 =
      (μ * ∑ t ∈ range n,
        ⟪g t, Ring.inverse (designOp V₀ (fun s ↦ √μ • g s) (t + 1)) (g t)⟫) / (2 * μ) := by
    rw [← sum_div]
    field_simp
  rw [h_eq]
  gcongr

/-- **Logarithmic regret of the Online Newton Step** [Ora, Section 7.10]. Under the assumptions of
`regret_le_onlineNewtonStep` with `V₀ = λ • 1`, `λ > 0`, `μ > 0`, in dimension `d` and with
gradients `‖g t‖ ≤ L`,
`regret ℓ x u n ≤ λ / 2 * ‖u‖ ^ 2 - λ / 2 * ‖x 0‖ ^ 2 + d / (2 μ) * log (1 + μ n L ^ 2 / (λ d))`.
The first play `x 0` is a point of `V` of minimal norm. -/
theorem regret_le_onlineNewtonStep_log_one_add [FiniteDimensional ℝ E] (hV : Convex ℝ V)
    {lam L : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (ℓ : ℕ → E → ℝ) (g x : ℕ → E) {u : E} {n : ℕ}
    (hℓ : ∀ t < n, ℓ t (x t) + ⟪g t, u - x t⟫ + μ / 2 * ⟪g t, u - x t⟫ ^ 2 ≤ ℓ t u)
    (hg : ∀ t < n, ‖g t‖ ≤ L) (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t ≤ n, IsMinOn
      (fun y ↦ lam / 2 * ‖y‖ ^ 2 + ∑ s ∈ range t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2)) V (x t))
    (hu : u ∈ V) :
    regret ℓ x u n ≤ lam / 2 * ‖u‖ ^ 2 - lam / 2 * ‖x 0‖ ^ 2 +
      Module.finrank ℝ E / (2 * μ) * log (1 + μ * n * L ^ 2 / (lam * Module.finrank ℝ E)) := by
  -- the regularizer `λ / 2 * ‖y‖ ^ 2` is `⟪(λ • 1) y, y⟫ / 2`
  have h_reg (y : E) : ⟪(lam • 1 : E →L[ℝ] E) y, y⟫ / 2 = lam / 2 * ‖y‖ ^ 2 := by
    simp only [smul_apply, one_apply_eq_self,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have h := regret_le_onlineNewtonStep_log_det hV (ContinuousLinearMap.isPositive_smul_one hlam.le)
    (ContinuousLinearMap.isUnit_smul_one hlam.ne') hμ ℓ g x hℓ hx (by simpa only [h_reg] using hmin)
    hu
  rw [h_reg, h_reg, ContinuousLinearMap.det_smul_one] at h
  refine h.trans ?_
  -- the vectors `√μ • g t` have norm at most `√μ L`
  have h_det := log_det_designOp_div_pow_le hlam (fun s ↦ √μ • g s) (L := √μ * L) (t := n)
    fun s hs ↦ by
      rw [norm_smul, Real.norm_of_nonneg (sqrt_nonneg μ)]
      exact mul_le_mul_of_nonneg_left (hg s hs) (sqrt_nonneg μ)
  rw [mul_pow, sq_sqrt hμ.le] at h_det
  rw [add_le_add_iff_left]
  calc _ ≤ Module.finrank ℝ E * log (1 + μ * n * L ^ 2 / (lam * Module.finrank ℝ E)) / (2 * μ) := by
        gcongr
        convert h_det using 3
        ring
    _ = _ := by ring

/-- **Logarithmic regret of the Online Newton Step on exp-concave losses** [Ora, Section 7.10,
Example 7.39]. Let the losses `ℓ t` be `α`-exp-concave on a convex set `V`, with subgradients
`⟪g t, ·⟫` within `V` at the plays, `‖g t‖ ≤ L` and `|⟪g t, u - x t⟫| ≤ B` (for instance
`B = D L` on a set of diameter `D`). If the plays are those of the ONS with `V₀ = λ • 1`, `λ > 0`,
and a parameter `0 < μ` with `2 μ ≤ min α B⁻¹`, then for `u ∈ V`
`regret ℓ x u n ≤ λ / 2 * ‖u‖ ^ 2 - λ / 2 * ‖x 0‖ ^ 2 + d / (2 μ) * log (1 + μ n L ^ 2 / (λ d))`.
-/
theorem regret_le_onlineNewtonStep_of_expConcaveOn [FiniteDimensional ℝ E] (hV : Convex ℝ V)
    {lam L α B : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (hμαB : 2 * μ ≤ min α B⁻¹) (ℓ : ℕ → E → ℝ)
    (g x : ℕ → E) {u : E} {n : ℕ} (hℓ : ∀ t < n, ExpConcaveOn V α (ℓ t))
    (hgℓ : ∀ t < n, HasSubgradientWithinAt (ℓ t) (innerSL ℝ (g t)) V (x t))
    (hgB : ∀ t < n, |⟪g t, u - x t⟫| ≤ B) (hg : ∀ t < n, ‖g t‖ ≤ L) (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t ≤ n, IsMinOn
      (fun y ↦ lam / 2 * ‖y‖ ^ 2 + ∑ s ∈ range t, (⟪g s, y⟫ + μ / 2 * ⟪g s, y - x s⟫ ^ 2)) V (x t))
    (hu : u ∈ V) :
    regret ℓ x u n ≤ lam / 2 * ‖u‖ ^ 2 - lam / 2 * ‖x 0‖ ^ 2 +
      Module.finrank ℝ E / (2 * μ) * log (1 + μ * n * L ^ 2 / (lam * Module.finrank ℝ E)) := by
  refine regret_le_onlineNewtonStep_log_one_add hV hlam hμ ℓ g x (fun t ht ↦ ?_) hg hx hmin hu
  -- the quadratic lower bound of exp-concave functions, with the smaller curvature `μ`
  have h := (hℓ t ht).add_apply_add_min_mul_sq_le_of_hasSubgradientWithinAt (hx t ht.le)
    (hgℓ t ht) hu (by simpa only [innerSL_apply_apply] using hgB t ht)
  simp only [innerSL_apply_apply] at h
  nlinarith [sq_nonneg ⟪g t, u - x t⟫]

/-- **The two-step form of the Online Newton Step** [Ora, Problem 7.12]. For a positive definite
`V₀` and `μ ≥ 0`, the minimizers over any set `V` of the ONS objective
`⟪V₀ z, z⟫ / 2 + ∑ s < t, (⟪g s, z⟫ + μ / 2 * ⟪g s, z - x s⟫ ^ 2)` are the minimizers over `V` of
the squared distance `⟪S (z - c), z - c⟫` to the unconstrained minimizer
`c = S⁻¹ (∑ s < t, (μ ⟪g s, x s⟫ • g s - g s))`, in the norm of the design operator
`S = designOp V₀ (√μ • g) t = V₀ + μ ∑ s < t, g s ⊗ g s`: an ONS play is an unconstrained step
followed by a projection onto `V` in the norm of `S`. -/
theorem isMinOn_onlineNewtonStep_iff (hV₀ : V₀.IsPositive) (hV₀u : IsUnit V₀) (hμ : 0 ≤ μ)
    (g x : ℕ → E) (t : ℕ) (V : Set E) (y : E) :
    IsMinOn (fun z ↦ ⟪V₀ z, z⟫ / 2 + ∑ s ∈ range t, (⟪g s, z⟫ + μ / 2 * ⟪g s, z - x s⟫ ^ 2)) V y ↔
      IsMinOn (fun z ↦ ⟪designOp V₀ (fun s ↦ √μ • g s) t
          (z - Ring.inverse (designOp V₀ (fun s ↦ √μ • g s) t)
            (∑ s ∈ range t, ((μ * ⟪g s, x s⟫) • g s - g s))),
        z - Ring.inverse (designOp V₀ (fun s ↦ √μ • g s) t)
          (∑ s ∈ range t, ((μ * ⟪g s, x s⟫) • g s - g s))⟫) V y := by
  set S := designOp V₀ (fun s ↦ √μ • g s) t
  set b := ∑ s ∈ range t, ((μ * ⟪g s, x s⟫) • g s - g s)
  -- completing the square: the gradient of the objective vanishes at `S⁻¹ b`
  have hc : S (Ring.inverse S b) = b :=
    ContinuousLinearMap.apply_ringInverse_apply (isUnit_designOp hV₀ hV₀u _ t) b
  have key (z : E) : ⟪V₀ z, z⟫ / 2 + ∑ s ∈ range t, (⟪g s, z⟫ + μ / 2 * ⟪g s, z - x s⟫ ^ 2) =
      ⟪V₀ (Ring.inverse S b), Ring.inverse S b⟫ / 2 + ∑ s ∈ range t,
        (⟪g s, Ring.inverse S b⟫ + μ / 2 * ⟪g s, Ring.inverse S b - x s⟫ ^ 2) +
        ⟪S (z - Ring.inverse S b), z - Ring.inverse S b⟫ / 2 := by
    have h := onlineNewtonStep_objective_eq hV₀.isSymmetric hμ g x t (Ring.inverse S b) z
    rwa [hc, sub_self, inner_zero_left, add_zero] at h
  simp only [isMinOn_iff]
  refine forall₂_congr fun z _ ↦ ?_
  rw [key y, key z]
  constructor <;> intro h <;> linarith

end LMLExplore.OnlineLearning
