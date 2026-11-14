/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Proximal
public import LMLExplore.OnlineLearning.FTRL.Stability
public import LMLExplore.OnlineLearning.SubgradientDescent

/-!
# FTRL with composite losses

A *composite* loss `ℓ t + r` is the sum of a loss `ℓ t` revealed at round `t` and a fixed, known
function `r`, such as an `ℓ¹` penalty `lam * ‖·‖₁` [Ora, Section 7.8]. Instead of linearizing the
whole loss, FTRL can keep `r` exact by moving it into the regularizer: on a set `V` of a real
normed space, its play at round `t` minimizes over `V`
`ψ t + (t + 1) * r + ∑ s < t, ℓ s`,
which anticipates the term `r` of the current round. With subgradients `g t` of `ℓ t` alone,
strong convexity of the objectives `ψ t + (t + 1) * r + ∑ s ≤ t, ℓ s` gives, for the composite
losses, the bound of FTRL for convex losses (`regret_le_ftrl_of_strongConvexOn`): for every
comparator `u` that does no better than the last point on the last objective,
`regret (ℓ + r) x u n ≤ ψ n u - ψ 0 (x 0) + ∑ t < n, ‖g t‖ ^ 2 / (2 lam t)
  + ∑ t < n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`.
Only the subgradients of `ℓ t` enter the bound, never those of `r`, and `r` need not be convex
when the objectives are strongly convex. Run on the linearized losses `g t` of convex losses
`f t`, the plays minimize `ψ t + (t + 1) * r + ∑ s < t, g s` and the same bound holds for the
composite losses `f t + r`.

For the regularizer `‖·‖ ^ 2 / (2 η)` and `r = lam * ‖·‖₁` on `EuclideanSpace ℝ α`, without
constraints, the play is a soft thresholding of the cumulative gradient, hence sparse
[Ora, Example 7.24].

## Main statements

* `regret_le_ftrl_composite_of_strongConvexOn`: [Ora, Section 7.8] the regret of FTRL for
  composite losses.
* `regret_le_ftrl_linearized_composite_of_strongConvexOn`: [Ora, Section 7.8] its form for FTRL
  run on the linearized losses, with the composite term kept exact.
* `isMinOn_norm_sq_div_add_mul_sum_abs_add_inner_iff`: [Ora, Example 7.24] the minimizer of
  `‖x‖ ^ 2 / (2 η) + c * ∑ a, |x a| + ⟪θ, x⟫` is the coordinatewise soft thresholding
  `η * softThreshold c (-θ a)`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Section 7.8, Example 7.24.
-/
public section

open Finset Set
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E}

/-- **The regret of FTRL for composite losses** [Ora, Section 7.8]. Let `x t ∈ V`, for `t ≤ n`,
and let `x t`, for `t < n`, minimize over `V` the objective `ψ t + (t + 1) * r + ∑ s < t, ℓ s`, in
which the composite term `r` of the current round is anticipated. Let `g t` be a subgradient of
`ℓ t` within `V` at `x t`, and let `ψ t + (t + 1) * r + ∑ s ≤ t, ℓ s` be `lam t`-strongly convex
on `V`, with `lam t > 0`, for `t < n`. If the last point does at least as well as the comparator
`u` on the last objective without anticipation, `ψ n + n * r + ∑ s < n, ℓ s`, then the regret of
the composite losses `ℓ t + r` satisfies
`regret (ℓ + r) x u n ≤ ψ n u - ψ 0 (x 0) + ∑ t < n, ‖g t‖ ^ 2 / (2 lam t)
  + ∑ t < n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`,
where `‖g t‖` is the dual norm. No subgradient of `r` is needed, and `r` need not be convex. For
`r = 0` this is `regret_le_ftrl_of_strongConvexOn`. -/
theorem regret_le_ftrl_composite_of_strongConvexOn (ψ ℓ : ℕ → E → ℝ) (r : E → ℝ) (x : ℕ → E)
    (g : ℕ → E →L[ℝ] ℝ) {lam : ℕ → ℝ} {u : E} {n : ℕ} (hlam : ∀ t < n, 0 < lam t)
    (hΦ : ∀ t < n, StrongConvexOn V (lam t)
      fun a ↦ ψ t a + (t + 1 : ℝ) * r a + ∑ s ∈ range (t + 1), ℓ s a)
    (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + (t + 1 : ℝ) * r a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : ∀ t < n, HasSubgradientWithinAt (ℓ t) (g t) V (x t))
    (hxn : ψ n (x n) + n * r (x n) + ∑ s ∈ range n, ℓ s (x n) ≤
      ψ n u + n * r u + ∑ s ∈ range n, ℓ s u) :
    regret (fun t a ↦ ℓ t a + r a) x u n ≤ ψ n u - ψ 0 (x 0) +
      ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * lam t) +
        ∑ t ∈ range n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1))) := by
  have h_sum (t : ℕ) (a : E) : ∑ s ∈ range t, (ℓ s a + r a) = ∑ s ∈ range t, ℓ s a + t * r a := by
    simp [sum_add_distrib]
  -- the FTRL inequality for the regularizers `ψ t` and the composite losses, whose objectives
  -- `ψ t + t * r + ∑ s < t, ℓ s` do not anticipate `r`
  refine (regret_le_ftrl ψ (fun t a ↦ ℓ t a + r a) x x ?_).trans ?_
  · simp only [h_sum]
    linarith
  rw [add_assoc, ← sum_add_distrib]
  refine add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_)
  have ht := mem_range.mp ht
  -- the stability of the round for the anticipating regularizers `ψ t + (t + 1) * r`
  have h := ftrl_stability_le_norm_sq_div_of_strongConvexOn (ψ := fun t a ↦ ψ t a + (t + 1) * r a)
    (hlam t ht) (hmin t ht) (hg t ht) (hΦ t ht) (hx t ht.le) (hx (t + 1) ht)
  simp only [h_sum, Nat.cast_add, Nat.cast_one] at h ⊢
  linear_combination h

/-- **The regret of linearized FTRL for composite losses** [Ora, Section 7.8]. Let `x t ∈ V`, for
`t ≤ n`, and let `x t`, for `t < n`, minimize over `V` the objective
`ψ t + (t + 1) * r + ∑ s < t, g s`, where `g s` is a subgradient of the loss `f s` within `V` at
`x s`: the losses are linearized but the composite term `r` is not. Let `ψ t + (t + 1) * r` be
`lam t`-strongly convex on `V`, with `lam t > 0`, for `t < n`. If the last point does at least as
well as `u ∈ V` on the last objective without anticipation, `ψ n + n * r + ∑ s < n, g s`, then
the regret of the composite losses `f t + r` satisfies
`regret (f + r) x u n ≤ ψ n u - ψ 0 (x 0) + ∑ t < n, ‖g t‖ ^ 2 / (2 lam t)
  + ∑ t < n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`,
where `‖g t‖` is the dual norm. -/
theorem regret_le_ftrl_linearized_composite_of_strongConvexOn (ψ f : ℕ → E → ℝ) (r : E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) {lam : ℕ → ℝ} {u : E} {n : ℕ} (hlam : ∀ t < n, 0 < lam t)
    (hψ : ∀ t < n, StrongConvexOn V (lam t) fun a ↦ ψ t a + (t + 1 : ℝ) * r a)
    (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + (t + 1 : ℝ) * r a + ∑ s ∈ range t, g s a) V (x t))
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (g t) V (x t)) (hu : u ∈ V)
    (hxn : ψ n (x n) + n * r (x n) + ∑ s ∈ range n, g s (x n) ≤
      ψ n u + n * r u + ∑ s ∈ range n, g s u) :
    regret (fun t a ↦ f t a + r a) x u n ≤ ψ n u - ψ 0 (x 0) +
      ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * lam t) +
        ∑ t ∈ range n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1))) := by
  -- adding the linear map `∑ s ≤ t, g s` preserves strong convexity
  have hΦ (t : ℕ) (ht : t < n) : StrongConvexOn V (lam t)
      fun a ↦ ψ t a + (t + 1 : ℝ) * r a + ∑ s ∈ range (t + 1), g s a := by
    have h := (hψ t ht).add_convexOn
      ((∑ s ∈ range (t + 1), g s).toLinearMap.convexOn (hψ t ht).1)
    convert h using 1
    ext a
    simp
  have h := regret_le_ftrl_composite_of_strongConvexOn ψ (fun s ↦ g s) r x g hlam hΦ hx hmin
    (fun t _ ↦ hasSubgradientWithinAt_linear (g t)) hxn
  -- the losses `f t` have regret at most that of their linearizations `g t`
  have h_lin := sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f g x hg hu
  have h_add (ℓ : ℕ → E → ℝ) : regret (fun t a ↦ ℓ t a + r a) x u n =
      regret ℓ x u n + regret (fun _ ↦ r) x u n := regret_add ℓ (fun _ ↦ r) x u n
  rw [h_add] at h ⊢
  rw [regret_eq_sum_apply_sub g] at h
  rw [regret_def]
  linarith

end NormedSpace

section Euclidean

variable {α : Type*} [Fintype α]

/-- **The plays of FTRL with an `ℓ¹` composite term are soft thresholdings** [Ora, Example 7.24].
On `EuclideanSpace ℝ α`, for `η > 0` and a level `c ≥ 0`, the function
`x ↦ ‖x‖ ^ 2 / (2 η) + c * ∑ a, |x a| + ⟪θ, x⟫` has exactly one minimizer, with coordinates
`η * softThreshold c (-θ a)`. For the regularizers `‖·‖ ^ 2 / (2 η t)`, the composite term
`r = lam * ∑ a, |· a|` and linear losses `⟪v s, ·⟫` without constraints, the play of round `t` of
`regret_le_ftrl_linearized_composite_of_strongConvexOn` is thus the soft thresholding at the
level `(t + 1) * lam` of the opposite of the cumulative gradient `θ = ∑ s < t, v s`, scaled by
`η t`: its coordinates vanish wherever `|θ a| ≤ (t + 1) * lam`. -/
theorem isMinOn_norm_sq_div_add_mul_sum_abs_add_inner_iff {η : ℝ} (hη : 0 < η) {c : ℝ}
    (hc : 0 ≤ c) (θ y : EuclideanSpace ℝ α) :
    IsMinOn (fun x ↦ ‖x‖ ^ 2 / (2 * η) + c * ∑ a, |x a| + ⟪θ, x⟫) univ y ↔
      y = WithLp.toLp 2 (fun a ↦ η * softThreshold c (-θ a)) := by
  -- completing the square: the objective is the proximal objective of `η * c * ∑ a, |· a|` from
  -- `-(η • θ)`, divided by `η`, plus a constant
  have h_sq (x : EuclideanSpace ℝ α) : ‖x‖ ^ 2 / (2 * η) + c * ∑ a, |x a| + ⟪θ, x⟫ =
      ((η * c) * ∑ a, |x a| + ‖x - -(η • θ)‖ ^ 2 / 2) / η - η * ‖θ‖ ^ 2 / 2 := by
    rw [sub_neg_eq_add, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hη, real_inner_comm]
    field_simp
    ring
  have h_soft : (fun a ↦ softThreshold (η * c) ((-(η • θ)) a)) =
      fun a ↦ η * softThreshold c (-θ a) := funext fun a ↦ by
    rw [← softThreshold_mul hη.le]
    simp
  rw [← h_soft, ← isMinOn_mul_sum_abs_add_norm_sub_sq_iff (mul_nonneg hη.le hc),
    isMinOn_univ_iff, isMinOn_univ_iff]
  refine forall_congr' fun b ↦ ?_
  rw [h_sq, h_sq, sub_le_sub_iff_right, div_le_div_iff_of_pos_right hη]

end Euclidean

end LMLExplore.OnlineLearning
