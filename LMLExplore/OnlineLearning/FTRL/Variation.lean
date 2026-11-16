/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Smooth
public import LMLExplore.Analysis.Normed.Group.Basic
public import LMLExplore.Analysis.SumIntegralComparisons
public import LMLExplore.OnlineLearning.FTRL.Optimistic
public import LMLExplore.OnlineLearning.FTRL.Quadratic
public import LMLExplore.OnlineLearning.SubgradientDescent

/-!
# Optimistic FTRL with the variance and the gradual variation of the losses

Optimistic follow the regularized leader (`LMLExplore.OnlineLearning.FTRL.Optimistic`) pays, at
each round, for the error of a hint that predicts the loss to come. This file gives two choices of
hints from the past losses, and the regret bounds they lead to [Ora, Sections 7.14 and 7.15].

**The variance of the subgradients** [Ora, Section 7.14]. On a real inner product space, predict
the vector `g t` of a linear loss by the running mean `m t = (t)⁻¹ • ∑ s < t, g s` of the past
ones, with `m 0 = 0`. The running means are follow-the-leader on the squared distances
`‖· - g t‖ ^ 2`, which are `2`-strongly convex, so for `‖g t‖ ≤ G` their errors satisfy
`∑ t < n, ‖m t - g t‖ ^ 2 ≤ 4 G ^ 2 (1 + log n) + ∑ t < n, ‖w - g t‖ ^ 2` for every `w`. The sum
on the right is smallest at the mean of the `g t`, where it is `n` times their empirical
variance. Optimistic FTRL with these hints and a fixed `λ`-strongly convex regularizer `ψ` has
regret at most `ψ u - ψ (x 0) + (4 G ^ 2 (1 + log n) + ∑ t < n, ‖g t - w‖ ^ 2) / (2 λ)`: the
variance term replaces the term `n G ^ 2` of plain FTRL, up to a term `G ^ 2 log n`.

**Gradual variations** [CYLMLJZ12; Ora, Section 7.15, Corollary 7.52]. In a real normed space,
predict the loss of round `t + 1` by the linearization `ℓ' t (x t)` of the loss of round `t` at
its play, where `ℓ' t a` is a subgradient of `ℓ t` at `a` (its derivative, for differentiable
losses). With the regularizers `λ t ψ`, for `ψ` nonnegative and `1`-strongly convex on `V`, rates
`λ t` nondecreasing with `λ t λ (t + 1) ≥ 8 m ^ 2`, and losses whose subgradients are
`m`-Lipschitz at consecutive plays, as for `m`-smooth losses, the regret against `u` is at most
`λ (n - 1) ψ u - λ 0 ψ (x 0) + ‖ℓ' 0 (x 0)‖ ^ 2 / λ 0
  + ∑ t < n - 1, 2 ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2 / λ (t + 1)`.
The sum measures the variation of the gradients between consecutive losses at a common point:
when all the losses are equal it vanishes, and with constant rates the regret is bounded by a
constant. With the adaptive rates
`λ t = √(max (8 α ^ 2 m ^ 2) (4 L ^ 2) + ∑ s < t - 1, ‖ℓ' (s + 1) (x s) - ℓ' s (x s)‖ ^ 2) / α`
for gradients of norm at most `L`, the regret is at most
`(ψ u / α + 4 α) √(max (8 α ^ 2 m ^ 2) (4 L ^ 2) + ∑ t < n - 1, ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2)
  + α L / 2`,
with no bound on the diameter of `V`.

## Main statements

* `sum_norm_inv_smul_sum_sub_sq_le`: [Ora, Section 7.14] the squared errors of the running means.
* `regret_le_optimistic_ftrl_sum_norm_sub_sq`: [Ora, Section 7.14] the regret of optimistic FTRL
  with the running means as hints, through the variance of the subgradients.
* `regret_le_optimistic_ftrl_gradual`: [Ora, Corollary 7.52, first bound] the regret of
  optimistic FTRL with the last gradients as hints, for subgradients Lipschitz at the plays;
  `regret_le_optimistic_ftrl_gradual_of_smoothOn` for convex smooth losses.
* `regret_le_optimistic_ftrl_gradual_mul_sqrt`: [Ora, Corollary 7.52, second bound] the same
  with the adaptive rates; `regret_le_optimistic_ftrl_gradual_mul_sqrt_of_smoothOn` for convex
  smooth losses with bounded gradients.

## Implementation notes

The hints are linear, `m t` and `ℓ' (t - 1) (x (t - 1))` (`0` at round `0`), and the theorems
take as hypotheses that the plays minimize the corresponding objectives over `V`. The proofs
apply the regret bounds of optimistic FTRL [Ora, Theorem 7.47] of
`LMLExplore.OnlineLearning.FTRL.Optimistic`.

[Ora] states the second bound of Corollary 7.52 with `(ψ u - ψ (x 0)) / α` in place of
`ψ u / α`. The term `-λ 0 ψ (x 0)` of the first bound only gives `-√(max …) / α * ψ (x 0)`, which
is not `-ψ (x 0) / α` times the final square root, so the bound here drops it, as it may since
`ψ ≥ 0`. [Ora] also uses `ψ ≥ 0` without stating it, to discard the increments
`(λ t - λ (t + 1)) ψ (x (t + 1))` of the regularizers.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Sections 7.14 and 7.15, Corollary 7.52.
* [CYLMLJZ12] C.-K. Chiang, T. Yang, C.-J. Lee, M. Mahdavi, C.-J. Lu, R. Jin and S. Zhu, *Online
  optimization with gradual variations*, COLT 2012.
-/
public section

open Finset
open scoped RealInnerProductSpace NNReal

namespace LMLExplore.OnlineLearning

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V : Set E}

/-- **The running mean predicts with logarithmic regret** [Ora, Section 7.14]. Let `‖g t‖ ≤ G` for
`t < n`. The running means `m t = (t)⁻¹ • ∑ s < t, g s`, with `m 0 = 0`, satisfy, for every `u`,
`∑ t < n, ‖m t - g t‖ ^ 2 ≤ 4 G ^ 2 (1 + log n) + ∑ t < n, ‖u - g t‖ ^ 2`.
The running means are follow-the-leader on the `2`-strongly convex losses `‖· - g t‖ ^ 2`. -/
theorem sum_norm_inv_smul_sum_sub_sq_le (g : ℕ → E) {G : ℝ} {n : ℕ} (hg : ∀ t < n, ‖g t‖ ≤ G)
    (u : E) :
    ∑ t ∈ range n, ‖(t : ℝ)⁻¹ • ∑ s ∈ range t, g s - g t‖ ^ 2 ≤
      4 * G ^ 2 * (1 + Real.log n) + ∑ t ∈ range n, ‖u - g t‖ ^ 2 := by
  set x : ℕ → E := fun t ↦ (t : ℝ)⁻¹ • ∑ s ∈ range t, g s with hx_def
  -- the running means are bounded by `G`
  have hx (t : ℕ) (ht : t < n) : ‖x t‖ ≤ G := by
    have hG : 0 ≤ G := (norm_nonneg _).trans (hg 0 (by omega))
    rcases t.eq_zero_or_pos with rfl | ht0
    · simpa [x] using hG
    have h := norm_sum_le_card_mul (range t) fun s hs ↦ hg s ((mem_range.mp hs).trans ht)
    rw [card_range] at h
    rw [hx_def, norm_smul, norm_inv, RCLike.norm_natCast, inv_mul_le_iff₀ (by positivity)]
    exact h
  -- follow-the-leader on the squared distances, which are `2`-strongly convex
  have h := regret_le_ftl_of_strongConvexOn (V := Set.univ) (fun t a ↦ ‖a - g t‖ ^ 2) x
    (fun t ↦ innerSL ℝ ((2 : ℝ) • (x t - g t))) (μ := fun _ ↦ 2) (u := u) (n := n)
    (fun t _ ↦ by
      convert strongConvexOn_div_two_mul_norm_sub_sq convex_univ 2 (g t) using 2 with a
      ring)
    (fun t _ ↦ by simp only [sum_const, card_range, nsmul_eq_mul]; positivity)
    (fun _ _ ↦ Set.mem_univ _)
    (fun t _ ↦ by simpa [x] using isMinOn_sum_norm_sub_sq_inv_smul_sum (range t) g)
    (fun t _ ↦ hasSubgradientWithinAt_norm_sub_sq _ _ _) (Set.mem_univ u)
  -- each stability term is `‖x t - g t‖ ^ 2 / (t + 1) ≤ 4 G ^ 2 / (t + 1)`
  have h_stab : ∀ t ∈ range n,
      ‖innerSL ℝ ((2 : ℝ) • (x t - g t))‖ ^ 2 / (2 * ∑ s ∈ range (t + 1), (2 : ℝ)) ≤
        4 * G ^ 2 * ((t : ℝ) + 1)⁻¹ := by
    intro t ht
    have ht := mem_range.mp ht
    have h_norm : ‖x t - g t‖ ≤ 2 * G := by
      linarith [norm_sub_le (x t) (g t), hx t ht, hg t ht]
    calc ‖innerSL ℝ ((2 : ℝ) • (x t - g t))‖ ^ 2 / (2 * ∑ s ∈ range (t + 1), (2 : ℝ))
        = ‖x t - g t‖ ^ 2 / ((t : ℝ) + 1) := by
          simp only [innerSL_apply_norm, norm_smul, Real.norm_ofNat, sum_const, card_range,
            nsmul_eq_mul]
          push_cast
          field_simp
      _ ≤ (2 * G) ^ 2 / ((t : ℝ) + 1) := by gcongr
      _ = 4 * G ^ 2 * ((t : ℝ) + 1)⁻¹ := by ring
  have h_log : ∑ t ∈ range n, 4 * G ^ 2 * ((t : ℝ) + 1)⁻¹ ≤ 4 * G ^ 2 * (1 + Real.log n) := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (Real.sum_range_inv_add_one_le n) (by positivity)
  have h_sum := (h.trans (sum_le_sum h_stab)).trans h_log
  rw [regret_def, sum_sub_distrib] at h_sum
  linarith

/-- **Optimistic FTRL with the running means as hints** [Ora, Section 7.14]. Let `ψ` be
`lam`-strongly convex on `V`, with `lam > 0`, let `0 < n` and, for `t < n`, let `‖g t‖ ≤ G`, let
`x t ∈ V` minimize over `V` the objective `ψ + ∑ s < t, ⟪g s, ·⟫ + ⟪m t, ·⟫` of optimistic FTRL
with the linear losses `⟪g s, ·⟫` and the running means `m t = (t)⁻¹ • ∑ s < t, g s` as hints,
and let `⟪g t, ·⟫` be a subgradient of the loss `f t` within `V` at `x t`. Then for every `u ∈ V`
and every `w`,
`regret f x u n ≤ ψ u - ψ (x 0) + (4 G ^ 2 (1 + log n) + ∑ t < n, ‖g t - w‖ ^ 2) / (2 lam)`.
With `w` the mean of the `g t`, the sum is `n` times the empirical variance of the subgradients. -/
theorem regret_le_optimistic_ftrl_sum_norm_sub_sq (ψ : E → ℝ) (f : ℕ → E → ℝ) (g x : ℕ → E)
    {lam G : ℝ} {u : E} {n : ℕ} (hn : 0 < n) (hlam : 0 < lam) (hψ : StrongConvexOn V lam ψ)
    (hg : ∀ t < n, ‖g t‖ ≤ G) (hx : ∀ t < n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ a + ∑ s ∈ range t, ⟪g s, a⟫ +
      ⟪(t : ℝ)⁻¹ • ∑ s ∈ range t, g s, a⟫) V (x t))
    (hf : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) V (x t)) (hu : u ∈ V)
    (w : E) :
    regret f x u n ≤ ψ u - ψ (x 0) +
      (4 * G ^ 2 * (1 + Real.log n) + ∑ t ∈ range n, ‖g t - w‖ ^ 2) / (2 * lam) := by
  -- the regret of the convex losses is at most that of their linearizations
  have h_lin := sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f (fun t ↦ innerSL ℝ (g t))
    x hf hu
  -- the regret of optimistic FTRL on the linear losses, with the prediction errors `g t - m t`
  have h := regret_le_optimistic_ftrl_norm_sq_div_of_strongConvexOn (V := V) (fun _ ↦ ψ)
    (fun t a ↦ ⟪g t, a⟫) (fun t a ↦ ⟪(t : ℝ)⁻¹ • ∑ s ∈ range t, g s, a⟫) x
    (fun t ↦ innerSL ℝ (g t - (t : ℝ)⁻¹ • ∑ s ∈ range t, g s))
    (lam := fun _ ↦ lam) (u := u) hn (fun _ _ ↦ hlam)
    (fun t _ ↦ by
      simpa using hψ.add_continuousLinearMap (∑ s ∈ range (t + 1), innerSL ℝ (g s)))
    hx hmin
    (fun t _ ↦ by
      convert hasSubgradientWithinAt_linear
        (innerSL ℝ (g t - (t : ℝ)⁻¹ • ∑ s ∈ range t, g s)) using 1
      ext a
      simp only [innerSL_apply_apply, inner_sub_left])
    hu
  simp only [sub_self, sum_const_zero, add_zero, innerSL_apply_norm, ← sum_div] at h
  have h_var := sum_norm_inv_smul_sum_sub_sq_le g hg w
  simp only [norm_sub_rev _ (g _)] at h_var
  have h_reg : regret (fun t a ↦ ⟪g t, a⟫) x u n = ∑ t ∈ range n, innerSL ℝ (g t) (x t - u) := by
    simp [regret_def, inner_sub_right]
  rw [regret_def]
  rw [h_reg] at h
  have h_div := div_le_div_of_nonneg_right h_var (by positivity : (0 : ℝ) ≤ 2 * lam)
  linarith

end InnerProductSpace

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E}

/-- The stability terms of optimistic FTRL with the last gradients as hints telescope. Let
`lam t > 0` for `t ≤ N` and `8 m ^ 2 ≤ lam t * lam (t + 1)` for `t < N`, and let the prediction
errors `G t` satisfy `‖G (t + 1)‖ ≤ m ‖y t - y (t + 1)‖ + δ t` for `t < N`. Then
`∑ t ≤ N, (G t (y t - y (t + 1)) - lam t / 2 * ‖y t - y (t + 1)‖ ^ 2)
  ≤ ‖G 0‖ ^ 2 / lam 0 + ∑ t < N, 2 δ t ^ 2 / lam (t + 1)`. -/
private lemma sum_stability_le_of_norm_le (G : ℕ → E →L[ℝ] ℝ) (y : ℕ → E) (lam δ : ℕ → ℝ)
    {m : ℝ} {N : ℕ} (hlam : ∀ t ≤ N, 0 < lam t)
    (hlam_mul : ∀ t < N, 8 * m ^ 2 ≤ lam t * lam (t + 1))
    (hG : ∀ t < N, ‖G (t + 1)‖ ≤ m * ‖y t - y (t + 1)‖ + δ t) :
    ∑ t ∈ range (N + 1), (G t (y t - y (t + 1)) - lam t / 2 * ‖y t - y (t + 1)‖ ^ 2) ≤
      ‖G 0‖ ^ 2 / lam 0 + ∑ t ∈ range N, 2 * δ t ^ 2 / lam (t + 1) := by
  set d : ℕ → ℝ := fun t ↦ ‖y t - y (t + 1)‖ with hd
  -- each stability term is at most `‖G t‖ ^ 2 / lam t - lam t / 4 * d t ^ 2`
  have h_round (t : ℕ) (ht : t ≤ N) :
      G t (y t - y (t + 1)) - lam t / 2 * d t ^ 2 ≤ ‖G t‖ ^ 2 / lam t - lam t / 4 * d t ^ 2 := by
    have h := apply_sub_sub_mul_norm_sq_le (half_pos (hlam t ht)) (G t) (y t) (y (t + 1))
    rw [show lam t / 2 / 2 = lam t / 4 by ring, show 2 * (lam t / 2) = lam t by ring] at h
    simp only [hd]
    linarith
  -- after the first round, the part `m d t` of the error is absorbed by the previous round
  have h_succ (t : ℕ) (ht : t < N) : ‖G (t + 1)‖ ^ 2 / lam (t + 1) ≤
      lam t / 4 * d t ^ 2 + 2 * δ t ^ 2 / lam (t + 1) := by
    have hl := hlam (t + 1) ht
    have h_sq : ‖G (t + 1)‖ ^ 2 ≤ 2 * m ^ 2 * d t ^ 2 + 2 * δ t ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (hG t ht) 2
      nlinarith [sq_nonneg (m * d t - δ t)]
    have h_md : 8 * m ^ 2 * d t ^ 2 ≤ lam t * lam (t + 1) * d t ^ 2 :=
      mul_le_mul_of_nonneg_right (hlam_mul t ht) (sq_nonneg _)
    have h_key : ‖G (t + 1)‖ ^ 2 ≤ lam t * lam (t + 1) / 4 * d t ^ 2 + 2 * δ t ^ 2 := by
      linarith
    calc ‖G (t + 1)‖ ^ 2 / lam (t + 1)
        ≤ (lam t * lam (t + 1) / 4 * d t ^ 2 + 2 * δ t ^ 2) / lam (t + 1) := by gcongr
      _ = lam t / 4 * d t ^ 2 + 2 * δ t ^ 2 / lam (t + 1) := by field_simp
  rw [sum_range_succ']
  have h_tail : ∑ t ∈ range N, (G (t + 1) (y (t + 1) - y (t + 1 + 1)) -
      lam (t + 1) / 2 * ‖y (t + 1) - y (t + 1 + 1)‖ ^ 2) ≤
      ∑ t ∈ range N, (lam t / 4 * d t ^ 2 - lam (t + 1) / 4 * d (t + 1) ^ 2) +
        ∑ t ∈ range N, 2 * δ t ^ 2 / lam (t + 1) := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun t ht ↦ ?_
    have ht := mem_range.mp ht
    linarith [h_round (t + 1) ht, h_succ t ht]
  rw [sum_range_sub' (fun t ↦ lam t / 4 * d t ^ 2)] at h_tail
  have h0 := h_round 0 (Nat.zero_le N)
  have hN : 0 ≤ lam N / 4 * d N ^ 2 := by have := hlam N le_rfl; positivity
  linarith

/-- **Optimistic FTRL with gradual variations** [CYLMLJZ12; Ora, Corollary 7.52, first bound].
Let `ψ` be nonnegative and `1`-strongly convex on `V`, let the losses `ℓ t` be convex on `V`, and
let `ℓ' t (x t)` be a subgradient of `ℓ t` within `V` at the play `x t ∈ V`, for `t < n`, with
`0 < n`. Let the subgradients be `m`-Lipschitz at consecutive plays:
`‖ℓ' (t + 1) (x (t + 1)) - ℓ' (t + 1) (x t)‖ ≤ m ‖x (t + 1) - x t‖`. Let the rates satisfy
`0 < lam t`, `lam t ≤ lam (t + 1)` and `8 m ^ 2 ≤ lam t * lam (t + 1)`. Let `x 0` minimize
`lam 0 ψ` over `V`, and `x (t + 1)` minimize over `V` the objective
`lam (t + 1) ψ + ∑ s ≤ t, ℓ s + ℓ' t (x t)` of optimistic FTRL whose hint is the last gradient.
Then for every `u ∈ V`,
`regret ℓ x u n ≤ lam (n - 1) ψ u - lam 0 ψ (x 0) + ‖ℓ' 0 (x 0)‖ ^ 2 / lam 0
  + ∑ t < n - 1, 2 ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2 / lam (t + 1)`,
where the norms are dual norms. The point `x t` is the one where `ℓ' (t + 1)` is queried for the
gradient variation of round `t + 1`. -/
theorem regret_le_optimistic_ftrl_gradual (ψ : E → ℝ) (ℓ : ℕ → E → ℝ)
    (ℓ' : ℕ → E → E →L[ℝ] ℝ) (x : ℕ → E) {lam : ℕ → ℝ} {m : ℝ} {u : E} {n : ℕ} (hn : 0 < n)
    (hψ : StrongConvexOn V 1 ψ) (hψ0 : ∀ a ∈ V, 0 ≤ ψ a) (hℓ : ∀ t < n, ConvexOn ℝ V (ℓ t))
    (hlam : ∀ t < n, 0 < lam t) (hlam_mono : ∀ t, t + 1 < n → lam t ≤ lam (t + 1))
    (hlam_mul : ∀ t, t + 1 < n → 8 * m ^ 2 ≤ lam t * lam (t + 1)) (hx : ∀ t < n, x t ∈ V)
    (hmin₀ : IsMinOn (fun a ↦ lam 0 * ψ a) V (x 0))
    (hmin : ∀ t, t + 1 < n → IsMinOn
      (fun a ↦ lam (t + 1) * ψ a + ∑ s ∈ range (t + 1), ℓ s a + ℓ' t (x t) a) V (x (t + 1)))
    (hg : ∀ t < n, HasSubgradientWithinAt (ℓ t) (ℓ' t (x t)) V (x t))
    (hsmooth : ∀ t, t + 1 < n →
      ‖ℓ' (t + 1) (x (t + 1)) - ℓ' (t + 1) (x t)‖ ≤ m * ‖x (t + 1) - x t‖) (hu : u ∈ V) :
    regret ℓ x u n ≤ lam (n - 1) * ψ u - lam 0 * ψ (x 0) + ‖ℓ' 0 (x 0)‖ ^ 2 / lam 0 +
      ∑ t ∈ range (n - 1), 2 * ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2 / lam (t + 1) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  rw [Nat.add_sub_cancel]
  -- the hints: `0` at round `0`, then the last gradient
  set h : ℕ → E →L[ℝ] ℝ := fun t ↦ if t = 0 then 0 else ℓ' (t - 1) (x (t - 1)) with hh
  have hh0 : h 0 = 0 := by simp [h]
  have hhs (t : ℕ) : h (t + 1) = ℓ' t (x t) := by simp [h]
  -- the plays, then the comparator as the last point
  set y := Function.update x (N + 1) u with hy
  have hyx (t : ℕ) (ht : t < N + 1) : y t = x t := Function.update_of_ne ht.ne _ _
  have h_main := regret_le_optimistic_ftrl_of_strongConvexOn (V := V)
    (fun t a ↦ lam t * ψ a) ℓ (fun t a ↦ h t a) y (fun t ↦ ℓ' t (x t) - h t) (u := u)
    (fun t ht ↦ by
      have h_sum := StrongConvexOn.fun_sum (m := fun _ ↦ 0) (t := range (t + 1)) hψ.1
        fun s hs ↦ strongConvexOn_zero.mpr (hℓ s ((mem_range.mp hs).trans_le ht))
      rw [sum_const_zero, strongConvexOn_zero] at h_sum
      simpa only [Pi.add_def, smul_eq_mul, mul_one] using
        (hψ.smul (hlam t ht).le).add_convexOn h_sum)
    (fun t ht ↦ by
      rcases ht.lt_or_eq with ht | rfl
      · exact hyx t ht ▸ hx t ht
      · simpa [hy] using hu)
    (fun t ht ↦ by
      rw [hyx t ht]
      rcases t with _ | t
      · simpa [hh0] using hmin₀
      · simpa only [hhs] using hmin t ht)
    (fun t ht ↦ by
      rw [hyx t ht]
      simpa [sub_eq_add_neg] using
        (hasSubgradientWithinAt_add_linear_iff (h := -h t)).mpr (hg t ht))
    (by simp [hy])
  rw [regret_congr hyx, hyx 0 (Nat.succ_pos N), Nat.add_sub_cancel] at h_main
  -- the increments of the regularizers are nonpositive, since `ψ ≥ 0` and `lam` is nondecreasing
  have h_inc : ∑ t ∈ range N, (lam t * ψ (y (t + 1)) - lam (t + 1) * ψ (y (t + 1))) ≤ 0 :=
    sum_nonpos fun t ht ↦ by
      have ht := mem_range.mp ht
      have hψt := hψ0 _ (hyx (t + 1) (by omega) ▸ hx (t + 1) (by omega))
      nlinarith [hlam_mono t (by omega)]
  -- the stability terms telescope
  have h_stab := sum_stability_le_of_norm_le (fun t ↦ ℓ' t (x t) - h t) y lam
    (fun t ↦ ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖) (m := m) (N := N) (fun t ht ↦ hlam t (by omega))
    (fun t ht ↦ hlam_mul t (by omega))
    (fun t ht ↦ by
      rw [hhs, hyx t (by omega), hyx (t + 1) (by omega), norm_sub_rev (x t)]
      calc ‖ℓ' (t + 1) (x (t + 1)) - ℓ' t (x t)‖
          ≤ ‖ℓ' (t + 1) (x (t + 1)) - ℓ' (t + 1) (x t)‖ + ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ m * ‖x (t + 1) - x t‖ + ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ := by
            gcongr
            exact hsmooth t (by omega))
  simp only [hh0, sub_zero] at h_stab
  linarith

/-- **Optimistic FTRL with gradual variations for smooth losses** [CYLMLJZ12; Ora,
Corollary 7.52, first bound]. `regret_le_optimistic_ftrl_gradual` for losses `ℓ t` that are
convex and `m`-smooth on `V` (`LMLExplore.SmoothOn`), with the derivatives `fderiv ℝ (ℓ t)` as
gradients. -/
theorem regret_le_optimistic_ftrl_gradual_of_smoothOn (ψ : E → ℝ) (ℓ : ℕ → E → ℝ) (x : ℕ → E)
    {lam : ℕ → ℝ} {m : ℝ≥0} {u : E} {n : ℕ} (hn : 0 < n) (hψ : StrongConvexOn V 1 ψ)
    (hψ0 : ∀ a ∈ V, 0 ≤ ψ a) (hℓ : ∀ t < n, ConvexOn ℝ V (ℓ t))
    (hsm : ∀ t < n, SmoothOn V m (ℓ t)) (hlam : ∀ t < n, 0 < lam t)
    (hlam_mono : ∀ t, t + 1 < n → lam t ≤ lam (t + 1))
    (hlam_mul : ∀ t, t + 1 < n → 8 * (m : ℝ) ^ 2 ≤ lam t * lam (t + 1)) (hx : ∀ t < n, x t ∈ V)
    (hmin₀ : IsMinOn (fun a ↦ lam 0 * ψ a) V (x 0))
    (hmin : ∀ t, t + 1 < n → IsMinOn (fun a ↦ lam (t + 1) * ψ a + ∑ s ∈ range (t + 1), ℓ s a +
      fderiv ℝ (ℓ t) (x t) a) V (x (t + 1)))
    (hu : u ∈ V) :
    regret ℓ x u n ≤ lam (n - 1) * ψ u - lam 0 * ψ (x 0) + ‖fderiv ℝ (ℓ 0) (x 0)‖ ^ 2 / lam 0 +
      ∑ t ∈ range (n - 1),
        2 * ‖fderiv ℝ (ℓ (t + 1)) (x t) - fderiv ℝ (ℓ t) (x t)‖ ^ 2 / lam (t + 1) :=
  regret_le_optimistic_ftrl_gradual ψ ℓ (fun t ↦ fderiv ℝ (ℓ t)) x hn hψ hψ0 hℓ hlam hlam_mono
    hlam_mul hx hmin₀ hmin
    (fun t ht ↦ ((hsm t ht).differentiableAt (hx t ht)).hasFDerivAt.hasSubgradientWithinAt
      (hℓ t ht) (hx t ht))
    (fun t ht ↦ (hsm (t + 1) ht).lipschitzOnWith.norm_sub_le (hx (t + 1) ht) (hx t (by omega)))
    hu

/-- The adaptive rates of Corollary 7.52 are nondecreasing: for `α ≥ 0` and `k ≤ l`,
`√(M + ∑ s < k, δ s ^ 2) / α ≤ √(M + ∑ s < l, δ s ^ 2) / α`. -/
private lemma sqrt_add_sum_div_le {δ : ℕ → ℝ} {M α : ℝ} (hα : 0 ≤ α) {k l : ℕ} (hkl : k ≤ l) :
    √(M + ∑ s ∈ range k, δ s ^ 2) / α ≤ √(M + ∑ s ∈ range l, δ s ^ 2) / α :=
  div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (add_le_add_right
    (sum_le_sum_of_subset_of_nonneg (range_mono hkl) fun _ _ _ ↦ sq_nonneg _) M)) hα

/-- **Optimistic FTRL with gradual variations and adaptive rates** [CYLMLJZ12; Ora,
Corollary 7.52, second bound]. Under the hypotheses of `regret_le_optimistic_ftrl_gradual`, with
`α > 0` and `L > 0`, let the gradients at the queried points be bounded,
`‖ℓ' t (x t)‖ ≤ L` and `‖ℓ' (t + 1) (x t)‖ ≤ L`, and let the rates be
`lam t = √(M + ∑ s < t - 1, ‖ℓ' (s + 1) (x s) - ℓ' s (x s)‖ ^ 2) / α`,
with `M = max (8 α ^ 2 m ^ 2) (4 L ^ 2)`, which only use the losses of the rounds before `t`.
Then for every `u ∈ V`,
`regret ℓ x u n ≤ (ψ u / α + 4 α) √(M + ∑ t < n - 1, ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2)
  + α L / 2`.
No bound on the diameter of `V` is needed. [Ora] states it with `(ψ u - ψ (x 0)) / α` in place of
`ψ u / α`; the first bound only gives the term `-ψ (x 0)` with the factor `lam 0`, and this bound
drops it, since `ψ ≥ 0`. -/
theorem regret_le_optimistic_ftrl_gradual_mul_sqrt (ψ : E → ℝ) (ℓ : ℕ → E → ℝ)
    (ℓ' : ℕ → E → E →L[ℝ] ℝ) (x : ℕ → E) {lam : ℕ → ℝ} {m α L : ℝ} {u : E} {n : ℕ}
    (hn : 0 < n) (hα : 0 < α) (hL : 0 < L) (hψ : StrongConvexOn V 1 ψ)
    (hψ0 : ∀ a ∈ V, 0 ≤ ψ a) (hℓ : ∀ t < n, ConvexOn ℝ V (ℓ t))
    (hlam : ∀ t < n, lam t = √(max (8 * α ^ 2 * m ^ 2) (4 * L ^ 2) +
      ∑ s ∈ range (t - 1), ‖ℓ' (s + 1) (x s) - ℓ' s (x s)‖ ^ 2) / α)
    (hx : ∀ t < n, x t ∈ V) (hmin₀ : IsMinOn (fun a ↦ lam 0 * ψ a) V (x 0))
    (hmin : ∀ t, t + 1 < n → IsMinOn
      (fun a ↦ lam (t + 1) * ψ a + ∑ s ∈ range (t + 1), ℓ s a + ℓ' t (x t) a) V (x (t + 1)))
    (hg : ∀ t < n, HasSubgradientWithinAt (ℓ t) (ℓ' t (x t)) V (x t))
    (hsmooth : ∀ t, t + 1 < n →
      ‖ℓ' (t + 1) (x (t + 1)) - ℓ' (t + 1) (x t)‖ ≤ m * ‖x (t + 1) - x t‖)
    (hL₀ : ∀ t < n, ‖ℓ' t (x t)‖ ≤ L) (hL₁ : ∀ t, t + 1 < n → ‖ℓ' (t + 1) (x t)‖ ≤ L)
    (hu : u ∈ V) :
    regret ℓ x u n ≤ (ψ u / α + 4 * α) * √(max (8 * α ^ 2 * m ^ 2) (4 * L ^ 2) +
      ∑ t ∈ range (n - 1), ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2) + α * L / 2 := by
  set M := max (8 * α ^ 2 * m ^ 2) (4 * L ^ 2) with hM
  have hM4 : 4 * L ^ 2 ≤ M := le_max_right _ _
  have hM8 : 8 * α ^ 2 * m ^ 2 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by positivity
  have h2L : 2 * L ≤ √M := by
    rw [show 2 * L = √((2 * L) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by linarith)
  -- the rates are nondecreasing, at least `√M / α`, hence `8 m ^ 2 ≤ lam t * lam (t + 1)`
  have hlam_ge (t : ℕ) (ht : t < n) : √M / α ≤ lam t := by
    rw [hlam t ht]
    simpa using sqrt_add_sum_div_le (δ := fun s ↦ ‖ℓ' (s + 1) (x s) - ℓ' s (x s)‖) (M := M)
      hα.le (Nat.zero_le (t - 1))
  have hlam_pos (t : ℕ) (ht : t < n) : 0 < lam t :=
    lt_of_lt_of_le (by positivity) (hlam_ge t ht)
  have hlam_mono (t : ℕ) (ht : t + 1 < n) : lam t ≤ lam (t + 1) := by
    rw [hlam t (by omega), hlam (t + 1) ht]
    exact sqrt_add_sum_div_le hα.le (by omega)
  have hlam_mul (t : ℕ) (ht : t + 1 < n) : 8 * m ^ 2 ≤ lam t * lam (t + 1) := by
    have h1 := hlam_ge t (by omega)
    have h2 := hlam_ge (t + 1) ht
    have hsq : (√M / α) ^ 2 = M / α ^ 2 := by rw [div_pow, Real.sq_sqrt hMpos.le]
    have h8 : 8 * m ^ 2 ≤ M / α ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith [div_pos (Real.sqrt_pos.mpr hMpos) hα]
  have h := regret_le_optimistic_ftrl_gradual ψ ℓ ℓ' x hn hψ hψ0 hℓ hlam_pos hlam_mono hlam_mul
    hx hmin₀ hmin hg hsmooth hu
  set R := √(M + ∑ t ∈ range (n - 1), ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2) with hR
  -- the regularizer terms: `lam (n - 1) ψ u ≤ ψ u / α * R` and `lam 0 ψ (x 0) ≥ 0`
  have hψu := hψ0 u hu
  have h_reg : lam (n - 1) * ψ u ≤ ψ u / α * R := by
    have h1 : lam (n - 1) ≤ R / α := by
      rw [hlam (n - 1) (by omega)]
      exact sqrt_add_sum_div_le hα.le (by omega)
    calc lam (n - 1) * ψ u ≤ R / α * ψ u := by gcongr
      _ = ψ u / α * R := by ring
  have h_x0 : 0 ≤ lam 0 * ψ (x 0) := mul_nonneg (hlam_pos 0 hn).le (hψ0 _ (hx 0 hn))
  -- the first round: `‖ℓ' 0 (x 0)‖ ^ 2 / lam 0 ≤ α L / 2`, since `lam 0 ≥ 2 L / α`
  have h_first : ‖ℓ' 0 (x 0)‖ ^ 2 / lam 0 ≤ α * L / 2 := by
    have h2L' : 2 * L / α ≤ lam 0 :=
      (div_le_div_of_nonneg_right h2L hα.le).trans (hlam_ge 0 hn)
    have hL0 := pow_le_pow_left₀ (norm_nonneg _) (hL₀ 0 hn) 2
    rw [div_le_iff₀ (hlam_pos 0 hn)]
    have h_eq : α * L / 2 * (2 * L / α) = L ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2L' (by positivity : (0 : ℝ) ≤ α * L / 2)]
  -- the gradient variations: `∑ 2 δ t ^ 2 / lam (t + 1) ≤ 4 α √(∑ δ t ^ 2) ≤ 4 α R`
  have h_var : ∑ t ∈ range (n - 1), 2 * ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2 / lam (t + 1) ≤
      4 * α * √(∑ t ∈ range (n - 1), ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2) := by
    -- `δ t ≤ ‖ℓ' (t + 1) (x t)‖ + ‖ℓ' t (x t)‖ ≤ 2 L`, so `δ t ^ 2 ≤ M`
    have hδ (t : ℕ) (ht : t < n - 1) : ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2 ≤ M := by
      have h_norm : ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ≤ 2 * L := by
        linarith [norm_sub_le (ℓ' (t + 1) (x t)) (ℓ' t (x t)), hL₁ t (by omega),
          hL₀ t (by omega)]
      have := pow_le_pow_left₀ (norm_nonneg _) h_norm 2
      linarith
    calc _ = 2 * α * ∑ t ∈ range (n - 1), ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2 /
          √(M + ∑ s ∈ range t, ‖ℓ' (s + 1) (x s) - ℓ' s (x s)‖ ^ 2) := by
          rw [mul_sum]
          refine sum_congr rfl fun t ht ↦ ?_
          rw [hlam (t + 1) (by have := mem_range.mp ht; omega), Nat.add_sub_cancel,
            div_div_eq_mul_div]
          ring
      _ ≤ 2 * α * (2 * √(∑ t ∈ range (n - 1), ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2)) := by
          gcongr
          exact Real.sum_div_sqrt_add_le_two_mul_sqrt (fun _ _ ↦ sq_nonneg _) hδ
      _ = 4 * α * √(∑ t ∈ range (n - 1), ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2) := by ring
  have h_sqrt : √(∑ t ∈ range (n - 1), ‖ℓ' (t + 1) (x t) - ℓ' t (x t)‖ ^ 2) ≤ R :=
    Real.sqrt_le_sqrt (by linarith)
  have h_sqrt' := mul_le_mul_of_nonneg_left h_sqrt (by positivity : (0 : ℝ) ≤ 4 * α)
  nlinarith

/-- **Optimistic FTRL with gradual variations and adaptive rates, for smooth losses**
[CYLMLJZ12; Ora, Corollary 7.52, second bound]. `regret_le_optimistic_ftrl_gradual_mul_sqrt`
for losses `ℓ t` that are convex and `m`-smooth on `V` (`LMLExplore.SmoothOn`), with gradients
`fderiv ℝ (ℓ t)` of norm at most `L` on `V`. -/
theorem regret_le_optimistic_ftrl_gradual_mul_sqrt_of_smoothOn (ψ : E → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) {lam : ℕ → ℝ} {m : ℝ≥0} {α L : ℝ} {u : E} {n : ℕ} (hn : 0 < n) (hα : 0 < α)
    (hL : 0 < L) (hψ : StrongConvexOn V 1 ψ) (hψ0 : ∀ a ∈ V, 0 ≤ ψ a)
    (hℓ : ∀ t < n, ConvexOn ℝ V (ℓ t)) (hsm : ∀ t < n, SmoothOn V m (ℓ t))
    (hL_le : ∀ t < n, ∀ a ∈ V, ‖fderiv ℝ (ℓ t) a‖ ≤ L)
    (hlam : ∀ t < n, lam t = √(max (8 * α ^ 2 * (m : ℝ) ^ 2) (4 * L ^ 2) +
      ∑ s ∈ range (t - 1), ‖fderiv ℝ (ℓ (s + 1)) (x s) - fderiv ℝ (ℓ s) (x s)‖ ^ 2) / α)
    (hx : ∀ t < n, x t ∈ V) (hmin₀ : IsMinOn (fun a ↦ lam 0 * ψ a) V (x 0))
    (hmin : ∀ t, t + 1 < n → IsMinOn (fun a ↦ lam (t + 1) * ψ a + ∑ s ∈ range (t + 1), ℓ s a +
      fderiv ℝ (ℓ t) (x t) a) V (x (t + 1)))
    (hu : u ∈ V) :
    regret ℓ x u n ≤ (ψ u / α + 4 * α) * √(max (8 * α ^ 2 * (m : ℝ) ^ 2) (4 * L ^ 2) +
      ∑ t ∈ range (n - 1), ‖fderiv ℝ (ℓ (t + 1)) (x t) - fderiv ℝ (ℓ t) (x t)‖ ^ 2) +
        α * L / 2 :=
  regret_le_optimistic_ftrl_gradual_mul_sqrt ψ ℓ (fun t ↦ fderiv ℝ (ℓ t)) x hn hα hL hψ hψ0 hℓ
    hlam hx hmin₀ hmin
    (fun t ht ↦ ((hsm t ht).differentiableAt (hx t ht)).hasFDerivAt.hasSubgradientWithinAt
      (hℓ t ht) (hx t ht))
    (fun t ht ↦ (hsm (t + 1) ht).lipschitzOnWith.norm_sub_le (hx (t + 1) ht) (hx t (by omega)))
    (fun t ht ↦ hL_le t ht _ (hx t ht)) (fun t ht ↦ hL_le (t + 1) ht _ (hx t (by omega))) hu

end NormedSpace

end LMLExplore.OnlineLearning
