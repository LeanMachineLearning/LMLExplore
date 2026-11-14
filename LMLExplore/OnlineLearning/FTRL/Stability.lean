/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Strong
public import LMLExplore.Analysis.InnerProductSpace.InvNormSq
public import LMLExplore.OnlineLearning.FTRL.Equality

/-!
# Stability of follow the regularized leader without derivatives

Follow the regularized leader (FTRL) on a set `V` of a real normed space `E`, with regularizers
and losses `ψ ℓ : ℕ → E → ℝ`, plays at round `t` a minimizer `x t` over `V` of the objective
`F t = ψ t + ∑ s < t, ℓ s`. By the FTRL equality (`regret_le_ftrl`), its regret is controlled by
the stability terms `F t (x t) - F (t + 1) (x (t + 1)) + ℓ t (x t)`. This file bounds them through
strong convexity, with subgradients within `V` in the sense of LML's `HasSubgradientWithinAt`
[Ora, Lemmas 7.5 and 7.7]:

* if `g` is a subgradient of `ℓ t` within `V` at `x t` and `F t + ℓ t` is `λ`-strongly convex on
  `V`, then for every `z ∈ V`, `F t (x t) + ℓ t (x t) - F (t + 1) z` is at most
  `g (x t - z) - λ / 2 * ‖x t - z‖ ^ 2 + ψ t z - ψ (t + 1) z`, hence at most
  `‖g‖ ^ 2 / (2 λ) + ψ t z - ψ (t + 1) z`;
* the same holds with any divergence `D z` in place of `λ / 2 * ‖x t - z‖ ^ 2` when `F t + ℓ t`
  lies above each of its subgradient planes at `x t` by `D` (relative strong convexity), and, in a
  real inner product space, the quadratic divergence `⟪S (z - x t), z - x t⟫ / 2` of a positive
  invertible operator `S` gives the bound `⟪v, S⁻¹ v⟫ / 2` for the loss gradient `v`;
* for proximal regularizers, those for which `x t` also minimizes `ψ (t + 1) - ψ t` on `V`, the
  strong convexity of `F (t + 1)` gives the bound with `ψ t (x t) - ψ (t + 1) (x t)`.

Neither the regularizers nor the losses need to be differentiable, the regularizers need not be
monotone in `t`, and only `F t + ℓ t` (not `ψ t`) must be strongly convex. Summed through the FTRL
equality, the stability bounds give the regret of FTRL for convex losses on sets that need not be
bounded [Ora, Corollary 7.6]: when the plays minimize their objectives over `V`, `g t` is a
subgradient of `ℓ t` within `V` at `x t` and `F t + ℓ t` is `λ t`-strongly convex on `V` with
`λ t > 0`, for every comparator `u` with `F n (x n) ≤ F n u` (for instance `u ∈ V` when `x n`
minimizes `F n` over `V`),
`regret ≤ ψ n u - ψ 0 (x 0) + ∑ t < n, ‖g t‖ ^ 2 / (2 λ t)
  + ∑ t < n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`.

## Main statements

* `ftrl_stability_le_of_forall_hasSubgradientWithinAt`: the stability bound with a divergence
  (relative strong convexity).
* `ftrl_stability_le_of_strongConvexOn`, `ftrl_stability_le_norm_sq_div_of_strongConvexOn`:
  [Ora, Lemma 7.5], the two forms of the stability bound for a strongly convex `F t + ℓ t`.
* `ftrl_stability_le_inner_ringInverse`: the quadratic case, with the bound `⟪v, S⁻¹ v⟫ / 2`.
* `ftrl_stability_le_of_isMinOn_sub_of_strongConvexOn`,
  `ftrl_stability_le_norm_sq_div_of_isMinOn_sub_of_strongConvexOn`: [Ora, Lemma 7.7] proximal
  regularizers.
* `regret_le_ftrl_of_strongConvexOn`: [Ora, Corollary 7.6] the regret of FTRL for convex losses,
  with arbitrary regularizers and strong convexity moduli.
* `regret_le_ftrl_of_strongConvexOn_div`: [Ora, Corollary 7.6] its case of the regularizers
  `F / η t`, for an `m`-strongly convex `F`, convex losses and arbitrary positive learning rates,
  keeping the increments `(1 / η t - 1 / η (t + 1)) * F (x (t + 1))` of the regularizers.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Lemmas 7.5 and 7.7, Corollary 7.6.
-/
public section

open Finset
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} {ψ ℓ : ℕ → E → ℝ}
  {x : ℕ → E} {t : ℕ} {z : E} {g : E →L[ℝ] ℝ} {lam : ℝ}

/-- The quadratic case of `apply_sub_sub_div_le_of_mul_norm_sq_le`:
`g (a - b) - lam / 2 * ‖a - b‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 lam)` for `lam > 0`. -/
private lemma apply_sub_sub_mul_norm_sq_le (hlam : 0 < lam) (g : E →L[ℝ] ℝ) (a b : E) :
    g (a - b) - lam / 2 * ‖a - b‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * lam) := by
  have h := apply_sub_sub_div_le_of_mul_norm_sq_le hlam one_pos g
    (le_of_eq (by rw [norm_sub_rev]) : lam / 2 * ‖b - a‖ ^ 2 ≤ lam / 2 * ‖a - b‖ ^ 2)
  rwa [div_one, one_div_mul_eq_div] at h

/-- **Stability of FTRL with a divergence** (relative strong convexity) [Ora, Lemma 7.5 and
Remark 7.28]. Let `x t` minimize the objective `F t = ψ t + ∑ s < t, ℓ s` over `V`, let `g` be a
subgradient of the loss `ℓ t` within `V` at `x t`, and let `F t + ℓ t` lie above each of its
subgradient planes within `V` at `x t` by the divergence `D`: for every subgradient `h` of
`F t + ℓ t` within `V` at `x t` and every `z ∈ V`,
`(F t + ℓ t) (x t) + h (z - x t) + D z ≤ (F t + ℓ t) z`. Then for every `z ∈ V`,
`F t (x t) - F (t + 1) z + ℓ t (x t) ≤ g (x t - z) - D z + ψ t z - ψ (t + 1) z`.
Neither `ψ t` nor `ℓ t` needs to be differentiable or convex. -/
theorem ftrl_stability_le_of_forall_hasSubgradientWithinAt {D : E → ℝ}
    (hmin : IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : HasSubgradientWithinAt (ℓ t) g V (x t))
    (hD : ∀ h : E →L[ℝ] ℝ,
      HasSubgradientWithinAt (fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a) h V (x t) →
      ∀ z ∈ V, ψ t (x t) + ∑ s ∈ range (t + 1), ℓ s (x t) + h (z - x t) + D z ≤
        ψ t z + ∑ s ∈ range (t + 1), ℓ s z)
    (hz : z ∈ V) :
    (ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) - (ψ (t + 1) z + ∑ s ∈ range (t + 1), ℓ s z) +
        ℓ t (x t) ≤
      g (x t - z) - D z + ψ t z - ψ (t + 1) z := by
  -- `x t` minimizes `F t` on `V`, so a subgradient of `ℓ t` is a subgradient of `F t + ℓ t`
  have hΦ : HasSubgradientWithinAt (fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a) g V (x t) := by
    have h := HasSubgradientWithinAt.fun_add_isMinOn hmin hg
    simp only [sum_range_succ, ← add_assoc]
    exact h
  have h := hD g hΦ z hz
  rw [show z - x t = -(x t - z) by abel, map_neg] at h
  simp only [sum_range_succ] at h ⊢
  linarith

/-- **Stability of FTRL** [Ora, Lemma 7.5, first inequality]. Let `x t ∈ V` minimize the objective
`F t = ψ t + ∑ s < t, ℓ s` over `V`, let `g` be a subgradient of the loss `ℓ t` within `V` at
`x t`, and let `F t + ℓ t` be `lam`-strongly convex on `V`. Then for every `z ∈ V`,
`F t (x t) - F (t + 1) z + ℓ t (x t) ≤ g (x t - z) - lam / 2 * ‖x t - z‖ ^ 2 + ψ t z - ψ (t + 1) z`.
No derivative of `ψ t` is needed, and `ψ t` alone need not be strongly convex. -/
theorem ftrl_stability_le_of_strongConvexOn
    (hmin : IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : HasSubgradientWithinAt (ℓ t) g V (x t))
    (hΦ : StrongConvexOn V lam fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a) (hx : x t ∈ V)
    (hz : z ∈ V) :
    (ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) - (ψ (t + 1) z + ∑ s ∈ range (t + 1), ℓ s z) +
        ℓ t (x t) ≤
      g (x t - z) - lam / 2 * ‖x t - z‖ ^ 2 + ψ t z - ψ (t + 1) z := by
  refine ftrl_stability_le_of_forall_hasSubgradientWithinAt (D := fun z ↦ lam / 2 * ‖x t - z‖ ^ 2)
    hmin hg (fun h hh z hz ↦ ?_) hz
  simpa only [norm_sub_rev (x t) z] using hΦ.add_add_le_of_hasSubgradientWithinAt hx hz hh

/-- **Stability of FTRL** [Ora, Lemma 7.5, second inequality]. Under the assumptions of
`ftrl_stability_le_of_strongConvexOn` with `lam > 0`, for every `z ∈ V`,
`F t (x t) - F (t + 1) z + ℓ t (x t) ≤ ‖g‖ ^ 2 / (2 lam) + ψ t z - ψ (t + 1) z`,
where `‖g‖` is the operator norm, the dual norm of the norm of `E`. -/
theorem ftrl_stability_le_norm_sq_div_of_strongConvexOn (hlam : 0 < lam)
    (hmin : IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : HasSubgradientWithinAt (ℓ t) g V (x t))
    (hΦ : StrongConvexOn V lam fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a) (hx : x t ∈ V)
    (hz : z ∈ V) :
    (ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) - (ψ (t + 1) z + ∑ s ∈ range (t + 1), ℓ s z) +
        ℓ t (x t) ≤
      ‖g‖ ^ 2 / (2 * lam) + ψ t z - ψ (t + 1) z := by
  have h := ftrl_stability_le_of_strongConvexOn hmin hg hΦ hx hz
  linarith [apply_sub_sub_mul_norm_sq_le hlam g (x t) z]

/-- **Stability of FTRL with proximal regularizers** [Ora, Lemma 7.7, first inequality]. Let
`x t ∈ V` minimize over `V` both the objective `F t = ψ t + ∑ s < t, ℓ s` and the increment
`ψ (t + 1) - ψ t` of the regularizers, let `g` be a subgradient of the loss `ℓ t` within `V` at
`x t`, and let `F (t + 1)` be `lam`-strongly convex on `V`. Then for every `z ∈ V`,
`F t (x t) - F (t + 1) z + ℓ t (x t)
  ≤ g (x t - z) - lam / 2 * ‖x t - z‖ ^ 2 + ψ t (x t) - ψ (t + 1) (x t)`.
A constant regularizer is proximal, and then this is `ftrl_stability_le_of_strongConvexOn`
[Ora, Remark 7.8]. -/
theorem ftrl_stability_le_of_isMinOn_sub_of_strongConvexOn
    (hmin : IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hprox : IsMinOn (fun a ↦ ψ (t + 1) a - ψ t a) V (x t))
    (hg : HasSubgradientWithinAt (ℓ t) g V (x t))
    (hF : StrongConvexOn V lam fun a ↦ ψ (t + 1) a + ∑ s ∈ range (t + 1), ℓ s a) (hx : x t ∈ V)
    (hz : z ∈ V) :
    (ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) - (ψ (t + 1) z + ∑ s ∈ range (t + 1), ℓ s z) +
        ℓ t (x t) ≤
      g (x t - z) - lam / 2 * ‖x t - z‖ ^ 2 + ψ t (x t) - ψ (t + 1) (x t) := by
  -- `x t` minimizes `F t + (ψ (t + 1) - ψ t)` on `V`, so a subgradient of `ℓ t` is a subgradient
  -- of `F t + (ψ (t + 1) - ψ t) + ℓ t = F (t + 1)`
  have hF' : HasSubgradientWithinAt (fun a ↦ ψ (t + 1) a + ∑ s ∈ range (t + 1), ℓ s a) g V
      (x t) := by
    have h := HasSubgradientWithinAt.fun_add_isMinOn (hmin.add hprox) hg
    convert h using 2 with a
    rw [sum_range_succ]
    ring
  have h := hF.add_add_le_of_hasSubgradientWithinAt hx hz hF'
  rw [show z - x t = -(x t - z) by abel, map_neg, norm_neg] at h
  simp only [sum_range_succ] at h ⊢
  linarith

/-- **Stability of FTRL with proximal regularizers** [Ora, Lemma 7.7, second inequality]. Under
the assumptions of `ftrl_stability_le_of_isMinOn_sub_of_strongConvexOn` with `lam > 0`, for every
`z ∈ V`,
`F t (x t) - F (t + 1) z + ℓ t (x t) ≤ ‖g‖ ^ 2 / (2 lam) + ψ t (x t) - ψ (t + 1) (x t)`,
where `‖g‖` is the operator norm, the dual norm of the norm of `E`. -/
theorem ftrl_stability_le_norm_sq_div_of_isMinOn_sub_of_strongConvexOn (hlam : 0 < lam)
    (hmin : IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hprox : IsMinOn (fun a ↦ ψ (t + 1) a - ψ t a) V (x t))
    (hg : HasSubgradientWithinAt (ℓ t) g V (x t))
    (hF : StrongConvexOn V lam fun a ↦ ψ (t + 1) a + ∑ s ∈ range (t + 1), ℓ s a) (hx : x t ∈ V)
    (hz : z ∈ V) :
    (ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) - (ψ (t + 1) z + ∑ s ∈ range (t + 1), ℓ s z) +
        ℓ t (x t) ≤
      ‖g‖ ^ 2 / (2 * lam) + ψ t (x t) - ψ (t + 1) (x t) := by
  have h := ftrl_stability_le_of_isMinOn_sub_of_strongConvexOn hmin hprox hg hF hx hz
  linarith [apply_sub_sub_mul_norm_sq_le hlam g (x t) z]

/-- **The regret of FTRL for convex losses** [Ora, Corollary 7.6]. Let `x t ∈ V`, for `t ≤ n`,
and let `x t`, for `t < n`, minimize over `V` the objective `F t = ψ t + ∑ s < t, ℓ s`. Let
`g t` be a subgradient of `ℓ t` within `V` at `x t` and let `F t + ℓ t` be `lam t`-strongly convex
on `V`, with `lam t > 0`, for `t < n`. If the last point does at least as well as the comparator
`u` on the last objective, `F n (x n) ≤ F n u` (for instance if `x n` minimizes `F n` over a set
containing `u`), then
`regret ℓ x u n ≤ ψ n u - ψ 0 (x 0) + ∑ t < n, ‖g t‖ ^ 2 / (2 lam t)
  + ∑ t < n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1)))`,
where `‖g t‖` is the dual norm. The regularizers need not be differentiable, nor monotone in `t`,
and `V` need not be bounded. -/
theorem regret_le_ftrl_of_strongConvexOn (ψ ℓ : ℕ → E → ℝ) (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ)
    {lam : ℕ → ℝ} {u : E} {n : ℕ} (hlam : ∀ t < n, 0 < lam t)
    (hΦ : ∀ t < n, StrongConvexOn V (lam t) fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a)
    (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : ∀ t < n, HasSubgradientWithinAt (ℓ t) (g t) V (x t))
    (hxn : ψ n (x n) + ∑ s ∈ range n, ℓ s (x n) ≤ ψ n u + ∑ s ∈ range n, ℓ s u) :
    regret ℓ x u n ≤ ψ n u - ψ 0 (x 0) + ∑ t ∈ range n, ‖g t‖ ^ 2 / (2 * lam t) +
      ∑ t ∈ range n, (ψ t (x (t + 1)) - ψ (t + 1) (x (t + 1))) := by
  refine (regret_le_ftrl ψ ℓ x x hxn).trans ?_
  rw [add_assoc, ← sum_add_distrib]
  -- bound each stability term, with the comparison point `x (t + 1)`
  refine add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_)
  have ht := mem_range.mp ht
  have h := ftrl_stability_le_norm_sq_div_of_strongConvexOn (hlam t ht) (hmin t ht) (hg t ht)
    (hΦ t ht) (hx t ht.le) (hx (t + 1) ht)
  linarith

/-- **The regret of FTRL with the regularizers `F / η t`** [Ora, Corollary 7.6]. Let `F` be
`m`-strongly convex on `V`, with `m > 0`, let the losses `ℓ t` be convex on `V` and the learning
rates `η t` be positive for `t < n`. Let `x t ∈ V`, for `t ≤ n`, and let `x t`, for `t < n`,
minimize over `V` the objective `F / η t + ∑ s < t, ℓ s`, and `g t` be a subgradient of `ℓ t`
within `V` at `x t`. If `F (x n) / η n + ∑ s < n, ℓ s (x n) ≤ F u / η n + ∑ s < n, ℓ s u`, then
`regret ℓ x u n ≤ F u / η n - F (x 0) / η 0 + ∑ t < n, η t / (2 m) * ‖g t‖ ^ 2
  + ∑ t < n, (1 / η t - 1 / η (t + 1)) * F (x (t + 1))`,
where `‖g t‖` is the dual norm. The learning rates need not be monotone, and the increments of
the regularizers are kept. [Ora] states it for the regularizers `(F - min F) / η t` with
nonincreasing rates and `η n = η (n - 1)`, where the increments are nonpositive and are dropped.
-/
theorem regret_le_ftrl_of_strongConvexOn_div {F : E → ℝ} {m : ℝ} (hF : StrongConvexOn V m F)
    (hm : 0 < m) (ℓ : ℕ → E → ℝ) (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) {η : ℕ → ℝ} {u : E} {n : ℕ}
    (hη : ∀ t < n, 0 < η t) (hℓ : ∀ t < n, ConvexOn ℝ V (ℓ t)) (hx : ∀ t ≤ n, x t ∈ V)
    (hmin : ∀ t < n, IsMinOn (fun a ↦ F a / η t + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : ∀ t < n, HasSubgradientWithinAt (ℓ t) (g t) V (x t))
    (hxn : F (x n) / η n + ∑ s ∈ range n, ℓ s (x n) ≤ F u / η n + ∑ s ∈ range n, ℓ s u) :
    regret ℓ x u n ≤ F u / η n - F (x 0) / η 0 + ∑ t ∈ range n, η t / (2 * m) * ‖g t‖ ^ 2 +
      ∑ t ∈ range n, (1 / η t - 1 / η (t + 1)) * F (x (t + 1)) := by
  -- `F / η t + ∑ s ≤ t, ℓ s` is `m / η t`-strongly convex on `V`
  have hΦ (t : ℕ) (ht : t < n) :
      StrongConvexOn V ((η t)⁻¹ * m) fun a ↦ F a / η t + ∑ s ∈ range (t + 1), ℓ s a := by
    have h_sum : ConvexOn ℝ V (∑ s ∈ range (t + 1), ℓ s) :=
      sum_induction _ (ConvexOn ℝ V) (fun _ _ ↦ ConvexOn.add) (convexOn_const 0 hF.1)
        fun s hs ↦ hℓ s ((mem_range.mp hs).trans_le ht)
    have h := (hF.smul (inv_nonneg.mpr (hη t ht).le)).add_convexOn h_sum
    convert h using 1
    ext a
    simp [div_eq_inv_mul]
  have h := regret_le_ftrl_of_strongConvexOn (fun t a ↦ F a / η t) ℓ x g
    (fun t ht ↦ mul_pos (inv_pos.mpr (hη t ht)) hm) hΦ hx hmin hg hxn
  -- rewrite the stability and penalty terms of the regularizers `F / η t`
  have h_stab : ∀ t ∈ range n, ‖g t‖ ^ 2 / (2 * ((η t)⁻¹ * m)) = η t / (2 * m) * ‖g t‖ ^ 2 := by
    intro t ht
    have := (hη t (mem_range.mp ht)).ne'
    field_simp
  have h_inc : ∀ t ∈ range n, F (x (t + 1)) / η t - F (x (t + 1)) / η (t + 1) =
      (1 / η t - 1 / η (t + 1)) * F (x (t + 1)) := fun _ _ ↦ by ring
  rwa [sum_congr rfl h_stab, sum_congr rfl h_inc] at h

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {V : Set E} {ψ ℓ : ℕ → E → ℝ}
  {x : ℕ → E} {t : ℕ} {z : E}

/-- **Stability of FTRL with a quadratic divergence** [Ora, Lemma 7.5 and Remark 7.28]. In a real
inner product space, let `x t` minimize the objective `F t = ψ t + ∑ s < t, ℓ s` over `V`, let
`⟪v, ·⟫` be a subgradient of the loss `ℓ t` within `V` at `x t`, and let `S` be a positive
invertible operator such that `F t + ℓ t` lies above each of its subgradient planes within `V` at
`x t` by `⟪S (z - x t), z - x t⟫ / 2`. Then for every `z ∈ V`,
`F t (x t) - F (t + 1) z + ℓ t (x t) ≤ ⟪v, S⁻¹ v⟫ / 2 + ψ t z - ψ (t + 1) z`. -/
theorem ftrl_stability_le_inner_ringInverse {S : E →L[ℝ] E} (hS : S.IsPositive) (hSu : IsUnit S)
    {v : E} (hmin : IsMinOn (fun a ↦ ψ t a + ∑ s ∈ range t, ℓ s a) V (x t))
    (hg : HasSubgradientWithinAt (ℓ t) (innerSL ℝ v) V (x t))
    (hD : ∀ h : E →L[ℝ] ℝ,
      HasSubgradientWithinAt (fun a ↦ ψ t a + ∑ s ∈ range (t + 1), ℓ s a) h V (x t) →
      ∀ z ∈ V, ψ t (x t) + ∑ s ∈ range (t + 1), ℓ s (x t) + h (z - x t) +
        ⟪S (z - x t), z - x t⟫ / 2 ≤ ψ t z + ∑ s ∈ range (t + 1), ℓ s z)
    (hz : z ∈ V) :
    (ψ t (x t) + ∑ s ∈ range t, ℓ s (x t)) - (ψ (t + 1) z + ∑ s ∈ range (t + 1), ℓ s z) +
        ℓ t (x t) ≤
      ⟪v, Ring.inverse S v⟫ / 2 + ψ t z - ψ (t + 1) z := by
  have h := ftrl_stability_le_of_forall_hasSubgradientWithinAt
    (D := fun z ↦ ⟪S (z - x t), z - x t⟫ / 2) hmin hg hD hz
  -- `2 ⟪v, w⟫ - ⟪w, S w⟫ ≤ ⟪v, S⁻¹ v⟫` at `w = x t - z`, the variational form of `‖v‖²_{S⁻¹}`
  have h_inv := ofReal_le_invNormSq (S : E →ₗ[ℝ] E) (x t - z) v
  have h_nonneg : 0 ≤ ⟪v, Ring.inverse S v⟫ := by
    have h := hS.inner_nonneg_left (Ring.inverse S v)
    rwa [ContinuousLinearMap.apply_ringInverse_apply hSu] at h
  rw [invNormSq_eq_ofReal_inner_ringInverse hS hSu, ENNReal.ofReal_le_ofReal_iff h_nonneg] at h_inv
  have h_neg : ⟪S (z - x t), z - x t⟫ = ⟪x t - z, S (x t - z)⟫ := by
    rw [show z - x t = -(x t - z) by abel, map_neg, inner_neg_neg, real_inner_comm]
  simp only [innerSL_apply_apply, ContinuousLinearMap.coe_coe, h_neg] at h h_inv
  linarith

end InnerProductSpace

end LMLExplore.OnlineLearning
