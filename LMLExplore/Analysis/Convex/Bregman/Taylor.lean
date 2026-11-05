/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Second-order forms of the Bregman divergence

For a function `f` on a real normed space `E` with derivative `f'` and second derivative
`f''`, the Bregman divergence `D_f(x, y) = f x - f y - f' y (x - y)` is the remainder of the
first-order Taylor expansion of `f` at `y`. Taylor's theorem with the Lagrange remainder along
the segment `[x, y]` gives it the exact form `D_f(x, y) = f'' z (x - y) (x - y) / 2` for some
`z ∈ [x, y]` [LS, Theorem 26.12], the squared local norm of `x - y` for the Hessian at `z`.

This exact form is how the stability terms `y (x - x') - D_f(x', x) / η` in the regret bounds of
mirror descent and follow the regularized leader are controlled through the Hessian of the
potential [LS, Theorem 26.13]: the term is at most `η / 2` times the squared dual local norm of
the loss at a point of the segment. In a normed space the dual local norm of a linear functional
`u` for the quadratic form `H` is not written with an inverse: any `c ≥ 0` with
`u v ^ 2 ≤ c * H v v` bounds it. With `H v v = ⟪v, T v⟫` for a positive invertible operator `T`
on an inner product space, `c = ⟪u, T⁻¹ u⟫` is such a bound, by
`ContinuousLinearMap.IsPositive.abs_inner_le_sqrt_mul_sqrt_ringInverse`.

## Main statements

* `Convex.exists_mem_segment_bregDiv_eq`: [LS, Theorem 26.12], first part. If `f` has
  derivative `f'` and `f'` has derivative `f''` within a convex set `s` containing `x` and `y`,
  then `D_f(x, y) = f'' z (x - y) (x - y) / 2` for some `z ∈ [x, y]`.
* `LMLExplore.apply_sub_sub_bregDiv_div_le_of_bregDiv_eq`: [LS, Theorem 26.13]. If
  `D_f(x, y) = H (x - y) (x - y) / 2` with `D_f(x, y) ≥ 0`, then
  `u (x - y) - D_f(x, y) / η ≤ η / 2 * c` for every `η > 0` and `c ≥ 0` with
  `u (x - y) ^ 2 ≤ c * H (x - y) (x - y)`.
* `ConvexOn.exists_mem_segment_apply_sub_sub_bregDiv_div_le`: the two combined for a convex
  function, with `z ∈ [x, y]` chosen independently of `u`, `c` and `η`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 26.4.
-/

public section

open Set

open scoped Bregman Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ}
  {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} {x y : E}

/-- **Taylor form of the Bregman divergence** [LS, Theorem 26.12]. Let `f` have derivative
`f' z` and `f'` have derivative `f'' z` within a convex set `s`, at every `z ∈ s`. Then for
`x, y ∈ s` there is a point `z` of the segment `[x, y]` such that
`D_f(x, y) = f'' z (x - y) (x - y) / 2`. [LS] assumes `f` convex, which the identity does not
need. -/
theorem Convex.exists_mem_segment_bregDiv_eq (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hf' : ∀ z ∈ s, HasFDerivWithinAt f' (f'' z) s z) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ z ∈ segment ℝ x y, D_[f](x, y, f' y) = f'' z (x - y) (x - y) / 2 := by
  -- Restrict `f` to the line `ℓ t = y + t • (x - y)`, with `ℓ 0 = y` and `ℓ 1 = x`.
  set v := x - y with hv
  set ℓ : ℝ → E := fun t ↦ y + t • v with hℓ
  have hmaps : MapsTo ℓ (Icc 0 1) s := by
    intro t ht
    refine hs.segment_subset hy hx ?_
    rw [segment_eq_image']
    exact ⟨t, ht, rfl⟩
  have hℓ' (t : ℝ) : HasDerivWithinAt ℓ v (Icc 0 1) t := by
    have h := ((hasDerivAt_id' t).smul_const v).const_add y
    rw [one_smul] at h
    exact h.hasDerivWithinAt
  -- `g = f ∘ ℓ` has derivative `g' t = f' (ℓ t) v` and second derivative `f'' (ℓ t) v v`.
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun t ↦ f (ℓ t)) (f' (ℓ t) v) (Icc 0 1) t :=
    HasFDerivWithinAt.comp_hasDerivWithinAt t (hf (ℓ t) (hmaps ht)) (hℓ' t) hmaps
  have hg' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun t ↦ f' (ℓ t) v) (f'' (ℓ t) v v) (Icc 0 1) t := by
    simpa using (HasFDerivWithinAt.comp_hasDerivWithinAt t (hf' (ℓ t) (hmaps ht)) (hℓ' t)
      hmaps).clm_apply (hasDerivWithinAt_const t (Icc 0 1) v)
  -- Cauchy's mean value theorem for `h t = g 1 - g t - g' t * (1 - t)` and `k t = (1 - t) ^ 2`,
  -- with `h' t = -(f'' (ℓ t) v v * (1 - t))` and `k' t = -(2 * (1 - t))`.
  have hint {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : Icc (0 : ℝ) 1 ∈ 𝓝 t :=
    Icc_mem_nhds ht.1 ht.2
  have hk (t : ℝ) : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ 2) (-(2 * (1 - t))) t := by
    simpa using ((hasDerivAt_id' t).const_sub 1).fun_pow 2
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun t ↦ f (ℓ 1) - f (ℓ t) - f' (ℓ t) v * (1 - t))
        (-(f'' (ℓ t) v v * (1 - t))) (Icc 0 1) t := by
    have := ((hasDerivWithinAt_const t (Icc 0 1) (f (ℓ 1))).fun_sub (hg t ht)).fun_sub
      ((hg' t ht).fun_mul ((hasDerivAt_id' t).const_sub 1).hasDerivWithinAt)
    convert this using 1
    ring
  obtain ⟨c, hc, hmvt⟩ := exists_ratio_hasDerivAt_eq_ratio_slope _ _ zero_lt_one
    (fun t ht ↦ (hh t ht).continuousWithinAt)
    (fun t ht ↦ (hh t (Ioo_subset_Icc_self ht)).hasDerivAt (hint ht)) _ _
    (fun t _ ↦ (hk t).continuousAt.continuousWithinAt) (fun t _ ↦ hk t)
  refine ⟨ℓ c, ?_, ?_⟩
  · rw [segment_symm, segment_eq_image']
    exact ⟨c, Ioo_subset_Icc_self hc, rfl⟩
  · have h1c : 0 < 1 - c := sub_pos.2 hc.2
    have hℓ0 : ℓ 0 = y := by simp [hℓ]
    have hℓ1 : ℓ 1 = x := by simp [hℓ, hv]
    simp only [hℓ0, hℓ1, sub_self, mul_zero, sub_zero, one_pow, zero_pow two_ne_zero,
      zero_sub] at hmvt
    rw [bregDiv]
    nlinarith

namespace LMLExplore

/-- **Stability bound through the Hessian** [LS, Theorem 26.13]. Let the Bregman divergence
`D_f(x, y)` be nonnegative and equal to `H (x - y) (x - y) / 2`, as for a convex `f` and the
Hessian `H` at a point of `[x, y]` given by `Convex.exists_mem_segment_bregDiv_eq`. Then for
every `η > 0`, every linear functional `u` and every `c ≥ 0` with
`u (x - y) ^ 2 ≤ c * H (x - y) (x - y)`, `u (x - y) - D_f(x, y) / η ≤ η / 2 * c`.
[LS] states the bound `η / 2 * ‖u‖²_{H⁻¹}` for a positive definite `H`: by the Cauchy–Schwarz
inequality for `H`, `c = ‖u‖²_{H⁻¹}` satisfies the hypothesis. -/
theorem apply_sub_sub_bregDiv_div_le_of_bregDiv_eq {J : E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hD : D_[f](x, y, J) = H (x - y) (x - y) / 2) (hD_nonneg : 0 ≤ D_[f](x, y, J)) {η : ℝ}
    (hη : 0 < η) (u : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hu : u (x - y) ^ 2 ≤ c * H (x - y) (x - y)) :
    u (x - y) - D_[f](x, y, J) / η ≤ η / 2 * c := by
  set a := u (x - y)
  set q := H (x - y) (x - y)
  have hq : 0 ≤ q := by linarith
  -- `2 η a ≤ η² c + q`, since `(η a)² ≤ η² c q` and `2 η a q ≤ (η a)² + q²`
  have key : 2 * η * a ≤ η ^ 2 * c + q := by
    rcases hq.eq_or_lt with hq0 | hq0
    · have ha : a = 0 := by nlinarith [sq_nonneg a]
      rw [ha, ← hq0]
      nlinarith [mul_nonneg (sq_nonneg η) hc]
    · have h1 : η ^ 2 * a ^ 2 ≤ η ^ 2 * (c * q) := mul_le_mul_of_nonneg_left hu (sq_nonneg η)
      refine le_of_mul_le_mul_right ?_ hq0
      nlinarith [sq_nonneg (η * a - q)]
  have ha : a ≤ (η ^ 2 * c + q) / (2 * η) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h_eq : (η ^ 2 * c + q) / (2 * η) = η / 2 * c + q / 2 / η := by
    field_simp
  rw [hD]
  linarith

end LMLExplore

/-- **Stability bound through the Hessian** for a convex function [LS, Theorems 26.12 and 26.13].
Let `f` be convex on `s`, with derivative `f' z` and second derivative `f'' z` within `s` at
every `z ∈ s`, and let `x, y ∈ s`. There is a point `z` of the segment `[x, y]` such that for
every `η > 0`, every linear functional `u` and every `c ≥ 0` with
`u (x - y) ^ 2 ≤ c * f'' z (x - y) (x - y)`, `u (x - y) - D_f(x, y) / η ≤ η / 2 * c`. -/
theorem ConvexOn.exists_mem_segment_apply_sub_sub_bregDiv_div_le (hfc : ConvexOn ℝ s f)
    (hf : ∀ z ∈ s, HasFDerivWithinAt f (f' z) s z)
    (hf' : ∀ z ∈ s, HasFDerivWithinAt f' (f'' z) s z) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ z ∈ segment ℝ x y, ∀ η, 0 < η → ∀ (u : E →L[ℝ] ℝ) (c : ℝ), 0 ≤ c →
      u (x - y) ^ 2 ≤ c * f'' z (x - y) (x - y) →
      u (x - y) - D_[f](x, y, f' y) / η ≤ η / 2 * c := by
  obtain ⟨z, hz, hD⟩ := hfc.1.exists_mem_segment_bregDiv_eq hf hf' hx hy
  exact ⟨z, hz, fun η hη u c hc hu ↦ LMLExplore.apply_sub_sub_bregDiv_div_le_of_bregDiv_eq hD
    ((hf y hy).hasSubgradientWithinAt hfc hy x hx) hη u hc hu⟩
