/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.InformationTheory.KullbackLeibler.Finite
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Bregman.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# The negative entropy on the probability simplex

The **unnormalized negative entropy** of a vector `x : α → ℝ` over a finite set `α` is
`negEntropy x = ∑ a, (x a * log (x a) - x a)` [LS, Example 26.5]. It is the potential of the
exponential weights algorithm seen as follow the regularized leader on the probability simplex
[LS, Example 28.3 and Proposition 28.7]. On the simplex it equals `∑ a, x a * log (x a) - 1`, so
it takes values in `[-log k - 1, -1]`, with `k` the cardinality of `α`.

Pinsker's inequality for probability vectors `x` and `z` with `x a = 0` whenever `z a = 0`
(`LMLExplore.sq_sum_abs_sub_le_two_mul_sum_mul_log_div`) reads
`(∑ a, |x a - z a|) ^ 2 ≤ 2 ∑ a, x a * log (x a / z a)`. The right-hand side is twice the relative
entropy of `x` with respect to `z`, which is also the Bregman divergence of `negEntropy` between
`x` and `z` on the simplex. As a consequence, the negative entropy is `1`-strongly convex on the
simplex for the `ℓ¹` norm, the norm of `PiLp 1 (fun _ : α ↦ ℝ)`. This is the strong convexity
that the regret bound of follow the regularized leader with a strongly convex potential uses, the
dual norm of the `ℓ¹` norm being the sup norm.

## Main definitions

* `LMLExplore.negEntropy x`: the unnormalized negative entropy `∑ a, (x a * log (x a) - x a)`.

## Main statements

* `LMLExplore.neg_log_card_sub_one_le_negEntropy`, `LMLExplore.negEntropy_le_neg_one`: on the
  simplex, `-log k - 1 ≤ negEntropy x ≤ -1`.
* `LMLExplore.strongConvexOn_negEntropy`: the negative entropy is `1`-strongly convex on the
  simplex for the `ℓ¹` norm.
* `LMLExplore.hasFDerivAt_negEntropy`: at a vector with nonzero coordinates, the derivative of the
  negative entropy on `PiLp p (fun _ : α ↦ ℝ)` is `h ↦ ∑ a, log (x a) * h a`.
* `LMLExplore.bregDiv_negEntropy`: on the simplex, the Bregman divergence of the negative entropy
  for that derivative is the relative entropy `∑ a, x a * log (x a / y a)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset Real WithLp
open scoped ENNReal

namespace LMLExplore

variable {α : Type*} [Fintype α]

/-- The **unnormalized negative entropy** `∑ a, (x a * log (x a) - x a)` of a vector `x : α → ℝ`
[LS, Example 26.5], with the convention `0 * log 0 = 0`. -/
noncomputable def negEntropy (x : α → ℝ) : ℝ := ∑ a, (x a * log (x a) - x a)

lemma negEntropy_def (x : α → ℝ) : negEntropy x = ∑ a, (x a * log (x a) - x a) := (rfl)

/-- On the simplex, the negative entropy is `∑ a, x a * log (x a) - 1`. -/
lemma negEntropy_of_mem_simplex {x : α → ℝ} (hx : x ∈ simplex α) :
    negEntropy x = ∑ a, x a * log (x a) - 1 := by
  rw [negEntropy_def, sum_sub_distrib, (mem_simplex_iff.1 hx).2]

/-- On the simplex, the negative entropy is at least `-log k - 1`, with `k` the cardinality of
`α`; the uniform vector attains this value. -/
theorem neg_log_card_sub_one_le_negEntropy {x : α → ℝ} (hx : x ∈ simplex α) :
    -log (Fintype.card α) - 1 ≤ negEntropy x := by
  have := nonempty_of_mem_simplex hx
  have hk : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  -- the relative entropy of `x` with respect to the uniform vector is nonnegative
  obtain ⟨hx0, hx1⟩ := mem_simplex_iff.1 hx
  obtain ⟨hu0, hu1⟩ := mem_simplex_iff.1 (uniform_mem_simplex α)
  have h := sum_mul_log_div_nonneg hx0 hu0 (fun a h ↦ absurd h (inv_pos.2 hk).ne')
    (hu1.trans hx1.symm).le
  have h_eq (a : α) : x a * log (x a / (Fintype.card α : ℝ)⁻¹) =
      x a * log (x a) + x a * log (Fintype.card α) := by
    rcases eq_or_ne (x a) 0 with h0 | h0
    · simp [h0]
    · rw [log_div h0 (inv_pos.2 hk).ne', log_inv]
      ring
  simp_rw [h_eq, sum_add_distrib, ← sum_mul, hx1, one_mul] at h
  rw [negEntropy_of_mem_simplex hx]
  linarith

/-- On the simplex, the negative entropy is at most `-1`, the value at the vertices. -/
theorem negEntropy_le_neg_one {x : α → ℝ} (hx : x ∈ simplex α) : negEntropy x ≤ -1 := by
  rw [negEntropy_of_mem_simplex hx, sub_le_iff_le_add, neg_add_cancel]
  exact sum_nonpos fun a _ ↦
    mul_log_nonpos ((mem_simplex_iff.1 hx).1 a) ((simplex_subset_Icc hx).2 a)

/-- For `a, b > 0` and `x, y ≥ 0`, with `z = a x + b y`, the convexity defect of `t ↦ t log t - t`
is the weighted sum of the relative entropy terms of `x` and `y` with respect to `z`. -/
private lemma mul_log_sub_convexity_defect {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    a * (x * log x - x) + b * (y * log y - y) -
        ((a * x + b * y) * log (a * x + b * y) - (a * x + b * y)) =
      a * (x * log (x / (a * x + b * y))) + b * (y * log (y / (a * x + b * y))) := by
  rcases hx.eq_or_lt with rfl | hx
  · rcases hy.eq_or_lt with rfl | hy
    · simp
    rw [log_div hy.ne' (by positivity)]
    simp only [mul_zero, zero_mul, zero_add, zero_sub]
    ring
  have hz : a * x + b * y ≠ 0 := by positivity
  rcases hy.eq_or_lt with rfl | hy
  · rw [log_div hx.ne' hz]
    simp only [mul_zero, add_zero, sub_zero, log_zero, zero_div]
    ring
  rw [log_div hx.ne' hz, log_div hy.ne' hz]
  ring

/-- The unnormalized negative entropy is `1`-strongly convex on the simplex for the `ℓ¹` norm:
for `x`, `y` in the simplex and `a, b ≥ 0` with `a + b = 1`,
`negEntropy (a x + b y) ≤ a negEntropy x + b negEntropy y - a b ‖x - y‖₁ ^ 2 / 2`.
This is a consequence of Pinsker's inequality. -/
theorem strongConvexOn_negEntropy :
    StrongConvexOn (ofLp ⁻¹' simplex α : Set (PiLp 1 fun _ : α ↦ ℝ)) 1
      fun x ↦ negEntropy (ofLp x) := by
  refine ⟨(convex_simplex α).linear_preimage (WithLp.linearEquiv 1 ℝ (α → ℝ)).toLinearMap,
    fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp only [Set.mem_preimage] at hx hy
  rw [PiLp.norm_eq_of_L1]
  simp only [ofLp_add, ofLp_smul, PiLp.sub_apply, Real.norm_eq_abs, smul_eq_mul]
  set D := ∑ i, |x i - y i|
  have hx0 := (mem_simplex_iff.1 hx).1
  have hy0 := (mem_simplex_iff.1 hy).1
  rcases ha.eq_or_lt with rfl | ha
  · simp [show b = 1 by linarith]
  rcases hb.eq_or_lt with rfl | hb
  · simp [show a = 1 by linarith]
  set z : α → ℝ := a • ofLp x + b • ofLp y
  have hz (i : α) : z i = a * x i + b * y i := by simp [z]
  have hz_mem : z ∈ simplex α := convex_simplex α hx hy ha.le hb.le hab
  have hxz (i : α) : z i = 0 → x i = 0 := fun h ↦ by
    rw [hz] at h
    nlinarith [hx0 i, hy0 i, mul_nonneg ha.le (hx0 i), mul_nonneg hb.le (hy0 i)]
  have hyz (i : α) : z i = 0 → y i = 0 := fun h ↦ by
    rw [hz] at h
    nlinarith [hx0 i, hy0 i, mul_nonneg ha.le (hx0 i), mul_nonneg hb.le (hy0 i)]
  -- Pinsker's inequality for `x` and `y` against their mixture `z`
  have h_px := sq_sum_abs_sub_le_two_mul_sum_mul_log_div hx hz_mem hxz
  have h_py := sq_sum_abs_sub_le_two_mul_sum_mul_log_div hy hz_mem hyz
  have h_dx : ∑ i, |x i - z i| = b * D := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hz, show x i - (a * x i + b * y i) = b * (x i - y i) by
      linear_combination -x i * hab, abs_mul, abs_of_pos hb]
  have h_dy : ∑ i, |y i - z i| = a * D := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hz, show y i - (a * x i + b * y i) = a * (y i - x i) by
      linear_combination -y i * hab, abs_mul, abs_of_pos ha, abs_sub_comm]
  -- the convexity defect is `a KL(x, z) + b KL(y, z)`
  have h_defect : a * negEntropy (ofLp x) + b * negEntropy (ofLp y) - negEntropy z =
      a * ∑ i, x i * log (x i / z i) + b * ∑ i, y i * log (y i / z i) := by
    simp only [negEntropy_def, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [hz]
    exact mul_log_sub_convexity_defect ha hb (hx0 i) (hy0 i)
  rw [h_dx] at h_px
  rw [h_dy] at h_py
  have h_sum : a * b * (1 / 2 * D ^ 2) =
      a * ((b * D) ^ 2 / 2) + b * ((a * D) ^ 2 / 2) := by
    linear_combination -(a * b * D ^ 2 / 2) * hab
  rw [h_sum]
  nlinarith [mul_le_mul_of_nonneg_left h_px ha.le, mul_le_mul_of_nonneg_left h_py hb.le]

/-- At a vector `x` with nonzero coordinates, the negative entropy on `PiLp p (fun _ : α ↦ ℝ)`
has derivative `h ↦ ∑ a, log (x a) * h a`. -/
theorem hasFDerivAt_negEntropy {p : ℝ≥0∞} [Fact (1 ≤ p)] {x : PiLp p fun _ : α ↦ ℝ}
    (hx : ∀ a, x a ≠ 0) :
    HasFDerivAt (fun x : PiLp p (fun _ : α ↦ ℝ) ↦ negEntropy (ofLp x))
      (∑ a, log (x a) • PiLp.proj (𝕜 := ℝ) p (fun _ : α ↦ ℝ) a) x := by
  simp_rw [negEntropy_def]
  refine HasFDerivAt.fun_sum fun a _ ↦ ?_
  have h : HasDerivAt (fun t ↦ t * log t - t) (log (x a)) (x a) := by
    simpa using (hasDerivAt_mul_log (hx a)).fun_sub (hasDerivAt_id' (x a))
  exact h.comp_hasFDerivAt x (PiLp.proj (𝕜 := ℝ) p (fun _ : α ↦ ℝ) a).hasFDerivAt

/-- On the simplex, the **Bregman divergence of the negative entropy**, for the derivative
`h ↦ ∑ a, log (y a) * h a` of `hasFDerivAt_negEntropy`, is the relative entropy
`D(x, y) = ∑ a, x a * log (x a / y a)` of `x` with respect to `y`, when `x a = 0` whenever
`y a = 0`. -/
theorem bregDiv_negEntropy {p : ℝ≥0∞} {x y : PiLp p fun _ : α ↦ ℝ}
    (hx : ofLp x ∈ simplex α) (hy : ofLp y ∈ simplex α) (hxy : ∀ a, y a = 0 → x a = 0) :
    bregDiv (fun x : PiLp p (fun _ : α ↦ ℝ) ↦ negEntropy (ofLp x)) x y
        (∑ a, log (y a) • PiLp.proj (𝕜 := ℝ) p (fun _ : α ↦ ℝ) a) =
      ∑ a, x a * log (x a / y a) := by
  have h_pt (a : α) : x a * log (x a / y a) =
      x a * log (x a) - x a - (y a * log (y a) - y a) - log (y a) * (x a - y a) + (x a - y a) := by
    rcases eq_or_ne (x a) 0 with h0 | h0
    · simp only [h0, zero_div, log_zero, mul_zero, zero_sub, sub_zero]
      ring
    rw [log_div h0 fun h ↦ h0 (hxy a h)]
    ring
  have h_mass : ∑ a, (x a - y a) = 0 := by
    rw [sum_sub_distrib, (mem_simplex_iff.1 hx).2, (mem_simplex_iff.1 hy).2, sub_self]
  simp_rw [h_pt, sum_add_distrib, h_mass, add_zero, sum_sub_distrib, bregDiv, negEntropy_def]
  simp

end LMLExplore
