/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.MeanInequalities
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Powers of nonnegative concave functions

Mathlib proves that `x ↦ x ^ p` is concave on `[0, ∞)` for `p ∈ [0, 1]` (`Real.concaveOn_rpow`).
Since it is also nondecreasing there, it preserves concavity: for a nonnegative concave function
`f` on a set `s` of a real vector space, `x ↦ f x ^ p` is concave on `s`. More generally the
weighted geometric mean `(a, b) ↦ a ^ p * b ^ q`, `p, q ≥ 0`, `p + q = 1`, is concave and
nondecreasing on the nonnegative quadrant (`Real.rpow_mul_rpow_add_rpow_mul_rpow_le`), so
`x ↦ f x ^ p * g x ^ q` is concave on `s` for nonnegative concave `f` and `g`.

These are the facts behind the calculus of exp-concave functions: `f` is `α`-exp-concave when
`exp (-(α * f))` is concave, and `exp (-(β * f)) = exp (-(α * f)) ^ (β / α)`,
`exp (-(γ * (f + g))) = exp (-(α * f)) ^ (γ / α) * exp (-(β * g)) ^ (γ / β)`.

## Main statements

* `ConcaveOn.rpow`: a nonnegative concave function raised to a power `p ∈ [0, 1]` is concave.
* `ConcaveOn.rpow_mul_rpow`: for nonnegative concave `f` and `g` and `p, q ≥ 0` with `p + q = 1`,
  `x ↦ f x ^ p * g x ^ q` is concave.
-/

public section

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {s : Set E} {f g : E → ℝ} {p q : ℝ}

namespace ConcaveOn

/-- For nonnegative concave functions `f` and `g` and exponents `p, q ≥ 0` with `p + q = 1`, the
weighted geometric mean `x ↦ f x ^ p * g x ^ q` is concave. -/
theorem rpow_mul_rpow (hf : ConcaveOn ℝ s f) (hg : ConcaveOn ℝ s g) (hf₀ : ∀ x ∈ s, 0 ≤ f x)
    (hg₀ : ∀ x ∈ s, 0 ≤ g x) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ConcaveOn ℝ s fun x ↦ f x ^ p * g x ^ q := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hfx := hf₀ x hx
  have hfy := hf₀ y hy
  have hgx := hg₀ x hx
  have hgy := hg₀ y hy
  -- the weighted geometric mean is positively homogeneous
  have hhom {c u v : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      c * (u ^ p * v ^ q) = (c * u) ^ p * (c * v) ^ q := by
    rw [Real.mul_rpow hc hu, Real.mul_rpow hc hv]
    nth_rw 1 [← Real.rpow_one c]
    rw [← hpq, Real.rpow_add' hc (by rw [hpq]; exact one_ne_zero)]
    ring
  simp only [smul_eq_mul]
  rw [hhom ha hfx hgx, hhom hb hfy hgy]
  calc (a * f x) ^ p * (a * g x) ^ q + (b * f y) ^ p * (b * g y) ^ q
      ≤ (a * f x + b * f y) ^ p * (a * g x + b * g y) ^ q :=
        Real.rpow_mul_rpow_add_rpow_mul_rpow_le (by positivity) (by positivity) (by positivity)
          (by positivity) hp hq hpq
    _ ≤ f (a • x + b • y) ^ p * g (a • x + b • y) ^ q := by
        have hz := hf.1 hx hy ha hb hab
        gcongr
        · exact Real.rpow_nonneg (hf₀ _ hz) p
        · simpa only [smul_eq_mul] using hf.2 hx hy ha hb hab
        · simpa only [smul_eq_mul] using hg.2 hx hy ha hb hab

/-- A nonnegative concave function raised to a power `p ∈ [0, 1]` is concave. -/
theorem rpow (hf : ConcaveOn ℝ s f) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ s fun x ↦ f x ^ p :=
  (hf.rpow_mul_rpow (concaveOn_const 1 hf.1) hf₀ (fun _ _ ↦ zero_le_one) hp₀ (sub_nonneg.2 hp₁)
    (add_sub_cancel _ _)).congr fun x _ ↦ by simp only [Real.one_rpow, mul_one]

end ConcaveOn
