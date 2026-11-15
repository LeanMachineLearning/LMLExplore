/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Weighted sums of finite extended nonnegative reals

## Main statements

* `ENNReal.ofReal_sum_mul_toReal`: a weighted sum `∑ x ∈ s, f x * (g x).toReal` of finite
  extended nonnegative reals `g x` with nonnegative real weights `f x`, mapped back to `ℝ≥0∞`, is
  `∑ x ∈ s, ENNReal.ofReal (f x) * g x`. It moves a real convex combination of finite
  divergences, such as a mixture of the divergence vectors of finitely many models, to `ℝ≥0∞`.
* `ENNReal.ofReal_sum_mul_add`: an affine form `∑ x ∈ s, f x * g x + c` with nonnegative real
  coefficients, evaluated at a point with nonnegative real coordinates and mapped to `ℝ≥0∞`, is
  the same affine form of the images in `ℝ≥0∞`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- A sum `∑ x ∈ s, f x * (g x).toReal` of finite extended nonnegative reals `g x` with
nonnegative weights `f x`, mapped back to `ℝ≥0∞`, is `∑ x ∈ s, ENNReal.ofReal (f x) * g x`. -/
lemma ofReal_sum_mul_toReal {ι : Type*} {s : Finset ι} {f : ι → ℝ} {g : ι → ℝ≥0∞}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, g x ≠ ∞) :
    ENNReal.ofReal (∑ x ∈ s, f x * (g x).toReal) = ∑ x ∈ s, ENNReal.ofReal (f x) * g x := by
  rw [ofReal_sum_of_nonneg fun x hx ↦ mul_nonneg (hf x hx) toReal_nonneg]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [ofReal_mul (hf x hx), ofReal_toReal (hg x hx)]

/-- An affine form `∑ x ∈ s, f x * g x + c` with nonnegative real coefficients `f x`, `c`,
evaluated at a point with nonnegative real coordinates `g x`, commutes with `ENNReal.ofReal`. -/
lemma ofReal_sum_mul_add {ι : Type*} {s : Finset ι} {f g : ι → ℝ} {c : ℝ}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) (hc : 0 ≤ c) :
    ENNReal.ofReal (∑ x ∈ s, f x * g x + c) =
      ∑ x ∈ s, ENNReal.ofReal (f x) * ENNReal.ofReal (g x) + ENNReal.ofReal c := by
  have h : ∀ x ∈ s, 0 ≤ f x * g x := fun x hx ↦ mul_nonneg (hf x hx) (hg x hx)
  rw [ofReal_add (Finset.sum_nonneg h) hc, ofReal_sum_of_nonneg h]
  refine congrArg (· + _) (Finset.sum_congr rfl fun x hx ↦ ?_)
  rw [ofReal_mul (hf x hx)]

end ENNReal
