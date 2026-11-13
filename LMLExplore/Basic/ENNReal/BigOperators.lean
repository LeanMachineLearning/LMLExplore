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

end ENNReal
