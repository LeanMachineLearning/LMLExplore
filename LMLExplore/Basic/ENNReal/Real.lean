/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Basic.ENNReal.Real

/-!
# Convex combinations of extended nonnegative reals and real numbers

## Main statements

* `ENNReal.ofReal_mul_add_ofReal_one_sub_mul`: for finite `x` and `y` and `p ∈ [0, 1]`, the convex
  combination `p x + (1 - p) y` computed in `ℝ≥0∞` is the image under `ENNReal.ofReal` of the one
  computed in `ℝ`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- For finite `x` and `y` and `p ∈ [0, 1]`, the convex combination `p x + (1 - p) y` computed in
`ℝ≥0∞` is the image under `ENNReal.ofReal` of the one computed in `ℝ`. -/
theorem ofReal_mul_add_ofReal_one_sub_mul {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ENNReal.ofReal p * x + ENNReal.ofReal (1 - p) * y =
      ENNReal.ofReal (p * x.toReal + (1 - p) * y.toReal) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.2 hp₁
  rw [ENNReal.ofReal_add (mul_nonneg hp₀ toReal_nonneg) (mul_nonneg hq toReal_nonneg),
    ENNReal.ofReal_mul hp₀,
    ENNReal.ofReal_mul hq, ENNReal.ofReal_toReal hx, ENNReal.ofReal_toReal hy]

end ENNReal
