/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Basic.ENNReal.Real

/-!
# Extended nonnegative reals of real numbers

## Main statements

* `ENNReal.ofReal_div_lt_of_ofReal_le_ofReal_mul`: if `ofReal θ ≤ ofReal N * I` with `0 < θ` and
  `0 ≤ N < b`, then `ofReal (θ / b) < I`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- If `θ ≤ N I` with `0 < θ` and `0 ≤ N < b`, then `θ / b < I`. In a peeling argument, a
deviation `θ` reached with fewer than `b` samples forces a rate `I` above `θ / b`. -/
theorem ofReal_div_lt_of_ofReal_le_ofReal_mul {N θ b : ℝ} {I : ℝ≥0∞} (hN : 0 ≤ N) (hθ : 0 < θ)
    (hb : N < b) (h : ENNReal.ofReal θ ≤ ENNReal.ofReal N * I) : ENNReal.ofReal (θ / b) < I := by
  by_contra! h'
  have hb0 : 0 < b := hN.trans_lt hb
  have hlt : N * (θ / b) < θ :=
    (mul_lt_mul_of_pos_right hb (div_pos hθ hb0)).trans_eq (mul_div_cancel₀ θ hb0.ne')
  refine (h.trans (mul_le_mul_right h' _)).not_gt ?_
  rw [← ENNReal.ofReal_mul hN]
  exact (ENNReal.ofReal_lt_ofReal_iff hθ).2 hlt

end ENNReal
