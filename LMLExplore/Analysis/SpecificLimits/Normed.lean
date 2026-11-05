/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Partial sums of the series `∑ n, n * r ^ n`

Mathlib computes the sum of the series `∑ n, n * r ^ n` for `‖r‖ < 1`
(`hasSum_coe_mul_geometric_of_norm_lt_one`). We record the resulting bound on its partial sums
for a nonnegative real ratio.

## Main statements

* `LMLExplore.sum_range_natCast_mul_pow_le`: for `0 ≤ r < 1`,
  `∑ j ∈ range n, j * r ^ j ≤ r / (1 - r) ^ 2`.
-/

public section

open Finset

namespace LMLExplore

/-- The partial sums of the series `∑ j, j * r ^ j` are at most `r / (1 - r) ^ 2` for
`0 ≤ r < 1`. -/
lemma sum_range_natCast_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ range n, (j * r ^ j : ℝ) ≤ r / (1 - r) ^ 2 :=
  sum_le_hasSum (range n) (fun j _ ↦ by positivity)
    (hasSum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hr0]))

end LMLExplore
