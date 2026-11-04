/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Real-valued bounds on the harmonic sums

Mathlib's `harmonic_le_one_add_log` bounds the rational harmonic numbers. This file restates it as
a sum of real numbers, and bounds the variant whose index is clipped at `1`, which appears in the
regret analysis of optimistic algorithms through the squared confidence widths `max(1, N)⁻¹`.

## Main statements

* `Real.sum_range_inv_add_one_le`: `∑_{j < n} (j + 1)⁻¹ ≤ 1 + log n`.
* `Real.sum_range_inv_max_one_le`: `∑_{j < n} max(1, j)⁻¹ ≤ 2 + log n`.
-/

public section

open Finset

namespace Real

/-- The partial sums of the harmonic series in `ℝ`: `∑_{j < n} (j + 1)⁻¹ ≤ 1 + log n`. -/
theorem sum_range_inv_add_one_le (n : ℕ) :
    ∑ j ∈ range n, ((j : ℝ) + 1)⁻¹ ≤ 1 + log n := by
  simpa [harmonic] using harmonic_le_one_add_log n

/-- The harmonic sum with index clipped at `1`: `∑_{j < n} max(1, j)⁻¹ ≤ 2 + log n`. The term
`j = 0` contributes `1` and the others the harmonic sum `∑_{j < n - 1} (j + 1)⁻¹`. -/
theorem sum_range_inv_max_one_le (n : ℕ) :
    ∑ j ∈ range n, (max 1 (j : ℝ))⁻¹ ≤ 2 + log n := by
  rcases n with _ | n
  · simp
  rw [LMLExplore.sum_range_succ_comp_max_one (fun x : ℝ ↦ x⁻¹), inv_one]
  have h_log : log n ≤ log ((n + 1 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact log_le_log (by positivity) (by simp)
  linarith [sum_range_inv_add_one_le n]

end Real
