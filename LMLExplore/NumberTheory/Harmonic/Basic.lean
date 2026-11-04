/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Tactic.Ring

/-!
# Harmonic numbers as sums of reversed inverses

The harmonic number `H_K = ∑_{i = 1}^K 1 / i`, minus its first term, is the sum
`∑_{j < K - 1} 1 / (K - j) = 1 / K + ⋯ + 1 / 2` of the inverses taken in decreasing order of the
denominators. Such sums appear when the `j`-th phase of an elimination algorithm with `K` arms
pulls `K - j` arms, as in successive rejects for best arm identification.

## Main statements

* `LMLExplore.sum_range_inv_add_one_sub_eq_harmonic_sub_one`:
  `∑_{j < m} 1 / (m + 1 - j) = H_{m + 1} - 1`.
* `LMLExplore.sum_range_inv_sub_eq_harmonic_sub_one`: `∑_{j < K - 1} 1 / (K - j) = H_K - 1` for
  `K ≠ 0`.
-/

public section

open Finset

namespace LMLExplore

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

/-- `∑_{j < m} 1 / (m + 1 - j) = H_{m + 1} - 1`, with `H` the harmonic numbers. -/
theorem sum_range_inv_add_one_sub_eq_harmonic_sub_one (m : ℕ) :
    ∑ j ∈ range m, ((m + 1 - j : 𝕜))⁻¹ = harmonic (m + 1) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ', harmonic_succ (m + 1)]
    push_cast
    rw [sum_congr rfl fun j _ ↦ by rw [show (m + 1 + 1 - (j + 1) : 𝕜) = m + 1 - j by ring], ih]
    ring

/-- `∑_{j < K - 1} 1 / (K - j) = H_K - 1` for `K ≠ 0`, with `H` the harmonic numbers. -/
theorem sum_range_inv_sub_eq_harmonic_sub_one {K : ℕ} (hK : K ≠ 0) :
    ∑ j ∈ range (K - 1), ((K - j : 𝕜))⁻¹ = harmonic K - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK
  rw [Nat.succ_sub_one, Nat.cast_succ]
  exact sum_range_inv_add_one_sub_eq_harmonic_sub_one m

end LMLExplore
