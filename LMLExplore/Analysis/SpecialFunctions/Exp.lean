/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Sums of exponentials

The geometric sum `∑_{s ≥ 1} exp (-c s) = 1 / (exp c - 1)` is at most `1 / c` for `c > 0`. This is
the form in which the sums over the sample sizes of sub-Gaussian tail bounds `exp (-s ε² / (2 σ²))`
are bounded, for example in the proof of [LS, Theorem 8.1].

## Main statements

* `Real.sum_range_exp_neg_mul_le`: `∑_{s < m} exp (-c (s + 1)) ≤ 1 / c` for `c > 0`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset

namespace Real

/-- For `c > 0`, `∑_{s < m} exp (-c (s + 1)) ≤ 1 / c`, uniformly in `m`. -/
theorem sum_range_exp_neg_mul_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∑ s ∈ range m, exp (-(c * (s + 1))) ≤ c⁻¹ := by
  -- each term is at most `v s - v (s + 1)` for `v s = exp (-c s) / c`, since `1 + c ≤ exp c`
  set v : ℕ → ℝ := fun s ↦ exp (-(c * s)) / c with hv
  have h_le (s : ℕ) : exp (-(c * (s + 1))) ≤ v s - v (s + 1) := by
    have h := add_one_le_exp c
    simp only [hv, Nat.cast_add_one]
    rw [← sub_div, le_div_iff₀ hc, show -(c * (s + 1)) = -(c * s) + -c by ring, exp_add]
    have h1 : exp (-c) * (c + 1) ≤ 1 := by
      calc exp (-c) * (c + 1)
      _ ≤ exp (-c) * exp c := by gcongr
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    nlinarith [mul_le_mul_of_nonneg_left h1 (exp_pos (-(c * s))).le]
  calc ∑ s ∈ range m, exp (-(c * (s + 1)))
  _ ≤ ∑ s ∈ range m, (v s - v (s + 1)) := sum_le_sum fun s _ ↦ h_le s
  _ = v 0 - v m := sum_range_sub' v m
  _ ≤ c⁻¹ := by
    have : 0 ≤ v m := by positivity
    simp only [hv, CharP.cast_eq_zero, mul_zero, neg_zero, exp_zero, one_div] at this ⊢
    linarith

end Real
