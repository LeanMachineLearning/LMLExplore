/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.Normed.Group.Real

/-!
# Norm bounds in seminormed groups

Bounds on the norm of a finite sum in a seminormed group whose terms have norm at most `L` (with
its special case for real numbers in `[-1, 1]`), and
the affine bound satisfied by a point that is a `β`-contraction of another towards a center.

## Main statements

* `norm_sum_le_card_mul`: a sum over `s` of terms of norm at most `L` has norm at most `#s * L`.
* `abs_sum_le_of_abs_le_one`: real numbers in `[-1, 1]` indexed by `s < t` sum to at most `t` in
  absolute value.
* `norm_sum_Icc_sub_le`: the sum `∑ t - τ ≤ s ≤ t, f s` of the last `τ + 1` terms of a sequence
  whose terms of index at most `t` have norm at most `L` has norm at most `(τ + 1) * L`.
* `norm_le_mul_norm_add_mul_norm_of_norm_sub_le_mul`: if `‖a - c‖ ≤ β * ‖b - c‖` with `0 ≤ β`,
  then `‖a‖ ≤ β * ‖b‖ + (1 + β) * ‖c‖`.
-/

public section

open Finset

namespace LMLExplore

variable {ι E : Type*} [SeminormedAddCommGroup E]

/-- A sum over `s` of terms of norm at most `L` has norm at most `#s * L`. -/
theorem norm_sum_le_card_mul (s : Finset ι) {f : ι → E} {L : ℝ} (h : ∀ i ∈ s, ‖f i‖ ≤ L) :
    ‖∑ i ∈ s, f i‖ ≤ #s * L :=
  (norm_sum_le_of_le s h).trans_eq (by rw [sum_const, nsmul_eq_mul])

/-- Real numbers in `[-1, 1]` indexed by `s < t` sum to at most `t` in absolute value. -/
theorem abs_sum_le_of_abs_le_one {c : ℕ → ℝ} {t : ℕ} (hc : ∀ s < t, |c s| ≤ 1) :
    |∑ s ∈ range t, c s| ≤ t := by
  simpa using norm_sum_le_card_mul (range t) (L := 1) fun s hs ↦
    (Real.norm_eq_abs (c s)).trans_le (hc s (mem_range.1 hs))

/-- The sum `∑ t - τ ≤ s ≤ t, f s` of the last `τ + 1` terms of a sequence up to index `t` has
norm at most `(τ + 1) * L` when the terms of index at most `t` have norm at most `L`. -/
theorem norm_sum_Icc_sub_le {f : ℕ → E} {L : ℝ} (t τ : ℕ) (h : ∀ s ≤ t, ‖f s‖ ≤ L) :
    ‖∑ s ∈ Icc (t - τ) t, f s‖ ≤ (τ + 1) * L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (h t le_rfl)
  refine (norm_sum_le_card_mul _ fun s hs ↦ h s (mem_Icc.mp hs).2).trans ?_
  gcongr
  rw [Nat.card_Icc]
  exact_mod_cast (by omega : t + 1 - (t - τ) ≤ τ + 1)

/-- If `a` is closer to the center `c` than `b`, up to a factor `β ≥ 0`, then
`‖a‖ ≤ β * ‖b‖ + (1 + β) * ‖c‖`. This turns a pseudo-contraction towards `c` into an affine bound
on the norm. -/
theorem norm_le_mul_norm_add_mul_norm_of_norm_sub_le_mul {a b c : E} {β : ℝ} (hβ : 0 ≤ β)
    (h : ‖a - c‖ ≤ β * ‖b - c‖) : ‖a‖ ≤ β * ‖b‖ + (1 + β) * ‖c‖ := by
  have h1 := norm_sub_norm_le a c
  have h2 := mul_le_mul_of_nonneg_left (norm_sub_le b c) hβ
  linarith

end LMLExplore
