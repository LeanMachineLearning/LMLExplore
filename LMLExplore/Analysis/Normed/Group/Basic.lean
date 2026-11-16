/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Norms of finite sums of bounded terms

Bounds on the norm of a finite sum in a seminormed group whose terms have norm at most `L`.

## Main statements

* `norm_sum_le_card_mul`: a sum over `s` of terms of norm at most `L` has norm at most `#s * L`.
* `norm_sum_Icc_sub_le`: the sum `∑ t - τ ≤ s ≤ t, f s` of the last `τ + 1` terms of a sequence
  whose terms of index at most `t` have norm at most `L` has norm at most `(τ + 1) * L`.
-/

public section

open Finset

namespace LMLExplore

variable {ι E : Type*} [SeminormedAddCommGroup E]

/-- A sum over `s` of terms of norm at most `L` has norm at most `#s * L`. -/
theorem norm_sum_le_card_mul (s : Finset ι) {f : ι → E} {L : ℝ} (h : ∀ i ∈ s, ‖f i‖ ≤ L) :
    ‖∑ i ∈ s, f i‖ ≤ #s * L :=
  (norm_sum_le_of_le s h).trans_eq (by rw [sum_const, nsmul_eq_mul])

/-- The sum `∑ t - τ ≤ s ≤ t, f s` of the last `τ + 1` terms of a sequence up to index `t` has
norm at most `(τ + 1) * L` when the terms of index at most `t` have norm at most `L`. -/
theorem norm_sum_Icc_sub_le {f : ℕ → E} {L : ℝ} (t τ : ℕ) (h : ∀ s ≤ t, ‖f s‖ ≤ L) :
    ‖∑ s ∈ Icc (t - τ) t, f s‖ ≤ (τ + 1) * L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (h t le_rfl)
  refine (norm_sum_le_card_mul _ fun s hs ↦ h s (mem_Icc.mp hs).2).trans ?_
  gcongr
  rw [Nat.card_Icc]
  exact_mod_cast (by omega : t + 1 - (t - τ) ≤ τ + 1)

end LMLExplore
