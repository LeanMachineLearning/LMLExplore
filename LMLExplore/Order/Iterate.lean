/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Order.Iterate

/-!
# Iterates of monotone maps

## Main statements

* `Monotone.iterate_le_of_map_le_succ`: if `f` is monotone and `f (u k) ≤ u (k + 1)` for all `k`,
  then `f^[k] (u 0) ≤ u k`.
-/

public section

open Function

/-- If `f` is monotone and `f (u k) ≤ u (k + 1)` for all `k`, then `f^[k] (u 0) ≤ u k`. -/
theorem Monotone.iterate_le_of_map_le_succ {α : Type*} [Preorder α] {f : α → α} {u : ℕ → α}
    (hf : Monotone f) (h : ∀ k, f (u k) ≤ u (k + 1)) (k : ℕ) : f^[k] (u 0) ≤ u k :=
  hf.seq_le_seq k (x := fun n ↦ f^[n] (u 0)) le_rfl (fun n _ ↦ (iterate_succ_apply' f n (u 0)).le)
    fun n _ ↦ h n
