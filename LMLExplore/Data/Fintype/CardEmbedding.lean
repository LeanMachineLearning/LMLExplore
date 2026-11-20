/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Sums over all maps bounded by the injective maps

There are `|κ| (|κ| - 1) ⋯ (|κ| - |ι| + 1)` injective maps `ι → κ` (Mathlib's
`Fintype.card_embedding_eq`). So if a nonnegative function of the maps `ι → κ` takes the value
`a` at every injective map, its sum over all maps is at least that number times `a`.

## Main statements

* `Fintype.descFactorial_card_nsmul_le_sum`: `(|κ|.descFactorial |ι|) • a ≤ ∑ i : ι → κ, f i`.
-/

public section

open Finset

namespace Fintype

variable {ι κ M : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]

/-- If a nonnegative function `f` of the maps `ι → κ` takes the value `a` at every injective map,
its sum over all maps is at least `|κ| (|κ| - 1) ⋯ (|κ| - |ι| + 1) • a`, the number of injective
maps times `a`. -/
theorem descFactorial_card_nsmul_le_sum {f : (ι → κ) → M} {a : M} (hf : ∀ i, 0 ≤ f i)
    (ha : ∀ e : ι ↪ κ, f e = a) :
    (card κ).descFactorial (card ι) • a ≤ ∑ i, f i := by
  classical
  calc (card κ).descFactorial (card ι) • a
  _ = ∑ e : ι ↪ κ, f e := by simp [ha, card_embedding_eq]
  _ = ∑ i ∈ univ.map ⟨fun e : ι ↪ κ ↦ (e : ι → κ), DFunLike.coe_injective⟩, f i := by
    rw [sum_map, Function.Embedding.coeFn_mk]
  _ ≤ ∑ i, f i := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ hf i

end Fintype
