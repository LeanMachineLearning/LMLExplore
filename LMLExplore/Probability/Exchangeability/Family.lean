/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Probability.Exchangeability.Family

/-!
# Exchangeability of a block of a family, given the rest

Let `X : κ ⊕ ι → Ω → α` be an exchangeable family, in Tau Ceti's sense
(`TauCeti.Probability.ExchangeableFamily`). Then the coordinates indexed by `ι` remain exchangeable
when each of them is paired with the whole block indexed by `κ`: the family
`j ↦ ((X (inl k))ₖ, X (inr j))` is exchangeable. In words, permuting the coordinates of one block
does not change the joint law with the other block. This is the exchangeability that split and
cross-conformal prediction use: the calibration points and the test point stay exchangeable once
the training set proper is known.

## Main statements

* `TauCeti.Probability.ExchangeableFamily.prodMk_inl_inr`: the coordinates indexed by `ι`, each
  paired with the block indexed by `κ`, form an exchangeable family.
-/

public section

open MeasureTheory

namespace TauCeti.Probability

variable {Ω α κ ι : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- In an exchangeable family indexed by `κ ⊕ ι`, the coordinates indexed by `ι`, each paired with
the whole block of the coordinates indexed by `κ`, form an exchangeable family. -/
theorem ExchangeableFamily.prodMk_inl_inr [Countable κ] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : κ ⊕ ι → Ω → α} (h : ExchangeableFamily μ X) (hX : ∀ i, Measurable (X i)) :
    ExchangeableFamily μ fun j ω ↦ ((fun k ↦ X (.inl k) ω), X (.inr j) ω) := by
  refine ExchangeableFamily.intro fun m a b ha hb ↦ ?_
  -- Both block laws are images of the laws of `X` along the injections `Sum.map id a` and
  -- `Sum.map id b` of `κ ⊕ Fin m`, under one measurable map.
  let g : (κ ⊕ Fin m → α) → Fin m → (κ → α) × α := fun v j ↦ (fun k ↦ v (.inl k), v (.inr j))
  have hg : Measurable g := by fun_prop
  have hlaw (c : Fin m → ι) : blockLaw μ (fun j ω ↦ ((fun k ↦ X (.inl k) ω), X (.inr j) ω)) c =
      (μ.map fun ω i ↦ X (Sum.map id c i) ω).map g := by
    rw [blockLaw_def, Measure.map_map hg (by fun_prop)]
    simp [g, Function.comp_def]
  rw [hlaw, hlaw, h.map_eq_of_injective (fun i ↦ (hX i).aemeasurable)
    (Function.injective_id.sumMap ha) (Function.injective_id.sumMap hb)]

end TauCeti.Probability
