/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Process.Adapted

/-!
# Adapted products

A product `M₀ * ∏ k < n, F k` is adapted to a filtration `ℱ` indexed by `ℕ` when `M₀` is
`ℱ 0`-measurable and each factor `F k` is `ℱ (k + 1)`-measurable. Such products are the wealth
processes of a gambler who reinvests at every round.

## Main statements

* `MeasureTheory.adapted_mul_prod_range`: the process `n ↦ M₀ * ∏ k < n, F k` is adapted.
-/

public section

open Finset

namespace MeasureTheory

variable {Ω β : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace β] [CommMonoid β]
  [MeasurableMul₂ β] {ℱ : Filtration ℕ mΩ}

/-- The process `n ↦ M₀ * ∏ k < n, F k` is adapted when `M₀` is `ℱ 0`-measurable and each factor
`F k` is `ℱ (k + 1)`-measurable. -/
theorem adapted_mul_prod_range {M₀ : Ω → β} (hM₀ : Measurable[ℱ 0] M₀) {F : ℕ → Ω → β}
    (hF : ∀ k, Measurable[ℱ (k + 1)] (F k)) :
    Adapted ℱ (fun n ω ↦ M₀ ω * ∏ k ∈ range n, F k ω) := fun n ↦
  (hM₀.mono (ℱ.mono n.zero_le) le_rfl).mul <| Finset.measurable_fun_prod _ fun k hk ↦
    (hF k).mono (ℱ.mono (mem_range.1 hk)) le_rfl

end MeasureTheory
