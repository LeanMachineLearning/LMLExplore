/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Logic.Function.DependsOn

/-!
# Indicators of functions that depend on a set of coordinates

## Main statements

* `dependsOn_indicator_of_eqOn`: if membership in `A` and, on `A`, the function `f` are
  determined by the coordinates in `s`, then so is the indicator `A.indicator f`.
-/

public section

variable {ι : Type*} {α : ι → Type*} {β : Type*}

/-- If membership in `A` is determined by the coordinates in `s`, and so is `f` on `A`, then the
indicator `A.indicator f` only depends on the coordinates in `s`. -/
lemma dependsOn_indicator_of_eqOn [Zero β] {A : Set (Π i, α i)} {f : (Π i, α i) → β}
    {s : Set ι} (hA : ∀ ⦃x y : Π i, α i⦄, (∀ i ∈ s, x i = y i) → (y ∈ A ↔ x ∈ A))
    (hf : ∀ ⦃x y : Π i, α i⦄, (∀ i ∈ s, x i = y i) → x ∈ A → f y = f x) :
    DependsOn (A.indicator f) s := by
  intro x y h
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hA h).2 hx), hf h hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hA h).1 hx)]
