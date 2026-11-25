/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of upper semicontinuous functions on a set

A function `f` that is upper semicontinuous on a set `s` is measurable along every measurable map
`g` with values in `s`: `f ∘ g` is measurable. This extends `UpperSemicontinuous.measurable` from
the whole space to a set, through the restriction of `f` to `s`.

## Main statements

* `UpperSemicontinuousOn.measurable_comp`: if `f` is upper semicontinuous on `s` and `g` is a
  measurable map with values in `s`, then `f ∘ g` is measurable.
-/

public section

variable {α δ γ : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
  [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ] [SecondCountableTopology δ]
  [MeasurableSpace δ] [BorelSpace δ] {mγ : MeasurableSpace γ}

/-- A function upper semicontinuous on a set `s` is measurable along every measurable map with
values in `s`. -/
theorem UpperSemicontinuousOn.measurable_comp {f : α → δ} {s : Set α}
    (hf : UpperSemicontinuousOn f s) {g : γ → α} (hg : Measurable g) (hgs : ∀ x, g x ∈ s) :
    Measurable (f ∘ g) :=
  (upperSemicontinuousOn_iff_restrict.2 hf).measurable.comp (hg.subtype_mk (h := hgs))
