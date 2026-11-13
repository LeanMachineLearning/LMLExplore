/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import TauCeti.Probability.Process.PathLaw.Filtration

/-!
# Measurability of coordinates for the natural filtration of a product

Mathlib's natural filtration `MeasureTheory.Filtration.piLE` of a product `Π i, X i` contains at
time `i` the measurable sets that depend only on the coordinates `≤ i`. Tau Ceti's
`MeasureTheory.Filtration.adapted_piLE` states that the coordinate `x ↦ x i` is measurable at time
`i`. This file records that every earlier coordinate `x ↦ x j`, `j ≤ i`, is measurable at time `i`.

## Main statements

* `MeasureTheory.Filtration.measurable_eval_piLE`: for `j ≤ i`, the coordinate `x ↦ x j` is
  measurable for `piLE i`.
-/

public section

namespace MeasureTheory.Filtration

variable {ι : Type*} [Preorder ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- For `j ≤ i`, the coordinate `x ↦ x j` of a product `Π i, X i` is measurable for its natural
filtration `piLE` at time `i`. -/
theorem measurable_eval_piLE {i j : ι} (hji : j ≤ i) :
    Measurable[piLE (X := X) i] fun x : Π i, X i ↦ x j :=
  (adapted_piLE (X := X) j).mono (piLE.mono hji) le_rfl

end MeasureTheory.Filtration
