/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Measurability of inverse-weighted evaluations

## Main statements

* `MeasureTheory.measurable_div_apply`: for a finite type `α` with measurable singletons and
  `c : α → G`, the function `(p, b) ↦ c b / p b` on `(α → G) × α` is measurable.
-/

public section

namespace MeasureTheory

variable {α G : Type*} [MeasurableSpace α] [Finite α] [MeasurableSingletonClass α] [Div G]
  [MeasurableSpace G] [MeasurableDiv G]

/-- For a finite type `α` with measurable singletons and `c : α → G`, the function
`(p, b) ↦ c b / p b` on `(α → G) × α` is measurable. Evaluated at the weights and the action of a
round of a bandit algorithm, it is an inverse-weighted function of the action. -/
lemma measurable_div_apply (c : α → G) :
    Measurable fun z : (α → G) × α ↦ c z.2 / z.1 z.2 :=
  measurable_from_prod_countable_left fun b ↦
    (measurable_const_div (c b)).comp (measurable_pi_apply b)

end MeasureTheory
