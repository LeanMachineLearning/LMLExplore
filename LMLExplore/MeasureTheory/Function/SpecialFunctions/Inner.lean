/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Measurability of the inner product with a fixed vector

Mathlib's `Measurable.const_inner` assumes that `E` is second countable, since it is derived from
the measurability of the inner product as a function of two variables. The inner product with a
fixed vector is continuous, so its composition with a measurable function is measurable without
that assumption.

## Main statements

* `Measurable.const_inner'`: the inner product of a fixed vector with a measurable function is
  measurable, without second countability.
-/

public section

open scoped InnerProductSpace

variable {α 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {_ : MeasurableSpace α}

/-- The inner product of a fixed vector with a measurable function is measurable. Unlike
`Measurable.const_inner`, this needs no second countability of `E`, since the inner product with a
fixed vector is continuous. -/
theorem Measurable.const_inner' {f : α → E} (hf : Measurable f) (c : E) :
    Measurable fun t ↦ ⟪c, f t⟫_𝕜 :=
  (continuous_const.inner continuous_id).measurable.comp hf
