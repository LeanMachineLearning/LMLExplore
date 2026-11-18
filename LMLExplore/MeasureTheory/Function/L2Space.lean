/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square-integrability of the distance to a point

For a random variable `X` in a normed space `E` that is only a.e.-measurable, with
`𝔼 ‖X‖² < ∞`, the squared distance `‖c - X‖²` to any point `c` is integrable. Without second
countability of `E`, `X` need not be a.e.-strongly measurable, so this does not follow from
`MeasureTheory.MemLp` of `X` itself; the hypotheses are stated on the real random variable
`‖X‖` instead.

## Main statements

* `MeasureTheory.integrable_norm_const_sub_sq`: `𝔼 ‖c - X‖² < ∞` for an a.e.-measurable `X`
  with `𝔼 ‖X‖² < ∞`, under a finite measure.
-/

public section

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- **The squared distance to a point is integrable**: under a finite measure, if `X` is
a.e.-measurable and `‖X‖` is square-integrable, then `x ↦ ‖c - X x‖²` is integrable for every
point `c`. -/
theorem integrable_norm_const_sub_sq {X : Ω → E} (hX : AEMeasurable X μ)
    (hX' : MemLp (fun x ↦ ‖X x‖) 2 μ) (c : E) : Integrable (fun x ↦ ‖c - X x‖ ^ 2) μ :=
  ((memLp_const ‖c‖).add hX').of_le (hX.const_sub c).norm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (norm_nonneg _), Pi.add_apply,
        Real.norm_of_nonneg (by positivity)]
      exact norm_sub_le _ _) |>.integrable_sq

end MeasureTheory
