/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.UnitInterval

/-!
# Integrability on the unit interval

The coercion of `unitInterval` to `ℝ` takes values in `[0, 1]`, so it is integrable under every
finite measure on `unitInterval`.

## Main statements

* `unitInterval.integrable_subtypeVal`: the coercion `unitInterval → ℝ` is integrable under every
  finite measure.
-/

public section

open MeasureTheory
open scoped unitInterval

namespace unitInterval

/-- The coercion of `[0, 1]` to `ℝ` is integrable under every finite measure. -/
theorem integrable_subtypeVal (μ : Measure I) [IsFiniteMeasure μ] :
    Integrable (fun x : I ↦ (x : ℝ)) μ :=
  Integrable.of_mem_Icc 0 1 measurable_subtypeVal.aemeasurable (ae_of_all _ fun x : I ↦ x.property)

end unitInterval
