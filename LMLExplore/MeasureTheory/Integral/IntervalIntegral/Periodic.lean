/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Lebesgue measure on the circle has no atoms

Lebesgue measure on the circle `AddCircle T` gives measure `0` to every point, since the closed
ball of radius `0` around a point has measure `min T 0`. So countable sets are null
(`Set.Countable.measure_zero`).

## Main statements

* An instance `NullSingletonClass (volume : Measure (AddCircle T))`.
-/

public section

open MeasureTheory

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)]

/-- Lebesgue measure on the circle `AddCircle T` has no atoms. -/
instance : NullSingletonClass (volume : Measure (AddCircle T)) :=
  ⟨fun x ↦ by rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]; simp⟩

end AddCircle
