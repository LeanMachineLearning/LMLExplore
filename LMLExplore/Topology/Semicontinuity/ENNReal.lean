/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Semicontinuity of functions to `ℝ≥0∞`

Multiplication by a finite constant `c : ℝ≥0∞` is continuous and monotone, so it preserves lower
and upper semicontinuity of functions to `ℝ≥0∞`. Rescaling a rate function of a large deviation
principle by a positive weight uses the first, and rescaling a p-to-e calibrator the second.

## Main statements

* `LowerSemicontinuous.ennreal_const_mul`: if `f` is lower semicontinuous and `c ≠ ∞`, then
  `y ↦ c * f y` is lower semicontinuous.
* `UpperSemicontinuous.ennreal_const_mul`: if `f` is upper semicontinuous and `c ≠ ∞`, then
  `y ↦ c * f y` is upper semicontinuous.
-/

public section

open scoped ENNReal

variable {Y : Type*} [TopologicalSpace Y] {f : Y → ℝ≥0∞}

/-- A finite multiple `y ↦ c * f y` of a lower semicontinuous function `f` to `ℝ≥0∞` is lower
semicontinuous. -/
theorem LowerSemicontinuous.ennreal_const_mul (hf : LowerSemicontinuous f) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : LowerSemicontinuous fun y ↦ c * f y :=
  (ENNReal.continuous_const_mul hc).comp_lowerSemicontinuous hf fun _ _ h ↦ by dsimp only; gcongr

/-- A finite multiple `y ↦ c * f y` of an upper semicontinuous function `f` to `ℝ≥0∞` is upper
semicontinuous. -/
theorem UpperSemicontinuous.ennreal_const_mul (hf : UpperSemicontinuous f) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : UpperSemicontinuous fun y ↦ c * f y :=
  (ENNReal.continuous_const_mul hc).comp_upperSemicontinuous hf fun _ _ h ↦ by dsimp only; gcongr
