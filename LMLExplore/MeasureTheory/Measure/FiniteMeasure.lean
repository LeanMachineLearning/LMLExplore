/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# The mass of sums and multiples of finite measures

The total mass `MeasureTheory.FiniteMeasure.mass` is additive and commutes with scalar
multiplication.

## Main statements

* `MeasureTheory.FiniteMeasure.mass_add`: the mass of a sum is the sum of the masses.
* `MeasureTheory.FiniteMeasure.mass_smul`: the mass of `c • μ` is `c • μ.mass`.
-/

public section

open scoped NNReal ENNReal

namespace MeasureTheory.FiniteMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The mass of a sum of finite measures is the sum of their masses. -/
@[simp]
theorem mass_add (μ ν : FiniteMeasure Ω) : (μ + ν).mass = μ.mass + ν.mass := by
  rw [← ENNReal.coe_inj]
  push_cast
  simp only [ennreal_mass, toMeasure_add, add_apply]

/-- The mass of a scalar multiple of a finite measure. -/
@[simp]
theorem mass_smul {R : Type*} [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (μ : FiniteMeasure Ω) :
    (c • μ).mass = c • μ.mass := by
  rw [← ENNReal.coe_inj, ENNReal.coe_smul, ennreal_mass, ennreal_mass, toMeasure_smul,
    smul_apply]

end MeasureTheory.FiniteMeasure
