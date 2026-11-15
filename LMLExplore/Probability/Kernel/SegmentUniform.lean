/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# The uniform law on a segment

The kernel `ProbabilityTheory.Kernel.segmentUniform : Kernel ℝ (ℝ × ℝ)` maps `s` to the law of
`(u * s, (1 - u) * s)` for `u` uniform on `[0, 1]`: for `s ≥ 0`, the first coordinate is uniform
on `[0, s]` and the two coordinates add up to `s`. It is the conditional law given the sum of a
pair of independent variables whose first coordinate is, given the sum, uniform on `[0, s]`, as
for two independent exponential variables with a common rate.

## Main definitions

* `ProbabilityTheory.Kernel.segmentUniform`: the uniform law on the segment of the pairs with
  sum `s`.

## Main statements

* `ProbabilityTheory.Kernel.segmentUniform_apply`: its value at `s` as an image of
  `uniformMeasure 0 1`.
* `ProbabilityTheory.Kernel.segmentUniform_comp`: its composition with a law of the sum.
* `ProbabilityTheory.Kernel.ae_add_segmentUniform`: under `Kernel.segmentUniform s`, the
  coordinates add up to `s`.
-/

public section

open MeasureTheory TauCeti.Probability

namespace ProbabilityTheory

/-- **The uniform law on a segment**: for `s : ℝ`, the law of `(u * s, (1 - u) * s)` for `u`
uniform on `[0, 1]`. For `s ≥ 0`, its first coordinate is uniform on `[0, s]` and the two
coordinates add up to `s`. -/
noncomputable def Kernel.segmentUniform : Kernel ℝ (ℝ × ℝ) :=
  (Kernel.id ×ₖ Kernel.const ℝ (uniformMeasure 0 1)).map fun p ↦ (p.2 * p.1, (1 - p.2) * p.1)

/-- The uniform law on a segment is a Markov kernel. -/
instance Kernel.isMarkovKernel_segmentUniform : IsMarkovKernel Kernel.segmentUniform := by
  unfold Kernel.segmentUniform
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The uniform law on the segment of the pairs with sum `s`. -/
@[simp]
theorem Kernel.segmentUniform_apply (s : ℝ) :
    Kernel.segmentUniform s = (uniformMeasure 0 1).map fun u ↦ (u * s, (1 - u) * s) := by
  rw [Kernel.segmentUniform, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The mixture of the uniform laws on the segments against a law `ν` of the sum is the image of
`uniformMeasure 0 1 ⊗ ν` under `(u, s) ↦ (u * s, (1 - u) * s)`. -/
theorem Kernel.segmentUniform_comp (ν : Measure ℝ) [SFinite ν] :
    Kernel.segmentUniform ∘ₘ ν =
      ((uniformMeasure 0 1).prod ν).map fun p ↦ (p.1 * p.2, (1 - p.1) * p.2) := by
  rw [Kernel.segmentUniform, ← Measure.map_comp _ _ (by fun_prop), ← Measure.compProd_eq_comp_prod,
    Measure.compProd_const, ← Measure.prod_swap, Measure.map_map (by fun_prop) measurable_swap]
  rfl

/-- Under the uniform law on the segment of the pairs with sum `s`, the coordinates add up to
`s`. -/
theorem Kernel.ae_add_segmentUniform (s : ℝ) : ∀ᵐ x ∂Kernel.segmentUniform s, x.1 + x.2 = s := by
  rw [Kernel.segmentUniform_apply,
    ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact ae_of_all _ fun u ↦ by ring

end ProbabilityTheory
