/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The law of a statistic under a composition with a kernel carried by its fibers

If a Markov kernel `κ : Kernel 𝓨 Ω` is carried by the fibers of a statistic `T : Ω → 𝓨`, that is,
`κ y` is carried by `T ⁻¹' {y}`, then the law of `T` under `κ ∘ₘ ν` is `ν`: the composition with
`κ` draws a point of the fiber of each `y`.

## Main statements

* `ProbabilityTheory.map_comp_eq_of_ae_eq`: `(κ ∘ₘ ν).map T = ν`.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω 𝓨 : Type*} {mΩ : MeasurableSpace Ω} {m𝓨 : MeasurableSpace 𝓨} {T : Ω → 𝓨}
  {κ : Kernel 𝓨 Ω}

/-- If `κ y` is a probability measure carried by the fiber `T ⁻¹' {y}` for `ν`-almost every `y`,
the law of `T` under `κ ∘ₘ ν` is `ν`. -/
theorem map_comp_eq_of_ae_eq [IsMarkovKernel κ] (hT : Measurable T) {ν : Measure 𝓨}
    (hκ : ∀ᵐ y ∂ν, ∀ᵐ x ∂κ y, T x = y) : (κ ∘ₘ ν).map T = ν := by
  ext A hA
  rw [Measure.map_apply hT hA, Measure.bind_apply (hT hA) κ.aemeasurable,
    ← lintegral_indicator_one hA]
  refine lintegral_congr_ae ?_
  filter_upwards [hκ] with y hκ
  by_cases hy : y ∈ A
  · rw [indicator_of_mem hy, Pi.one_apply, ← measure_univ (μ := κ y)]
    refine measure_congr ?_
    filter_upwards [hκ] with x hx
    simp [hx, hy]
  · rw [indicator_of_notMem hy]
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hκ] with x hx
    simpa [hx] using hy

end ProbabilityTheory
