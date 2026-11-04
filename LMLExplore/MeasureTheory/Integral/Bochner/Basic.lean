/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expectation of an almost sure bound on a finite sum

## Main statements

* `MeasureTheory.integral_sum_le_add_mul_of_ae_le`: under a probability measure, an almost sure
  bound `∑ i ∈ s, Z i ≤ B + c ∑ i ∈ s, V i` with `c ≥ 0` gives `∫ ∑ i ∈ s, Z i ∂P ≤ B + c C` when
  the expectations of the `V i` sum to at most `C`.
-/

public section

open Finset

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {s : Finset ι}

/-- If almost surely `∑ i ∈ s, Z i ≤ B + c ∑ i ∈ s, V i` with `c ≥ 0`, where the `Z i` and `V i`
are integrable and the expectations of the `V i` sum to at most `C`, then the expectation of
`∑ i ∈ s, Z i` is at most `B + c C`. The analyses of Exp3 and Exp4 use it to turn pathwise bounds
into bounds on the expected estimated regret. -/
lemma integral_sum_le_add_mul_of_ae_le {Z V : ι → Ω → ℝ} {B c C : ℝ} (hc : 0 ≤ c)
    (hZ : ∀ i ∈ s, Integrable (Z i) P) (hV : ∀ i ∈ s, Integrable (V i) P)
    (hVC : ∑ i ∈ s, ∫ ω, V i ω ∂P ≤ C)
    (hZV : ∀ᵐ ω ∂P, ∑ i ∈ s, Z i ω ≤ B + c * ∑ i ∈ s, V i ω) :
    ∫ ω, ∑ i ∈ s, Z i ω ∂P ≤ B + c * C := by
  calc ∫ ω, ∑ i ∈ s, Z i ω ∂P
  _ ≤ ∫ ω, B + c * ∑ i ∈ s, V i ω ∂P := by
      refine integral_mono_ae (integrable_finsetSum _ hZ)
        ((integrable_const _).add ((integrable_finsetSum _ hV).const_mul _)) ?_
      filter_upwards [hZV] with ω hω
      exact hω
  _ = B + c * ∑ i ∈ s, ∫ ω, V i ω ∂P := by
      rw [integral_add (integrable_const _) ((integrable_finsetSum _ hV).const_mul _),
        integral_const_mul, integral_finsetSum _ hV, integral_const, probReal_univ, one_smul]
  _ ≤ B + c * C := by gcongr

end MeasureTheory
