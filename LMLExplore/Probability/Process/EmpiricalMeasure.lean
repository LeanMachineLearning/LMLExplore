/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import TauCeti.Probability.Process.EmpiricalMeasure

/-!
# Products of empirical measures

The i.i.d. law of `n` draws from the empirical measure of a finite population `y : κ → α`
(Tau Ceti's `TauCeti.Probability.empiricalMeasureOfFintype`) is the law of `y ∘ i` for an
index map `i : ι → κ` drawn uniformly. So the expectation of a function `H` of the `n` draws is
the V-statistic `(card κ)⁻ⁿ ∑_{i : ι → κ} H (y ∘ i)` of `H`.

## Main statements

* `TauCeti.Probability.lintegral_pi_empiricalMeasureOfFintype`: the expectation of `H` under the
  i.i.d. law of the empirical measure is the V-statistic of `H`.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace TauCeti.Probability

variable {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [Nonempty κ]

/-- The expectation of `H` under the i.i.d. law of the empirical measure of a finite population
`y : κ → α` is the V-statistic `(card κ)⁻ⁿ ∑_{i : ι → κ} H (y ∘ i)`. -/
theorem lintegral_pi_empiricalMeasureOfFintype (y : κ → α) {H : (ι → α) → ℝ≥0∞}
    (hH : Measurable H) :
    ∫⁻ x, H x ∂(Measure.pi fun _ : ι ↦ (empiricalMeasureOfFintype y : Measure α)) =
      (Fintype.card κ : ℝ≥0∞)⁻¹ ^ Fintype.card ι * ∑ i : ι → κ, H (y ∘ i) := by
  let _ : MeasurableSpace κ := ⊤
  have : DiscreteMeasurableSpace κ := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have hy : Measurable y := .of_discrete
  rw [empiricalMeasureOfFintype_eq_map_uniformOn, ← Measure.pi_map_pi fun _ ↦ hy.aemeasurable,
    lintegral_map hH .of_discrete, lintegral_fintype, Finset.mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [Measure.pi_singleton, ProbabilityTheory.uniformOn_univ, Measure.count_singleton,
    prod_const, card_univ, ENNReal.div_eq_inv_mul, mul_one, Function.comp_def]
  rw [mul_comm]

end TauCeti.Probability
