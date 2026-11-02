/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Lebesgue integral of an `ℕ∞`-valued function

The expectation of a random variable `f` with values in `ℕ∞`, such as a random time, is the sum of
its tail probabilities: `∫⁻ f ∂μ = ∑ n, μ {n < f}` (the discrete layer cake formula). As a
consequence, a random time that is at most `T` on an event `E T` for every `T ≥ T₀` has
expectation at most `T₀ + ∑_{T ≥ T₀} μ (E T)ᶜ` under a probability measure. This is the form in
which upper bounds on the expected stopping time of sequential algorithms are proved: the events
`E T` are good events of the first `T` rounds on which the algorithm must have stopped.

## Main statements

* `MeasureTheory.lintegral_toENNReal_eq_tsum_measure_lt`: `∫⁻ f ∂μ = ∑' n, μ {n < f}`.
* `MeasureTheory.lintegral_toENNReal_le_add_tsum_measure_compl`: if `f ≤ T` on `E T` for every
  `T ≥ T₀`, then `∫⁻ f ∂μ ≤ T₀ + ∑' T, μ (E (T + T₀))ᶜ`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → ℕ∞}

/-- **Tail-sum formula** (discrete layer cake formula): the integral of a function with values in
`ℕ∞` is the sum of the measures of the sets where it exceeds each natural number. -/
lemma lintegral_toENNReal_eq_tsum_measure_lt (hf : AEMeasurable f μ) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < f ω} := by
  have h_meas (n : ℕ) : NullMeasurableSet {ω | (n : ℕ∞) < f ω} μ :=
    hf.nullMeasurableSet_preimage (s := Set.Ioi (n : ℕ∞)) .of_discrete
  -- Pointwise, `f ω` is the number of natural numbers below it.
  have h_card (k : ℕ∞) : (k : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < k then 1 else 0 := by
    induction k using ENat.recTopCoe with
    | top => simp
    | coe k =>
      rw [tsum_eq_sum (s := Finset.range k) fun n hn ↦ by simpa using hn]
      simp [Finset.filter_true_of_mem fun n hn ↦ Finset.mem_range.1 hn]
  calc ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ
  _ = ∫⁻ ω, ∑' n : ℕ, {ω | (n : ℕ∞) < f ω}.indicator 1 ω ∂μ :=
    lintegral_congr fun ω ↦ by simp [h_card (f ω), Set.indicator_apply]
  _ = ∑' n : ℕ, μ {ω | (n : ℕ∞) < f ω} := by
    rw [lintegral_tsum (f := fun (n : ℕ) ↦ {ω | (n : ℕ∞) < f ω}.indicator 1)
      fun n ↦ aemeasurable_one.indicator₀ (h_meas n)]
    exact tsum_congr fun n ↦ lintegral_indicator_one₀ (h_meas n)

/-- If a function with values in `ℕ∞` is at most `T` on a set `E T` for every `T ≥ T₀`, then its
integral under a probability measure is at most `T₀ + ∑_{T ≥ T₀} μ (E T)ᶜ`. For a random time,
`E T` is an event on which it is at most `T`. -/
lemma lintegral_toENNReal_le_add_tsum_measure_compl [IsZeroOrProbabilityMeasure μ]
    (hf : AEMeasurable f μ) {E : ℕ → Set Ω} {T₀ : ℕ} (hE : ∀ T ≥ T₀, ∀ ω ∈ E T, f ω ≤ T) :
    ∫⁻ ω, (f ω : ℝ≥0∞) ∂μ ≤ T₀ + ∑' T, μ (E (T + T₀))ᶜ := by
  rw [lintegral_toENNReal_eq_tsum_measure_lt hf,
    ← Summable.sum_add_tsum_nat_add' (k := T₀) ENNReal.summable]
  gcongr with T
  · -- The first `T₀` tail probabilities are at most `1`.
    calc ∑ n ∈ Finset.range T₀, μ {ω | (n : ℕ∞) < f ω}
    _ ≤ ∑ n ∈ Finset.range T₀, 1 := Finset.sum_le_sum fun _ _ ↦ prob_le_one
    _ = T₀ := by simp
  · -- From `T₀` on, `f` exceeds `T` only outside `E T`.
    exact fun ω hω hωE ↦ (hE (T + T₀) (Nat.le_add_left _ _) ω hωE).not_gt hω

end MeasureTheory
