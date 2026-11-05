/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Add

/-!
# Markov's inequality for the number of events that occur

If each event of a finite family has probability at most `η`, then the expected number of events
that occur is at most `#S * η`, so by Markov's inequality at least `m` of them occur with
probability at most `#S * η / m`.

## Main statements

* `MeasureTheory.measure_le_card_filter_le`: if each of the events `E b`, `b ∈ S`, has probability
  at most `η` and `#S ≤ m c` with `m ≠ 0`, then at least `m` of these events occur with probability
  at most `c η`.
-/

public section

open Finset
open scoped ENNReal

namespace MeasureTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Markov's inequality for a number of events.** If each of the events `E b`, `b ∈ S`, has
probability at most `η` and `#S ≤ m c` with `m ≠ 0`, then at least `m` of these events occur with
probability at most `c η`. -/
lemma measure_le_card_filter_le {E : ι → Set Ω} [∀ b, DecidablePred (· ∈ E b)] {S : Finset ι}
    (hE : ∀ b ∈ S, MeasurableSet (E b)) {η : ℝ≥0∞} (h : ∀ b ∈ S, P (E b) ≤ η) {m c : ℕ}
    (hm : m ≠ 0) (hc : #S ≤ m * c) :
    P {ω | m ≤ #{b ∈ S | ω ∈ E b}} ≤ c * η := by
  -- The number of events that occur.
  set N : Ω → ℝ≥0∞ := fun ω ↦ ∑ b ∈ S, (E b).indicator 1 ω with hN
  have h_eq : {ω | m ≤ #{b ∈ S | ω ∈ E b}} = {ω | (m : ℝ≥0∞) ≤ N ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hN, Set.indicator_apply, Pi.one_apply]
    rw [sum_boole]
    norm_cast
  have h_int : ∫⁻ ω, N ω ∂P ≤ #S * η := by
    rw [hN, lintegral_finsetSum_indicator_one hE]
    calc ∑ b ∈ S, P (E b) ≤ ∑ _b ∈ S, η := sum_le_sum h
    _ = #S * η := by simp
  have h_markov := (mul_meas_ge_le_lintegral₀ (μ := P) (Finset.measurable_sum _ fun b hb ↦
    measurable_one.indicator (hE b hb)).aemeasurable (m : ℝ≥0∞)).trans h_int
  have hSc : (#S : ℝ≥0∞) * η ≤ m * (c * η) := by
    rw [← mul_assoc]
    gcongr
    exact_mod_cast hc
  rw [h_eq]
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hm) (by simp)).1 (h_markov.trans hSc)

end MeasureTheory
