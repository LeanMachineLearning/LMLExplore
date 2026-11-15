/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import LMLExplore.MeasureTheory.Integral.Lebesgue.Add

/-!
# Markov's inequality for counts

If each event of a finite family has probability at most `η`, then the expected number of events
that occur is at most `#S * η`, so by Markov's inequality at least `m` of them occur with
probability at most `#S * η / m`. In the same way, a count `U` whose integral, scaled by `b - a`,
is at most `C` reaches `K` with probability at most `C / ((b - a) K)`; this is the form in which
Doob's upcrossing inequality bounds the probability of many upcrossings of `[a, b]`.

## Main statements

* `MeasureTheory.measure_le_card_filter_le`: if each of the events `E b`, `b ∈ S`, has probability
  at most `η` and `#S ≤ m c` with `m ≠ 0`, then at least `m` of these events occur with probability
  at most `c η`.
* `MeasureTheory.measure_natCast_le_le_of_mul_lintegral_le`: if `(b - a) ∫⁻ U ≤ C` and
  `C ≤ (b - a) K ε`, then `U` is at least `K` with probability at most `ε`.
-/

public section

open Finset
open scoped ENNReal NNReal

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

/-- **Markov's inequality for a count.** If `(b - a) ∫⁻ U ≤ C` and `C ≤ (b - a) K ε`, with `a < b`
and `K ≠ 0`, then `U` is at least `K` with probability at most `ε`. -/
lemma measure_natCast_le_le_of_mul_lintegral_le {U : Ω → ℝ≥0∞} (hU : AEMeasurable U P) {a b : ℝ}
    (hab : a < b) {K : ℕ} (hK : K ≠ 0) {C ε : ℝ≥0}
    (hUC : ENNReal.ofReal (b - a) * ∫⁻ ω, U ω ∂P ≤ C) (hC : (C : ℝ) ≤ (b - a) * K * ε) :
    P {ω | (K : ℝ≥0∞) ≤ U ω} ≤ ε := by
  set x := ENNReal.ofReal (b - a) * K
  have hx0 : x ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne' (Nat.cast_ne_zero.2 hK)
  have hxtop : x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  rw [← ENNReal.mul_le_mul_iff_right hx0 hxtop]
  calc x * P {ω | (K : ℝ≥0∞) ≤ U ω}
      = ENNReal.ofReal (b - a) * (K * P {ω | (K : ℝ≥0∞) ≤ U ω}) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal (b - a) * ∫⁻ ω, U ω ∂P := by
        gcongr
        exact mul_meas_ge_le_lintegral₀ hU _
    _ ≤ C := hUC
    _ = ENNReal.ofReal C := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal ((b - a) * K * ε) := ENNReal.ofReal_le_ofReal hC
    _ = x * ε := by
        rw [ENNReal.ofReal_mul (mul_nonneg (sub_nonneg.2 hab.le) (Nat.cast_nonneg _)),
          ENNReal.ofReal_mul (sub_nonneg.2 hab.le), ENNReal.ofReal_natCast,
          ENNReal.ofReal_coe_nnreal]

end MeasureTheory
