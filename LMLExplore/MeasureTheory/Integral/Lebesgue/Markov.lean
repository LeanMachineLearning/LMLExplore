/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import TauCeti.MeasureTheory.Integral.Lebesgue.Encard

/-!
# Markov's inequality for counts and for nonincreasing functions

If each event of a finite family has probability at most `η`, then by Markov's inequality for the
number of events that occur (`MeasureTheory.measure_lt_card_filter_le` of Tau Ceti), at least `m`
of them occur with probability at most `#S * η / m`. In the same way, a count `U` whose integral,
scaled by `d > 0`, is at most `C` reaches `K` with probability at most `C / (d K)`. A function
nonincreasing on `[a, b]` is at least `f u` on `[a, u]`, so `(u - a) f u` is at most its integral
over `[a, b]`.

## Main statements

* `MeasureTheory.measure_le_card_filter_le`: if each of the events `E b`, `b ∈ S`, has probability
  at most `η` and `#S ≤ m c` with `m ≠ 0`, then at least `m` of these events occur with probability
  at most `c η`.
* `MeasureTheory.measure_natCast_le_le_of_mul_lintegral_le`: if `d ∫⁻ U ≤ C` and `C ≤ d K ε`
  with `0 < d`, then `U` is at least `K` with probability at most `ε`.
* `AntitoneOn.ofReal_sub_mul_le_setLIntegral_Icc`: a function nonincreasing on `[a, b]` satisfies
  `(u - a) f u ≤ ∫⁻_{[a, b]} f` for `u ∈ [a, b]`, so that `f u` is at most `∫⁻_{[0, 1]} f / u` on
  `[0, 1]`.
-/

public section

open Finset
open scoped ENNReal NNReal

namespace MeasureTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Markov's inequality for a number of events.** If each of the events `E b`, `b ∈ S`, has
probability at most `η` and `#S ≤ m c` with `m ≠ 0`, then at least `m` of these events occur with
probability at most `c η`. This is Tau Ceti's `measure_lt_card_filter_le` with threshold `m - 1`
and a common bound on the measures of the events. -/
lemma measure_le_card_filter_le {E : ι → Set Ω} [∀ b, DecidablePred (· ∈ E b)] {S : Finset ι}
    {η : ℝ≥0∞} (h : ∀ b ∈ S, P (E b) ≤ η) {m c : ℕ} (hm : m ≠ 0) (hc : #S ≤ m * c) :
    P {ω | m ≤ #{b ∈ S | ω ∈ E b}} ≤ c * η := by
  have h_sub : {ω | m ≤ #{b ∈ S | ω ∈ E b}} ⊆ {ω | m - 1 < #{b ∈ S | ω ∈ E b}} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    omega
  refine (measure_mono h_sub).trans
    ((measure_lt_card_filter_le S E _).trans (ENNReal.div_le_of_le_mul' ?_))
  calc ∑ b ∈ S, P (E b) ≤ #S • η := sum_le_card_nsmul _ _ _ h
  _ = #S * η := nsmul_eq_mul _ _
  _ ≤ (↑(m - 1) + 1) * c * η := by
    gcongr
    rw [← Nat.cast_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)]
    exact_mod_cast hc
  _ = _ := mul_assoc _ _ _

/-- **Markov's inequality for a count.** If `d ∫⁻ U ≤ C` and `C ≤ d K ε`, with `0 < d` and
`K ≠ 0`, then `U` is at least `K` with probability at most `ε`. -/
lemma measure_natCast_le_le_of_mul_lintegral_le {U : Ω → ℝ≥0∞} (hU : AEMeasurable U P) {d : ℝ}
    (hd : 0 < d) {K : ℕ} (hK : K ≠ 0) {C ε : ℝ≥0}
    (hUC : ENNReal.ofReal d * ∫⁻ ω, U ω ∂P ≤ C) (hC : (C : ℝ) ≤ d * K * ε) :
    P {ω | (K : ℝ≥0∞) ≤ U ω} ≤ ε := by
  set x := ENNReal.ofReal d * K
  have hx0 : x ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (Nat.cast_ne_zero.2 hK)
  have hxtop : x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  rw [← ENNReal.mul_le_mul_iff_right hx0 hxtop]
  calc x * P {ω | (K : ℝ≥0∞) ≤ U ω}
      = ENNReal.ofReal d * (K * P {ω | (K : ℝ≥0∞) ≤ U ω}) := mul_assoc _ _ _
    _ ≤ ENNReal.ofReal d * ∫⁻ ω, U ω ∂P := by
        gcongr
        exact mul_meas_ge_le_lintegral₀ hU _
    _ ≤ C := hUC
    _ = ENNReal.ofReal C := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (d * K * ε) := ENNReal.ofReal_le_ofReal hC
    _ = x * ε := by
        rw [ENNReal.ofReal_mul (mul_nonneg hd.le (Nat.cast_nonneg _)),
          ENNReal.ofReal_mul hd.le, ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]

end MeasureTheory

namespace AntitoneOn

open MeasureTheory

/-- **Markov's inequality for a nonincreasing function**: a function `f` nonincreasing on `[a, b]`
is at least `f u` on `[a, u]`, so `(u - a) f u ≤ ∫⁻_{[a, b]} f` for `u ∈ [a, b]`. -/
theorem ofReal_sub_mul_le_setLIntegral_Icc {f : ℝ → ℝ≥0∞} {a b u : ℝ}
    (hf : AntitoneOn f (Set.Icc a b)) (hu : u ∈ Set.Icc a b) :
    ENNReal.ofReal (u - a) * f u ≤ ∫⁻ v in Set.Icc a b, f v :=
  calc ENNReal.ofReal (u - a) * f u = ∫⁻ _ in Set.Icc a u, f u := by
        rw [setLIntegral_const, Real.volume_Icc, mul_comm]
    _ ≤ ∫⁻ v in Set.Icc a u, f v :=
        setLIntegral_mono' measurableSet_Icc fun v hv ↦ hf ⟨hv.1, hv.2.trans hu.2⟩ hu hv.2
    _ ≤ ∫⁻ v in Set.Icc a b, f v := lintegral_mono_set (Set.Icc_subset_Icc le_rfl hu.2)

end AntitoneOn
