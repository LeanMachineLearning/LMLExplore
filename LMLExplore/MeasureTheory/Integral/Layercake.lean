/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Expectation of a random variable with a quadratic tail

If a real random variable `f` satisfies the tail bound `P(x < f) ≤ a / x ²` for every `x > 0`, then
the layer cake formula `E[f⁺] = ∫_0^∞ P(x < f) dx` and the bound `P(x < f) ≤ min 1 (a / x ²)` give
`E[f⁺] ≤ 2 √a`. The proof of [LS, Theorem 9.1] uses this to bound the expected amount by which the
index of an optimal arm under the MOSS algorithm falls below its mean.

## Main statements

* `MeasureTheory.lintegral_ofReal_le_two_mul_sqrt_of_measure_lt_le`: if
  `P(x < f) ≤ a / x ^ 2` for every `x > 0`, then `∫⁻ ω, ofReal (f ω) ∂P ≤ ofReal (2 √a)`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  proof of Theorem 9.1.
-/

public section

open Set Real

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {f : Ω → ℝ} {a : ℝ}

/-- **Expectation from a quadratic tail.** If a real random variable `f` on a probability space
satisfies `P(x < f) ≤ a / x ^ 2` for every `x > 0`, then the expectation of its positive part is
at most `2 √a`: `∫⁻ ω, ofReal (f ω) ∂P ≤ ofReal (2 √a)`. -/
theorem lintegral_ofReal_le_two_mul_sqrt_of_measure_lt_le (hf : AEMeasurable f P) (ha : 0 ≤ a)
    (h : ∀ x > 0, P {ω | x < f ω} ≤ ENNReal.ofReal (a / x ^ 2)) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal (2 * √a) := by
  -- the layer cake formula for the positive part of `f`
  have h_layer : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P = ∫⁻ x in Ioi 0, P {ω | x < f ω} := by
    have h_pos := lintegral_eq_lintegral_meas_lt P (f := fun ω ↦ max (f ω) 0)
      (ae_of_all _ fun _ ↦ le_max_right _ _) (hf.max aemeasurable_const)
    simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le] at h_pos
    rw [h_pos]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
    simp [lt_max_iff, hx.not_gt]
  rw [h_layer]
  rcases ha.eq_or_lt with rfl | ha
  · -- for `a = 0`, every tail probability vanishes
    calc ∫⁻ x in Ioi 0, P {ω | x < f ω}
    _ ≤ ∫⁻ _ in Ioi (0 : ℝ), 0 :=
      setLIntegral_mono measurable_const fun x hx ↦ by simpa using h x hx
    _ ≤ ENNReal.ofReal (2 * √0) := by simp
  -- split the levels at `√a`: below, bound the probability by `1`; above, by `a / x ^ 2`
  set b := √a with hb
  have hb0 : 0 < b := sqrt_pos.mpr ha
  have h_int : ∫ x in Ioi b, a * x ^ (-2 : ℝ) = b := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hb0]
    have : b ^ (-2 + 1 : ℝ) = b⁻¹ := by norm_num [rpow_neg_one]
    rw [this, hb, show (-2 + 1 : ℝ) = -1 by norm_num, div_neg, div_one, neg_neg, ← div_eq_mul_inv,
      div_sqrt]
  have h_integrable : IntegrableOn (fun x ↦ a * x ^ (-2 : ℝ)) (Ioi b) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hb0).const_mul a
  calc ∫⁻ x in Ioi 0, P {ω | x < f ω}
  _ = (∫⁻ x in Ioc 0 b, P {ω | x < f ω}) + ∫⁻ x in Ioi b, P {ω | x < f ω} := by
    rw [← Ioc_union_Ioi_eq_Ioi hb0.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  _ ≤ (∫⁻ _ in Ioc 0 b, 1) + ∫⁻ x in Ioi b, ENNReal.ofReal (a * x ^ (-2 : ℝ)) := by
    refine add_le_add (setLIntegral_mono measurable_const fun _ _ ↦ prob_le_one)
      (setLIntegral_mono (by fun_prop : Measurable fun x : ℝ ↦ ENNReal.ofReal (a * x ^ (-2 : ℝ)))
        fun x hx ↦ ?_)
    have hx0 : 0 < x := hb0.trans hx
    refine (h x hx0).trans_eq ?_
    rw [rpow_neg hx0.le, rpow_two, div_eq_mul_inv]
  _ = ENNReal.ofReal b + ENNReal.ofReal b := by
    rw [setLIntegral_const, one_mul, volume_Ioc, sub_zero,
      ← ofReal_integral_eq_lintegral_ofReal h_integrable
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x (hx : b < x) ↦
          by positivity [(hb0.trans hx).le]), h_int]
  _ = ENNReal.ofReal (2 * b) := by
    rw [← ENNReal.ofReal_add hb0.le hb0.le, two_mul]

end MeasureTheory
