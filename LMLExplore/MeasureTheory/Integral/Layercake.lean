/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Expectation of a random variable with a power tail

By the layer cake formula, the expectation of the positive part of a real random variable `f` is
`E[f⁺] = ∫_0^∞ P(x < f) dx`. If `P(x < f) ≤ c x ^ p` for every level `x > b > 0`, with `p < -1`,
then bounding the tail probability by `1` below `b` and by `c x ^ p` above gives
`∫_0^∞ P(x < f) dx ≤ b - c b ^ (p + 1) / (p + 1)`.

For a quadratic tail `P(x < f) ≤ a / x ²` and the level `b = √a`, this gives `E[f⁺] ≤ 2 √a`. The
proof of [LS, Theorem 9.1] uses this to bound the expected amount by which the index of an optimal
arm under the MOSS algorithm falls below its mean.

## Main statements

* `MeasureTheory.lintegral_Ioi_measure_lt_le_of_le_rpow`: if `P(x < f) ≤ c x ^ p` for every
  `x > b > 0`, with `p < -1`, then
  `∫⁻ x in Ioi 0, P {ω | x < f ω} ≤ ofReal (b - c b ^ (p + 1) / (p + 1))`.
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

/-- **Layer cake bound from a power tail.** If `P(x < f) ≤ c x ^ p` for every level `x > b`, where
`b > 0` and `p < -1`, then bounding the tail probability by `1` below the level `b` and by `c x ^ p`
above it gives `∫⁻ x in Ioi 0, P {ω | x < f ω} ≤ ofReal (b - c b ^ (p + 1) / (p + 1))`. -/
theorem lintegral_Ioi_measure_lt_le_of_le_rpow {b c p : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (hp : p < -1)
    (h : ∀ x > b, P {ω | x < f ω} ≤ ENNReal.ofReal (c * x ^ p)) :
    ∫⁻ x in Ioi 0, P {ω | x < f ω} ≤ ENNReal.ofReal (b - c * b ^ (p + 1) / (p + 1)) := by
  have h_integrable : IntegrableOn (fun x ↦ c * x ^ p) (Ioi b) :=
    (integrableOn_Ioi_rpow_of_lt hp hb).const_mul c
  calc ∫⁻ x in Ioi 0, P {ω | x < f ω}
  _ = (∫⁻ x in Ioc 0 b, P {ω | x < f ω}) + ∫⁻ x in Ioi b, P {ω | x < f ω} := by
    rw [← Ioc_union_Ioi_eq_Ioi hb.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  _ ≤ (∫⁻ _ in Ioc 0 b, 1) + ∫⁻ x in Ioi b, ENNReal.ofReal (c * x ^ p) :=
    add_le_add (setLIntegral_mono measurable_const fun _ _ ↦ prob_le_one)
      (setLIntegral_mono (by fun_prop) h)
  _ = ENNReal.ofReal b + ENNReal.ofReal (c * (-b ^ (p + 1) / (p + 1))) := by
    rw [← integral_Ioi_rpow_of_lt hp hb, ← integral_const_mul,
      ofReal_integral_eq_lintegral_ofReal h_integrable ?_]
    · simp
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun x (hx : b < x) ↦ by
      positivity [(hb.trans hx).le]
  _ = ENNReal.ofReal (b - c * b ^ (p + 1) / (p + 1)) := by
    have hp1 : p + 1 < 0 := by linarith
    rw [← ENNReal.ofReal_add hb.le
      (mul_nonneg hc (div_nonneg_of_nonpos (neg_nonpos.2 (rpow_pos_of_pos hb _).le) hp1.le))]
    congr 1
    ring

/-- **Expectation from a quadratic tail.** If a real random variable `f` on a probability space
satisfies `P(x < f) ≤ a / x ^ 2` for every `x > 0`, then the expectation of its positive part is
at most `2 √a`: `∫⁻ ω, ofReal (f ω) ∂P ≤ ofReal (2 * √a)`. -/
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
  -- split the levels at `√a`: below, bound the probability by `1`; above, by `a x ^ (-2)`
  have hb0 : 0 < √a := sqrt_pos.mpr ha
  refine (lintegral_Ioi_measure_lt_le_of_le_rpow hb0 ha.le (by norm_num : (-2 : ℝ) < -1)
    fun x hx ↦ (h x (hb0.trans hx)).trans_eq ?_).trans_eq ?_
  · rw [rpow_neg (hb0.trans hx).le, rpow_two, div_eq_mul_inv]
  · rw [show (-2 : ℝ) + 1 = -1 by norm_num, rpow_neg_one]
    congr 1
    field_simp
    rw [sq_sqrt ha.le]
    ring

end MeasureTheory
