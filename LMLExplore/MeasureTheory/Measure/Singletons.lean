/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Measures through their masses on points

Facts about measures read off their masses on points: a measure that charges every point
dominates every measure; on a countable additive monoid with an antidiagonal (such as `ℕ`), the
law of the sum of the coordinates of a measure on pairs gives a point `s` the total mass of the
pairs with sum `s`; and on a finite type, `a ↦ p a / ν{a}` is a density of the vector `p` with
respect to a finite measure `ν`, of total `ν`-integral `∑ a, p a` when `ν` charges every point.

## Main statements

* `MeasureTheory.Measure.absolutelyContinuous_of_forall_singleton_pos`: every measure is absolutely
  continuous with respect to a measure that charges every point.
* `MeasureTheory.Measure.map_add_singleton_eq_sum_antidiagonal`: the mass of `{s}` under the law of
  `x.1 + x.2` is `∑ x ∈ antidiagonal s, μ {x}`.
* `MeasureTheory.lintegral_ofReal_div_measureReal_le`,
  `MeasureTheory.lintegral_ofReal_div_measureReal_eq`: the density `p a / ν{a}` of a nonnegative
  vector `p` has `ν`-integral at most `∑ a, p a`, with equality if `ν` charges every point.
-/

public section

open Set Finset

namespace MeasureTheory.Measure

/-- Every measure is absolutely continuous with respect to a measure that charges every point. -/
theorem absolutelyContinuous_of_forall_singleton_pos {α : Type*} {_ : MeasurableSpace α}
    {μ ν : Measure α} (h : ∀ x, 0 < ν {x}) : μ ≪ ν :=
  AbsolutelyContinuous.mk fun t _ ht ↦ by
    rcases t.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · exact measure_empty
    · exact absurd ht ((h x).trans_le (measure_mono (singleton_subset_iff.mpr hx))).ne'

/-- On a countable additive monoid with an antidiagonal, the mass of a point `s` under the law of
the sum of the coordinates is the sum of the masses of the pairs with sum `s`. -/
theorem map_add_singleton_eq_sum_antidiagonal {M : Type*} [AddMonoid M] [HasAntidiagonal M]
    [MeasurableSpace M] [Countable M] [MeasurableSingletonClass M] (μ : Measure (M × M)) (s : M) :
    μ.map (fun x ↦ x.1 + x.2) {s} = ∑ x ∈ antidiagonal s, μ {x} := by
  rw [map_apply (measurable_of_countable _) (measurableSet_singleton s), sum_measure_singleton]
  congr 1
  ext x
  simp

end MeasureTheory.Measure

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]

/-- A point charged by the finite measure `ν` carries the mass `ofReal (x / ν{a}) * ν{a} = ofReal x`
of the density `x / ν{a}`. -/
theorem ofReal_div_measureReal_mul {a : α} (ha : ν {a} ≠ 0) (x : ℝ) :
    ENNReal.ofReal (x / ν.real {a}) * ν {a} = ENNReal.ofReal x := by
  have h0 : ν.real {a} ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 ha
  rw [← ofReal_measureReal (measure_ne_top _ _), ← ENNReal.ofReal_mul' measureReal_nonneg,
    div_mul_cancel₀ x h0]

variable [Fintype α] [MeasurableSingletonClass α]

/-- The density `p a / ν{a}` of a nonnegative vector `p` has `ν`-integral at most `∑ a, p a`. -/
theorem lintegral_ofReal_div_measureReal_le {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) :
    ∫⁻ a, ENNReal.ofReal (p a / ν.real {a}) ∂ν ≤ ENNReal.ofReal (∑ a, p a) := by
  rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hp a]
  refine sum_le_sum fun a _ ↦ ?_
  rcases eq_or_ne (ν {a}) 0 with ha | ha
  · simp [ha]
  · rw [ofReal_div_measureReal_mul ha]

/-- If `ν` is finite and charges every point, the density `p a / ν{a}` has `ν`-integral
`∑ a, p a`. -/
theorem lintegral_ofReal_div_measureReal_eq (hν : ∀ a, ν {a} ≠ 0) {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) :
    ∫⁻ a, ENNReal.ofReal (p a / ν.real {a}) ∂ν = ENNReal.ofReal (∑ a, p a) := by
  rw [lintegral_fintype, ENNReal.ofReal_sum_of_nonneg fun a _ ↦ hp a]
  exact sum_congr rfl fun a _ ↦ ofReal_div_measureReal_mul (hν a) _

end MeasureTheory
