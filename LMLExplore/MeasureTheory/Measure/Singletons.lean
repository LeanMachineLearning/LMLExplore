/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Measures through their masses on points

Two facts about measures read off their masses on points: a measure that charges every point
dominates every measure, and on a countable additive monoid with an antidiagonal (such as `ℕ`), the
law of the sum of the coordinates of a measure on pairs gives a point `s` the total mass of the
pairs with sum `s`.

## Main statements

* `MeasureTheory.Measure.absolutelyContinuous_of_forall_singleton_pos`: every measure is absolutely
  continuous with respect to a measure that charges every point.
* `MeasureTheory.Measure.map_add_singleton_eq_sum_antidiagonal`: the mass of `{s}` under the law of
  `x.1 + x.2` is `∑ x ∈ antidiagonal s, μ {x}`.
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
