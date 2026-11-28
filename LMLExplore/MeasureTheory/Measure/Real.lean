/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# The union bound in high-probability form

High-probability statements are proved by bounding the probability of a bad event for each of
finitely many indices and taking a union bound. This file records that step once: if each of the
events `s i`, `i : ι` with `ι` finite, has probability at most `δ / card ι`, then with probability
at least `1 - δ` none of them happens. The events need not be measurable. It also records the
intersection of two high-probability events: if `s` and `t` have probabilities at least `1 - a` and
`1 - b`, then `s ∩ t` has probability at least `1 - a - b`, and that the masses of the traces in a
set of the cells of a finite measurable partition sum to the mass of the set. Finally, it records
that a set of nonzero finite mass has positive real mass, so that the products of the real masses of
points under a finite measure that charges every point are positive, that finite products of ratios
of masses are the `ofReal` of the products of the ratios of the real masses, that the real masses of
the points of a finite space sum to `1` under a probability measure, as do the products of the real
masses of the coordinates of the samples `x : ι → α`, and that the real mass is monotone under
almost-everywhere inclusion.

## Main statements

* `LMLExplore.one_sub_le_measureReal_compl_iUnion`: the union bound over a finite type, with
  confidence `δ / card ι` for each index.
* `LMLExplore.one_sub_sub_le_measureReal_inter`: two events of probabilities at least `1 - a` and
  `1 - b` both happen with probability at least `1 - a - b`.
* `LMLExplore.sum_measureReal_preimage_singleton_inter`: the masses of the traces in a set `C` of
  the cells of a finite measurable partition `π : Ω → Fin k` sum to the mass of `C`.
* `MeasureTheory.measureReal_pos_of_ne_zero`: a set of nonzero finite mass has positive real mass.
* `MeasureTheory.prod_measureReal_singleton_pos`: `0 < ∏ i, μ.real {x i}` for a finite measure `μ`
  that charges every point.
* `MeasureTheory.prod_measure_div_eq_ofReal_prod`: a finite product of ratios of masses of finite
  measures is the `ofReal` of the product of the ratios of the real masses.
* `MeasureTheory.sum_measureReal_singleton_eq_one`: the real masses of the points of a finite
  space sum to `1` under a probability measure.
* `MeasureTheory.sum_prod_measureReal_singleton_eq_one`: `∑ x : ι → α, ∏ i, μ.real {x i} = 1` for
  a probability measure `μ` on a finite space.
* `MeasureTheory.measureReal_mono_ae`: the real mass is monotone under almost-everywhere
  inclusion.
-/

public section

open MeasureTheory Set

open scoped ENNReal

namespace LMLExplore

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Union bound**, in high-probability form: if each of the finitely many events `s i` has
probability at most `δ / card ι`, then with probability at least `1 - δ` none of them happens.
The events need not be measurable. -/
lemma one_sub_le_measureReal_compl_iUnion [IsProbabilityMeasure μ] [Fintype ι] {s : ι → Set Ω}
    {δ : ℝ} (hδ : 0 ≤ δ) (hs : ∀ i, μ.real (s i) ≤ δ / Fintype.card ι) :
    1 - δ ≤ μ.real (⋃ i, s i)ᶜ := by
  have h_univ : 1 ≤ μ.real (⋃ i, s i) + μ.real (⋃ i, s i)ᶜ := by
    have h := measureReal_union_le (μ := μ) (⋃ i, s i) (⋃ i, s i)ᶜ
    rwa [union_compl_self, probReal_univ] at h
  have h_sum : ∑ i, μ.real (s i) ≤ δ := by
    refine (Finset.sum_le_sum fun i _ ↦ hs i).trans ?_
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp [hδ]
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_div_cancel₀ _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  linarith [measureReal_iUnion_fintype_le (μ := μ) s]

/-- **Intersection of two high-probability events**: if `s` has probability at least `1 - a` and
the measurable event `t` has probability at least `1 - b`, then `s ∩ t` has probability at least
`1 - a - b`. -/
lemma one_sub_sub_le_measureReal_inter [IsProbabilityMeasure μ] {s t : Set Ω} (ht : MeasurableSet t)
    {a b : ℝ} (hs : 1 - a ≤ μ.real s) (htb : 1 - b ≤ μ.real t) : 1 - a - b ≤ μ.real (s ∩ t) := by
  have h := measureReal_union_add_inter (μ := μ) (s := s) ht
  have h₁ : μ.real (s ∪ t) ≤ 1 := measureReal_le_one
  linarith

/-- The masses of a finite measure on the traces in a set `C` of the cells of a finite measurable
partition sum to the mass of `C`. -/
lemma sum_measureReal_preimage_singleton_inter (μ : Measure Ω) [IsFiniteMeasure μ]
    {k : ℕ} {π : Ω → Fin k} (hπ : Measurable π) (C : Set Ω) :
    ∑ j, μ.real (π ⁻¹' {j} ∩ C) = μ.real C := by
  have := sum_measureReal_preimage_singleton (μ := μ.restrict C) Finset.univ (f := π)
    (fun j _ ↦ hπ (measurableSet_singleton j))
  simpa only [Finset.coe_univ, preimage_univ, measureReal_restrict_apply
    (hπ (measurableSet_singleton _)), measureReal_restrict_apply MeasurableSet.univ,
    univ_inter] using this

end LMLExplore

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s t : Set α}

/-- A set of nonzero finite mass has positive real mass. -/
lemma measureReal_pos_of_ne_zero (h₀ : μ s ≠ 0) (h : μ s ≠ ∞ := by finiteness) :
    0 < μ.real s :=
  ENNReal.toReal_pos h₀ h

/-- The finite products of the real masses of points under a finite measure that charges every
point are positive. -/
lemma prod_measureReal_singleton_pos {ι : Type*} [Fintype ι] [IsFiniteMeasure μ]
    (hμ : ∀ x, μ {x} ≠ 0) (x : ι → α) : 0 < ∏ i, μ.real {x i} :=
  Finset.prod_pos fun _ _ ↦ measureReal_pos_of_ne_zero (hμ _)

/-- A finite product of ratios of the masses of sets under two finite measures is the `ofReal` of
the product of the ratios of their real masses, when the second measure charges the sets. -/
lemma prod_measure_div_eq_ofReal_prod {ι : Type*} {s : Finset ι} {ν : Measure α}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {t : ι → Set α} (ht : ∀ i ∈ s, ν (t i) ≠ 0) :
    ∏ i ∈ s, μ (t i) / ν (t i) = ENNReal.ofReal (∏ i ∈ s, μ.real (t i) / ν.real (t i)) := by
  rw [ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ div_nonneg measureReal_nonneg measureReal_nonneg]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [ENNReal.ofReal_div_of_pos (measureReal_pos_of_ne_zero (ht i hi)), ofReal_measureReal,
    ofReal_measureReal]

/-- The real masses of the points of a finite space sum to `1` under a probability measure. -/
lemma sum_measureReal_singleton_eq_one [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ y, μ.real {y} = 1 := by
  rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]

/-- Under a probability measure on a finite space, the products of the real masses of the
coordinates of the samples `x : ι → α` sum to `1`. -/
lemma sum_prod_measureReal_singleton_eq_one [MeasurableSingletonClass α] [Fintype α]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : Measure α) [IsProbabilityMeasure μ] :
    ∑ x : ι → α, ∏ i, μ.real {x i} = 1 := by
  rw [← Fintype.prod_sum fun (_ : ι) y ↦ μ.real {y}, sum_measureReal_singleton_eq_one,
    Finset.prod_const_one]

/-- The real mass is monotone under almost-everywhere inclusion of sets of finite mass. -/
lemma measureReal_mono_ae (h : s ≤ᵐ[μ] t) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono h₂ (measure_mono_ae h)

end MeasureTheory
