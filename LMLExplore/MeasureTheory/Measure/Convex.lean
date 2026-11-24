/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Measure.Sum

/-!
# Charging finitely many sets in a convex set of measures

In a convex set of measures over `ℝ≥0∞`, the even mixture of two members charges every set that
one of them charges. So if each of finitely many sets is charged by some member, a single member
charges them all.

## Main statements

* `Convex.exists_mem_forall_measure_ne_zero`: in a nonempty convex set of measures, if each of
  finitely many sets is charged by some member, then some member charges all of them.
-/

public section

open MeasureTheory
open scoped ENNReal

/-- In a nonempty convex set `S` of measures, if each set `A i`, for `i` in a finite set `s`, is
charged by some member of `S`, then a single member of `S` charges all of them. -/
lemma Convex.exists_mem_forall_measure_ne_zero {α ι : Type*} {mα : MeasurableSpace α}
    {S : Set (Measure α)} (hS : Convex ℝ≥0∞ S) (hne : S.Nonempty) {s : Finset ι}
    {A : ι → Set α} (h : ∀ i ∈ s, ∃ P ∈ S, P (A i) ≠ 0) :
    ∃ ρ ∈ S, ∀ i ∈ s, ρ (A i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨hne.some, hne.some_mem, by simp⟩
  | insert x s hx ih =>
    obtain ⟨ρ, hρ, hρs⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    obtain ⟨P, hP, hPx⟩ := h x (Finset.mem_insert_self x s)
    refine ⟨(2⁻¹ : ℝ≥0∞) • ρ + (2⁻¹ : ℝ≥0∞) • P,
      hS hρ hP zero_le zero_le ENNReal.inv_two_add_inv_two, fun i hi ↦ ?_⟩
    simp only [add_apply, smul_apply, smul_eq_mul, ne_eq, add_eq_zero,
      mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.ofNat_ne_top, false_or, not_and]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact fun _ ↦ hPx
    · exact fun h ↦ absurd h (hρs i hi)
