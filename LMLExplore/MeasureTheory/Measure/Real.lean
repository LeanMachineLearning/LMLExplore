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
at least `1 - δ` none of them happens. The events need not be measurable.

## Main statements

* `LMLExplore.one_sub_le_measureReal_compl_iUnion`: the union bound over a finite type, with
  confidence `δ / card ι` for each index.
-/

public section

open MeasureTheory Set

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

end LMLExplore
