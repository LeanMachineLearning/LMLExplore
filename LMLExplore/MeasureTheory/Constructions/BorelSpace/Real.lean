/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Probability measures on `ℝ` and bounded intervals

The intervals `[-M, M]`, `M : ℕ`, increase to `ℝ`, so a probability measure on `ℝ` gives them a
mass tending to `1`: it gives a mass more than `1 - δ` to one of them, for every `δ ≠ 0`.

## Main statements

* `MeasureTheory.exists_one_sub_lt_measure_Icc`: a probability measure on `ℝ` gives a mass more
  than `1 - δ` to some interval `[-M, M]`.
-/

public section

open Set

open scoped ENNReal

namespace MeasureTheory

/-- A probability measure on `ℝ` gives a mass more than `1 - δ` to some interval `[-M, M]`. -/
lemma exists_one_sub_lt_measure_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] {δ : ℝ≥0∞}
    (hδ : δ ≠ 0) : ∃ M : ℕ, 1 - δ < μ (Icc (-(M : ℝ)) M) := by
  have hU : (⋃ M : ℕ, Icc (-(M : ℝ)) M) = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨⌈|x|⌉₊, abs_le.1 (Nat.le_ceil _)⟩
  have htend := tendsto_measure_iUnion_atTop (μ := μ) (s := fun M : ℕ ↦ Icc (-(M : ℝ)) M)
    fun m n hmn ↦ Icc_subset_Icc (by simpa using hmn) (by simpa using hmn)
  rw [hU, measure_univ] at htend
  exact (htend.eventually (lt_mem_nhds
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδ))).exists

end MeasureTheory
