/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Basic.ENNReal.Action
public import Mathlib.Basic.ENNReal.Inv
import LMLExplore.Algebra.BigOperators.Field

/-!
# Finite convex combinations for convexity over `ℝ≥0∞`

Convex sets of measures are stated with Mathlib's `Convex ℝ≥0∞`, for which Mathlib's
`Convex.sum_mem` does not apply: it needs a field of scalars acting on an additive group. This file
proves that such a convex set contains the finite convex combinations of its members with weights
in `ℝ≥0`, acting through the coercion `ℝ≥0 → ℝ≥0∞` (Mathlib's `ENNReal.smul_def`).

## Main statements

* `Convex.sum_nnreal_smul_mem`: a set convex over `ℝ≥0∞` contains the finite combinations of its
  members with weights in `ℝ≥0` of sum `1`.
-/

public section

open scoped ENNReal NNReal

/-- A set convex over `ℝ≥0∞` contains the finite combinations of its members with weights in
`ℝ≥0` of sum `1`, the weights acting through the coercion `ℝ≥0 → ℝ≥0∞`. -/
lemma Convex.sum_nnreal_smul_mem {E ι : Type*} [AddCommMonoid E] [Module ℝ≥0∞ E] {S : Set E}
    (hS : Convex ℝ≥0∞ S) {T : Finset ι} {w : ι → ℝ≥0} (hw : ∑ i ∈ T, w i = 1) {x : ι → E}
    (hx : ∀ i ∈ T, x i ∈ S) : ∑ i ∈ T, w i • x i ∈ S := by
  classical
  induction T using Finset.induction_on generalizing w with
  | empty => simp at hw
  | insert a T ha ih =>
    rw [Finset.sum_insert ha] at hw ⊢
    have hxa := hx a (Finset.mem_insert_self a T)
    have hxT : ∀ i ∈ T, x i ∈ S := fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    rcases eq_or_ne (∑ i ∈ T, w i) 0 with h0 | h0
    · rw [h0, add_zero] at hw
      rw [Finset.sum_eq_zero fun i hi ↦ by rw [Finset.sum_eq_zero_iff.1 h0 i hi, zero_smul],
        add_zero, hw, one_smul]
      exact hxa
    · rw [Finset.sum_smul_eq_smul_sum_div_smul h0]
      have h := hS hxa (ih (w := fun i ↦ w i / ∑ j ∈ T, w j) ?_ hxT) zero_le zero_le
        (show (w a : ℝ≥0∞) + ((∑ i ∈ T, w i : ℝ≥0) : ℝ≥0∞) = 1 by exact_mod_cast hw)
      · rwa [← ENNReal.smul_def, ← ENNReal.smul_def] at h
      · rw [← Finset.sum_div, div_self h0]
