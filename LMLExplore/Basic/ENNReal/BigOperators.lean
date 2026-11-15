/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Weighted sums and products of extended nonnegative reals

## Main statements

* `ENNReal.ofReal_sum_mul_toReal`: a weighted sum `∑ x ∈ s, f x * (g x).toReal` of finite
  extended nonnegative reals `g x` with nonnegative real weights `f x`, mapped back to `ℝ≥0∞`, is
  `∑ x ∈ s, ENNReal.ofReal (f x) * g x`. It moves a real convex combination of finite
  divergences, such as a mixture of the divergence vectors of finitely many models, to `ℝ≥0∞`.
* `ENNReal.one_sub_prod_le_sum_one_sub`: for numbers `m i ≤ 1`,
  `1 - ∏ i ∈ s, m i ≤ ∑ i ∈ s, (1 - m i)`, the union bound for independent events of
  probabilities `1 - m i`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- A sum `∑ x ∈ s, f x * (g x).toReal` of finite extended nonnegative reals `g x` with
nonnegative weights `f x`, mapped back to `ℝ≥0∞`, is `∑ x ∈ s, ENNReal.ofReal (f x) * g x`. -/
lemma ofReal_sum_mul_toReal {ι : Type*} {s : Finset ι} {f : ι → ℝ} {g : ι → ℝ≥0∞}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, g x ≠ ∞) :
    ENNReal.ofReal (∑ x ∈ s, f x * (g x).toReal) = ∑ x ∈ s, ENNReal.ofReal (f x) * g x := by
  rw [ofReal_sum_of_nonneg fun x hx ↦ mul_nonneg (hf x hx) toReal_nonneg]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [ofReal_mul (hf x hx), ofReal_toReal (hg x hx)]

/-- For numbers `m i ≤ 1`, one minus their product is at most the sum of the numbers `1 - m i`:
the union bound for independent events of probabilities `1 - m i`. -/
lemma one_sub_prod_le_sum_one_sub {ι : Type*} (s : Finset ι) {m : ι → ℝ≥0∞}
    (hm : ∀ i ∈ s, m i ≤ 1) :
    1 - ∏ i ∈ s, m i ≤ ∑ i ∈ s, (1 - m i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    have hmj : m j ≤ 1 := hm j (Finset.mem_insert_self j s)
    have hms : ∀ i ∈ s, m i ≤ 1 := fun i hi ↦ hm i (Finset.mem_insert_of_mem hi)
    have hprod : ∏ i ∈ s, m i ≤ 1 := Finset.prod_le_one hms
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    calc 1 - m j * ∏ i ∈ s, m i ≤ (1 - m j) + (1 - ∏ i ∈ s, m i) := by
          refine tsub_le_iff_right.2 ?_
          calc (1 : ℝ≥0∞) = (1 - m j) + m j * ((1 - ∏ i ∈ s, m i) + ∏ i ∈ s, m i) := by
                rw [tsub_add_cancel_of_le hprod, mul_one, tsub_add_cancel_of_le hmj]
          _ = (1 - m j) + (m j * (1 - ∏ i ∈ s, m i) + m j * ∏ i ∈ s, m i) := by rw [mul_add]
          _ ≤ (1 - m j) + ((1 - ∏ i ∈ s, m i) + m j * ∏ i ∈ s, m i) := by
                gcongr; exact mul_le_of_le_one_left' hmj
          _ = (1 - m j) + (1 - ∏ i ∈ s, m i) + m j * ∏ i ∈ s, m i := (add_assoc _ _ _).symm
    _ ≤ (1 - m j) + ∑ i ∈ s, (1 - m i) := by gcongr; exact ih hms

end ENNReal
