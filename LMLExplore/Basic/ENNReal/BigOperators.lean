/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.BigOperators.Perm
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Sums and products of extended nonnegative reals

## Main statements

* `ENNReal.ofReal_sum_mul_toReal`: a weighted sum `∑ x ∈ s, f x * (g x).toReal` of finite
  extended nonnegative reals `g x` with nonnegative real weights `f x`, mapped back to `ℝ≥0∞`, is
  `∑ x ∈ s, ENNReal.ofReal (f x) * g x`. It moves a real convex combination of finite
  divergences, such as a mixture of the divergence vectors of finitely many models, to `ℝ≥0∞`.
* `ENNReal.sum_perm_apply_div_card`: the average of `w (σ j)` over all permutations `σ` of a
  finite type is the average `(∑ i, w i) / K` of the `w i`, as `Equiv.Perm.sum_apply_div_card`
  says in a semifield of characteristic zero.
* `ENNReal.sum_coe_div_card_ne_top`: the average of finitely many finite values is finite.
* `ENNReal.ofReal_sum_mul_add`: an affine form `∑ x ∈ s, f x * g x + c` with nonnegative real
  coefficients, evaluated at a point with nonnegative real coordinates and mapped to `ℝ≥0∞`, is
  the same affine form of the images in `ℝ≥0∞`.
* `ENNReal.one_sub_mul_le_one_sub_add_one_sub`: `1 - a * b ≤ (1 - a) + (1 - b)`, the union
  bound for two independent events.
* `ENNReal.one_sub_prod_le_sum_one_sub`: `1 - ∏ i ∈ s, m i ≤ ∑ i ∈ s, (1 - m i)`, the union
  bound for independent events of probabilities `1 - m i`.
-/

public section

open scoped ENNReal NNReal

namespace ENNReal

/-- A sum `∑ x ∈ s, f x * (g x).toReal` of finite extended nonnegative reals `g x` with
nonnegative weights `f x`, mapped back to `ℝ≥0∞`, is `∑ x ∈ s, ENNReal.ofReal (f x) * g x`. -/
lemma ofReal_sum_mul_toReal {ι : Type*} {s : Finset ι} {f : ι → ℝ} {g : ι → ℝ≥0∞}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, g x ≠ ∞) :
    ENNReal.ofReal (∑ x ∈ s, f x * (g x).toReal) = ∑ x ∈ s, ENNReal.ofReal (f x) * g x := by
  rw [ofReal_sum_of_nonneg fun x hx ↦ mul_nonneg (hf x hx) toReal_nonneg]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [ofReal_mul (hf x hx), ofReal_toReal (hg x hx)]

/-- **Averaging over all permutations** in `ℝ≥0∞`: the average of `w (σ j)` over the
permutations `σ` is the average `(∑ i, w i) / K` of the `w i`, for `K` the cardinality of `ι`. -/
theorem sum_perm_apply_div_card {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ≥0∞) (j : ι) :
    (∑ σ : Equiv.Perm ι, w (σ j)) / Fintype.card (Equiv.Perm ι) = (∑ i, w i) / Fintype.card ι := by
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (@Fintype.card_ne_zero ι _ ⟨j⟩)
  rw [ENNReal.div_eq_div_iff hK (by simp) (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by simp)]
  simpa [nsmul_eq_mul] using Equiv.Perm.card_nsmul_sum_apply w j

/-- The average `(∑ i, e i) / K` of finitely many finite values `e i`, for `K` the cardinality of
`ι`, is finite. -/
theorem sum_coe_div_card_ne_top {ι : Type*} [Fintype ι] (e : ι → ℝ≥0) :
    (∑ i, (e i : ℝ≥0∞)) / Fintype.card ι ≠ ∞ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · exact div_ne_top (by simp) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- An affine form `∑ x ∈ s, f x * g x + c` with nonnegative real coefficients `f x`, `c`,
evaluated at a point with nonnegative real coordinates `g x`, commutes with `ENNReal.ofReal`. -/
lemma ofReal_sum_mul_add {ι : Type*} {s : Finset ι} {f g : ι → ℝ} {c : ℝ}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 ≤ g x) (hc : 0 ≤ c) :
    ENNReal.ofReal (∑ x ∈ s, f x * g x + c) =
      ∑ x ∈ s, ENNReal.ofReal (f x) * ENNReal.ofReal (g x) + ENNReal.ofReal c := by
  have h : ∀ x ∈ s, 0 ≤ f x * g x := fun x hx ↦ mul_nonneg (hf x hx) (hg x hx)
  rw [ofReal_add (Finset.sum_nonneg h) hc, ofReal_sum_of_nonneg h]
  refine congrArg (· + _) (Finset.sum_congr rfl fun x hx ↦ ?_)
  rw [ofReal_mul (hf x hx)]

/-- One minus a product of two extended nonnegative reals is at most the sum of the numbers
`1 - a` and `1 - b`: the union bound for two independent events of probabilities `1 - a` and
`1 - b`. -/
lemma one_sub_mul_le_one_sub_add_one_sub (a b : ℝ≥0∞) : 1 - a * b ≤ (1 - a) + (1 - b) := by
  rcases le_total 1 a with ha | ha
  · exact (tsub_le_tsub_left (le_mul_of_one_le_left' ha) 1).trans le_add_self
  rcases le_total 1 b with hb | hb
  · exact (tsub_le_tsub_left (le_mul_of_one_le_right' hb) 1).trans le_self_add
  -- For `a, b ≤ 1`: `1 = (1 - a) + a` and `a = a * (1 - b) + a * b ≤ (1 - b) + a * b`.
  refine tsub_le_iff_right.2 ?_
  calc (1 : ℝ≥0∞) = (1 - a) + (a * (1 - b) + a * b) := by
        rw [← mul_add, tsub_add_cancel_of_le hb, mul_one, tsub_add_cancel_of_le ha]
  _ ≤ (1 - a) + ((1 - b) + a * b) := by gcongr; exact mul_le_of_le_one_left' ha
  _ = (1 - a) + (1 - b) + a * b := (add_assoc _ _ _).symm

/-- One minus a product of extended nonnegative reals is at most the sum of the numbers
`1 - m i`: the union bound for independent events of probabilities `1 - m i`. -/
lemma one_sub_prod_le_sum_one_sub {ι : Type*} (s : Finset ι) (m : ι → ℝ≥0∞) :
    1 - ∏ i ∈ s, m i ≤ ∑ i ∈ s, (1 - m i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact (one_sub_mul_le_one_sub_add_one_sub _ _).trans (by gcongr)

end ENNReal
