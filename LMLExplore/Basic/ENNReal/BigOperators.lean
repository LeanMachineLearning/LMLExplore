/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.BigOperators.Perm
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Sums of extended nonnegative reals

## Main statements

* `ENNReal.ofReal_sum_mul_toReal`: a weighted sum `∑ x ∈ s, f x * (g x).toReal` of finite
  extended nonnegative reals `g x` with nonnegative real weights `f x`, mapped back to `ℝ≥0∞`, is
  `∑ x ∈ s, ENNReal.ofReal (f x) * g x`. It moves a real convex combination of finite
  divergences, such as a mixture of the divergence vectors of finitely many models, to `ℝ≥0∞`.
* `ENNReal.sum_perm_apply_div_card`: the average of `w (σ j)` over all permutations `σ` of a
  finite type is the average `(∑ i, w i) / K` of the `w i`, as `Equiv.Perm.sum_apply_div_card`
  says in a semifield of characteristic zero.
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

/-- **Averaging over all permutations** in `ℝ≥0∞`: the average of `w (σ j)` over the
permutations `σ` is the average `(∑ i, w i) / K` of the `w i`, for `K` the cardinality of `ι`. -/
theorem sum_perm_apply_div_card {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℝ≥0∞) (j : ι) :
    (∑ σ : Equiv.Perm ι, w (σ j)) / Fintype.card (Equiv.Perm ι) = (∑ i, w i) / Fintype.card ι := by
  have hK : (Fintype.card ι : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (@Fintype.card_ne_zero ι _ ⟨j⟩)
  rw [ENNReal.div_eq_div_iff hK (by simp) (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by simp)]
  simpa [nsmul_eq_mul] using Equiv.Perm.card_nsmul_sum_apply w j

end ENNReal
