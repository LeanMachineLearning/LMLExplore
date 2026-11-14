/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.EReal.BigOperators
public import Mathlib.Data.EReal.Inv
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Comparing reals with extended nonnegative reals in `EReal`

The bounds of a large deviation principle compare real exponents `r` with values of a rate
function in `ℝ≥0∞`, both cast to `EReal`. This file collects two such comparisons.

* A real `r` below a finite sum `∑ a ∈ s, f a` of values in `ℝ≥0∞` splits into reals `g a` below
  each `f a` with `r < ∑ a ∈ s, g a`, and symmetrically above. This divides an exponent of a
  product of measures between its factors.
* A real `r` is below `w * c`, for `w > 0` and `c : ℝ≥0∞`, if and only if `r / w` is below `c`,
  and similarly above. This rescales an exponent when the speed of a principle changes.

## Main statements

* `EReal.exists_forall_lt_and_lt_sum`: if `r < ∑ a ∈ s, f a`, there are reals `g a < f a` with
  `r < ∑ a ∈ s, g a`.
* `EReal.exists_forall_gt_and_sum_lt`: if `∑ a ∈ s, f a < r`, there are reals `g a > f a` with
  `∑ a ∈ s, g a < r`.
* `EReal.coe_lt_coe_ennreal_ofReal_mul_iff`: `r < w * c ↔ r / w < c` for `w > 0`.
* `EReal.coe_ennreal_ofReal_mul_lt_coe_iff`: `w * c < r ↔ c < r / w` for `w > 0`.
-/

public section

open Finset

open scoped ENNReal NNReal

namespace EReal

variable {ι : Type*} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ}

/-- A real `r` below a finite sum of reals `x a` stays below the sum when every term is lowered by
a common margin `δ > 0`. -/
private lemma exists_pos_lt_sum_sub {x : ι → ℝ} (h : r < ∑ a ∈ s, x a) :
    ∃ δ > 0, r < ∑ a ∈ s, (x a - δ) := by
  set δ := (∑ a ∈ s, x a - r) / (#s + 1) with hδ_def
  have hδ' : (#s + 1 : ℝ) * δ = ∑ a ∈ s, x a - r := by
    rw [hδ_def, mul_div_cancel₀ _ (by positivity)]
  have hδ : 0 < δ := _root_.div_pos (by linarith) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  rw [sum_sub_distrib, sum_const, _root_.nsmul_eq_mul]
  linarith

/-- **Splitting a real below a sum.** If a real `r` is below the sum `∑ a ∈ s, f a` of values in
`ℝ≥0∞`, then there are reals `g a`, each below `f a`, whose sum is still above `r`. -/
lemma exists_forall_lt_and_lt_sum (h : (r : EReal) < ((∑ a ∈ s, f a : ℝ≥0∞) : EReal)) :
    ∃ g : ι → ℝ, (∀ a ∈ s, (g a : EReal) < f a) ∧ r < ∑ a ∈ s, g a := by
  classical
  by_cases htop : ∑ a ∈ s, f a = ∞
  · -- One term is infinite: it takes a large real, the others take `-1`.
    obtain ⟨a₀, ha₀, hfa₀⟩ := ENNReal.sum_eq_top.1 htop
    refine ⟨fun a ↦ -1 + if a = a₀ then r + #s + 1 else 0, fun a _ ↦ ?_, ?_⟩
    · by_cases ha : a = a₀
      · rw [ha, hfa₀, coe_ennreal_top]
        exact coe_lt_top _
      · simp only [ha, ite_false, add_zero]
        exact (EReal.coe_lt_coe_iff.2 (by norm_num : (-1 : ℝ) < 0)).trans_le (coe_ennreal_nonneg _)
    · simp only [sum_add_distrib, sum_const, sum_ite_eq', ha₀, ite_true, _root_.nsmul_eq_mul,
        mul_neg, mul_one]
      linarith
  · -- All terms are finite: each takes its value minus a common margin.
    have hf : ∀ a ∈ s, f a ≠ ∞ := fun a ha h' ↦ htop (ENNReal.sum_eq_top.2 ⟨a, ha, h'⟩)
    rw [← coe_ennreal_toReal htop, EReal.coe_lt_coe_iff, ENNReal.toReal_sum hf] at h
    obtain ⟨δ, hδ, hδr⟩ := exists_pos_lt_sum_sub h
    refine ⟨fun a ↦ (f a).toReal - δ, fun a ha ↦ ?_, mod_cast hδr⟩
    rw [← coe_ennreal_toReal (hf a ha), EReal.coe_lt_coe_iff]
    linarith

/-- **Splitting a real above a sum.** If the sum `∑ a ∈ s, f a` of values in `ℝ≥0∞` is below a
real `r`, then there are reals `g a`, each above `f a`, whose sum is still below `r`. -/
lemma exists_forall_gt_and_sum_lt (h : ((∑ a ∈ s, f a : ℝ≥0∞) : EReal) < r) :
    ∃ g : ι → ℝ, (∀ a ∈ s, (f a : EReal) < g a) ∧ ∑ a ∈ s, g a < r := by
  have htop : ∑ a ∈ s, f a ≠ ∞ := fun h' ↦ by simp [h'] at h
  have hf : ∀ a ∈ s, f a ≠ ∞ := fun a ha h' ↦ htop (ENNReal.sum_eq_top.2 ⟨a, ha, h'⟩)
  rw [← coe_ennreal_toReal htop, EReal.coe_lt_coe_iff, ENNReal.toReal_sum hf] at h
  -- Lower the negated terms below the negated sum.
  obtain ⟨δ, hδ, hδr⟩ := exists_pos_lt_sum_sub (x := fun a ↦ -(f a).toReal) (r := -r)
    (by rw [sum_neg_distrib]; linarith)
  refine ⟨fun a ↦ (f a).toReal + δ, fun a ha ↦ ?_, ?_⟩
  · rw [← coe_ennreal_toReal (hf a ha), EReal.coe_lt_coe_iff]
    linarith
  · simp only [← neg_add', sum_neg_distrib] at hδr
    have : ∑ a ∈ s, ((f a).toReal + δ) < r := by linarith
    exact_mod_cast this

/-- For `w ≥ 0` and `c : ℝ≥0`, the product `w * c` in `ℝ≥0∞`, cast to `EReal`, is the real
`w * c`. -/
private lemma coe_ennreal_ofReal_mul_coe {w : ℝ} (hw : 0 ≤ w) (c : ℝ≥0) :
    ((ENNReal.ofReal w * c : ℝ≥0∞) : EReal) = ((w * c : ℝ) : EReal) := by
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hw, coe_ennreal_ofReal,
    max_eq_left (by positivity)]

/-- For `w > 0`, a real `r` is below `w * c`, for `c : ℝ≥0∞`, if and only if `r / w` is below
`c`. -/
lemma coe_lt_coe_ennreal_ofReal_mul_iff {w : ℝ} (hw : 0 < w) {c : ℝ≥0∞} :
    (r : EReal) < ((ENNReal.ofReal w * c : ℝ≥0∞) : EReal) ↔ ((r / w : ℝ) : EReal) < c := by
  induction c using ENNReal.recTopCoe with
  | top => simp [ENNReal.mul_top (ENNReal.ofReal_pos.2 hw).ne']
  | coe c =>
    rw [coe_ennreal_ofReal_mul_coe hw.le, coe_nnreal_eq_coe_real, EReal.coe_lt_coe_iff,
      EReal.coe_lt_coe_iff, div_lt_iff₀' hw]

/-- For `w > 0`, `w * c`, for `c : ℝ≥0∞`, is below a real `r` if and only if `c` is below
`r / w`. -/
lemma coe_ennreal_ofReal_mul_lt_coe_iff {w : ℝ} (hw : 0 < w) {c : ℝ≥0∞} :
    ((ENNReal.ofReal w * c : ℝ≥0∞) : EReal) < r ↔ (c : EReal) < ((r / w : ℝ) : EReal) := by
  induction c using ENNReal.recTopCoe with
  | top => simp [ENNReal.mul_top (ENNReal.ofReal_pos.2 hw).ne']
  | coe c =>
    rw [coe_ennreal_ofReal_mul_coe hw.le, coe_nnreal_eq_coe_real, EReal.coe_lt_coe_iff,
      EReal.coe_lt_coe_iff, lt_div_iff₀' hw]

end EReal
