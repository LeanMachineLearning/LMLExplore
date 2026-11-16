/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Analysis.Normed.Module.RademacherSum.Basic

/-!
# Moments of real Rademacher sums

Independent Rademacher signs `ε i ∈ {-1, 1}`, `i ∈ ι`, are the uniform average over the finite
sign cube `ι → ℤˣ`, as in Tau Ceti's `TauCeti.rademacherSecondMoment`. This file proves the facts
about the real Rademacher sums `∑ i ∈ s, ε i` that the lower bounds of online learning use.

* A sign times a function of the other signs averages to zero
  (`expect_units_apply_mul_eq_zero`). In particular, if `ι` is ordered (the rounds of a game) and
  `a ε i` depends only on the signs `ε j` with `j < i`, then `∑ i, ε i * a ε i` averages to zero
  (`expect_sum_units_apply_mul_eq_zero`): the signs are the increments of a martingale, and
  `a` is predictable. This is why an adversary playing random signs makes the expected loss of
  every learner vanish.
* The first, second and fourth moments: `𝔼 ∑ i ∈ s, ε i = 0`, `𝔼 (∑ i ∈ s, ε i) ^ 2 = #s` and
  `𝔼 (∑ i ∈ s, ε i) ^ 4 = 3 #s ^ 2 - 2 #s`.
* The lower Khintchine inequality in `L¹` with the constant `1 / √3`:
  `√(#s / 3) ≤ 𝔼 |∑ i ∈ s, ε i|` [Ora, Theorem A.14]. It follows from the two moments through the
  pointwise inequality `3 c ^ 2 x ^ 2 - x ^ 4 ≤ 2 c ^ 3 |x|` with `c = √(3 #s)`, a form of Hölder's
  inequality `(𝔼 S ^ 2) ^ 3 ≤ (𝔼 |S|) ^ 2 𝔼 S ^ 4`. The sharp constant `1 / √2` is Szarek's.

## Main statements

* `LMLExplore.expect_units_apply_mul_eq_zero`: `𝔼 ε i * f ε = 0` when `f` does not depend on
  `ε i`.
* `LMLExplore.expect_sum_units_apply_mul_eq_zero`: `𝔼 ∑ i, ε i * a ε i = 0` for predictable `a`.
* `LMLExplore.expect_sum_units_eq_zero`, `LMLExplore.expect_sum_units_sq`,
  `LMLExplore.expect_sum_units_pow_four`: the first, second and fourth moments of
  `∑ i ∈ s, ε i`.
* `LMLExplore.sqrt_card_div_three_le_expect_abs_sum_units`: `√(#s / 3) ≤ 𝔼 |∑ i ∈ s, ε i|`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* S. J. Szarek, *On the best constants in the Khinchin inequality*, Studia Math. 58 (1976).
-/

public section

open Finset
open scoped BigOperators

namespace LMLExplore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A sign is orthogonal to the other signs**: averaged over the sign cube, the product of the
sign `ε i` with a function of the other signs vanishes. -/
theorem expect_units_apply_mul_eq_zero (i : ι) {f : (ι → ℤˣ) → ℝ}
    (hf : ∀ ε ε' : ι → ℤˣ, (∀ j ≠ i, ε j = ε' j) → f ε = f ε') :
    𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) * f ε = 0 := by
  -- Flipping the sign of the `i`-th coordinate negates every term.
  let σ := Equiv.mulLeft (Pi.mulSingle i (-1) : ι → ℤˣ)
  have hσ (ε : ι → ℤˣ) (j : ι) : σ ε j = if j = i then -ε j else ε j := by
    by_cases hj : j = i
    · subst hj; simp [σ]
    · simp [σ, hj]
  have h := Fintype.expect_equiv σ (fun ε ↦ -(((ε i : ℤ) : ℝ) * f ε))
    (fun ε ↦ ((ε i : ℤ) : ℝ) * f ε) fun ε ↦ by
      rw [hf (σ ε) ε fun j hj ↦ by simp [hσ, hj], hσ]
      simp
  rw [expect_neg_distrib] at h
  linarith

/-- A Rademacher sign has mean zero. -/
@[simp]
theorem expect_units_apply_eq_zero (i : ι) : 𝔼 ε : ι → ℤˣ, ((ε i : ℤ) : ℝ) = 0 := by
  simpa using expect_units_apply_mul_eq_zero i (f := fun _ ↦ 1) fun _ _ _ ↦ rfl

/-- The **first moment** of a Rademacher sum: `𝔼 ∑ i ∈ s, ε i = 0`. -/
@[simp]
theorem expect_sum_units_eq_zero (s : Finset ι) :
    𝔼 ε : ι → ℤˣ, ∑ i ∈ s, ((ε i : ℤ) : ℝ) = 0 := by
  rw [expect_sum_comm]
  exact sum_eq_zero fun i _ ↦ expect_units_apply_eq_zero i

/-- **Predictable sums of signs have mean zero.** If the weight `a ε i` of the sign `ε i`
depends only on the signs `ε j` of the indices `j < i`, then `∑ i, ε i * a ε i` averages to zero
over the sign cube. -/
theorem expect_sum_units_apply_mul_eq_zero [Preorder ι] {a : (ι → ℤˣ) → ι → ℝ}
    (ha : ∀ (ε ε' : ι → ℤˣ) (i : ι), (∀ j < i, ε j = ε' j) → a ε i = a ε' i) :
    𝔼 ε : ι → ℤˣ, ∑ i, ((ε i : ℤ) : ℝ) * a ε i = 0 := by
  rw [expect_sum_comm]
  exact sum_eq_zero fun i _ ↦ expect_units_apply_mul_eq_zero i fun ε ε' h ↦
    ha ε ε' i fun j hj ↦ h j hj.ne

/-- The **second moment** of a Rademacher sum: `𝔼 (∑ i ∈ s, ε i) ^ 2 = #s`. -/
@[simp]
theorem expect_sum_units_sq (s : Finset ι) :
    𝔼 ε : ι → ℤˣ, (∑ i ∈ s, ((ε i : ℤ) : ℝ)) ^ 2 = #s := by
  have h := TauCeti.expect_norm_sum_units_smul_sq ℝ fun i : ι ↦ if i ∈ s then (1 : ℝ) else 0
  simpa [Units.smul_def, sum_ite_mem, sq_abs] using h

/-- The **fourth moment** of a Rademacher sum: `𝔼 (∑ i ∈ s, ε i) ^ 4 = 3 #s ^ 2 - 2 #s`. -/
@[simp]
theorem expect_sum_units_pow_four (s : Finset ι) :
    𝔼 ε : ι → ℤˣ, (∑ i ∈ s, ((ε i : ℤ) : ℝ)) ^ 4 = 3 * (#s : ℝ) ^ 2 - 2 * #s := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    -- With `e = ε a` and `S = ∑ i ∈ s, ε i`,
    -- `(e + S) ^ 4 = 1 + 6 S ^ 2 + S ^ 4 + e (4 S + 4 S ^ 3)`, and the last term averages to zero
    -- since `S` does not depend on `ε a`.
    have h (ε : ι → ℤˣ) : (∑ i ∈ insert a s, ((ε i : ℤ) : ℝ)) ^ 4 =
        1 + 6 * (∑ i ∈ s, ((ε i : ℤ) : ℝ)) ^ 2 + (∑ i ∈ s, ((ε i : ℤ) : ℝ)) ^ 4 +
          ((ε a : ℤ) : ℝ) *
            (4 * ∑ i ∈ s, ((ε i : ℤ) : ℝ) + 4 * (∑ i ∈ s, ((ε i : ℤ) : ℝ)) ^ 3) := by
      have he : ((ε a : ℤ) : ℝ) ^ 2 = 1 := by
        rw [← sq_abs, abs_unit_intCast, one_pow]
      rw [sum_insert ha]
      linear_combination (((ε a : ℤ) : ℝ) ^ 2 + 1 + 4 * (∑ i ∈ s, ((ε i : ℤ) : ℝ)) * (ε a : ℤ) +
        6 * (∑ i ∈ s, ((ε i : ℤ) : ℝ)) ^ 2) * he
    have h0 : 𝔼 ε : ι → ℤˣ, ((ε a : ℤ) : ℝ) *
        (4 * ∑ i ∈ s, ((ε i : ℤ) : ℝ) + 4 * (∑ i ∈ s, ((ε i : ℤ) : ℝ)) ^ 3) = 0 := by
      refine expect_units_apply_mul_eq_zero a fun ε ε' hεε' ↦ ?_
      rw [sum_congr rfl fun j hj ↦ by rw [hεε' j (ne_of_mem_of_not_mem hj ha)]]
    simp_rw [h, expect_add_distrib, h0, ← mul_expect, expect_sum_units_sq, ih,
      card_insert_of_notMem ha, Fintype.expect_const]
    push_cast
    ring

/-- The **lower Khintchine inequality** in `L¹`: a Rademacher sum of `#s` signs has mean absolute
value at least `√(#s / 3)` [Ora, Theorem A.14, with the constant `1 / √3` in place of Szarek's
`1 / √2`]. -/
theorem sqrt_card_div_three_le_expect_abs_sum_units (s : Finset ι) :
    √((#s : ℝ) / 3) ≤ 𝔼 ε : ι → ℤˣ, |∑ i ∈ s, ((ε i : ℤ) : ℝ)| := by
  have hm : 0 ≤ 𝔼 ε : ι → ℤˣ, |∑ i ∈ s, ((ε i : ℤ) : ℝ)| := expect_nonneg fun _ _ ↦ abs_nonneg _
  rcases (Nat.cast_nonneg #s : (0 : ℝ) ≤ #s).eq_or_lt with hn | hn
  · rw [← hn, zero_div, Real.sqrt_zero]
    exact hm
  -- The pointwise inequality `3 c ^ 2 x ^ 2 - x ^ 4 ≤ 2 c ^ 3 |x|` for `c ≥ 0`, that is,
  -- `0 ≤ |x| (|x| - c) ^ 2 (|x| + 2 c)`, averaged with `c = √(3 #s)`.
  have key {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 3 * c ^ 2 * x ^ 2 - x ^ 4 ≤ 2 * c ^ 3 * |x| := by
    have hx := abs_nonneg x
    have h := mul_nonneg (mul_nonneg hx (sq_nonneg (|x| - c))) (by positivity : 0 ≤ |x| + 2 * c)
    have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have h4 : x ^ 4 = (|x| ^ 2) ^ 2 := by rw [← h2]; ring
    rw [h4, h2]
    nlinarith [h]
  have hc : 0 < √(3 * (#s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hc2 : √(3 * (#s : ℝ)) ^ 2 = 3 * #s := Real.sq_sqrt (by positivity)
  have h := expect_le_expect (s := univ) fun (ε : ι → ℤˣ) _ ↦
    key hc.le (∑ i ∈ s, ((ε i : ℤ) : ℝ))
  rw [expect_sub_distrib, ← mul_expect, ← mul_expect, expect_sum_units_sq,
    expect_sum_units_pow_four] at h
  generalize √(3 * (#s : ℝ)) = c at hc hc2 h
  generalize 𝔼 ε : ι → ℤˣ, |∑ i ∈ s, ((ε i : ℤ) : ℝ)| = m at hm h ⊢
  generalize (#s : ℝ) = n at hn hc2 h ⊢
  -- `h : 3 c ^ 2 n - (3 n ^ 2 - 2 n) ≤ 2 c ^ 3 m` with `c ^ 2 = 3 n`, so `n ≤ c m` and
  -- `n / 3 ≤ m ^ 2`.
  have hc3 : c ^ 3 = 3 * n * c := by rw [pow_succ, hc2]
  rw [hc2, hc3] at h
  have hcm : n ≤ c * m := by nlinarith
  have hn2 : n ^ 2 ≤ 3 * n * m ^ 2 := by
    rw [← hc2]
    nlinarith [mul_le_mul hcm hcm hn.le (by positivity)]
  rw [Real.sqrt_le_left hm, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  nlinarith

end LMLExplore
