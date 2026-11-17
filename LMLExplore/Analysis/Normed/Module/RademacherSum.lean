/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Sum
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
* The law of `∑ i, ε i`: it is `2 X - card ι` for `X` binomial with parameters `card ι` and `1 / 2`
  (`card_filter_le_sum_units`), and it is symmetric (`card_filter_le_abs_sum_units`).

## Main statements

* `LMLExplore.expect_units_apply_mul_eq_zero`: `𝔼 ε i * f ε = 0` when `f` does not depend on
  `ε i`.
* `LMLExplore.expect_sum_units_apply_mul_eq_zero`: `𝔼 ∑ i, ε i * a ε i = 0` for predictable `a`.
* `LMLExplore.expect_sum_units_eq_zero`, `LMLExplore.expect_sum_units_sq`,
  `LMLExplore.expect_sum_units_pow_four`: the first, second and fourth moments of
  `∑ i ∈ s, ε i`.
* `LMLExplore.sqrt_card_div_three_le_expect_abs_sum_units`: `√(#s / 3) ≤ 𝔼 |∑ i ∈ s, ε i|`.
* `LMLExplore.card_filter_le_sum_units`, `LMLExplore.card_filter_le_abs_sum_units`: the number of
  signs with `∑ i, ε i ≥ 2 k - card ι`, and with `|∑ i, ε i| ≥ d`.

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

/-! ### The law of a Rademacher sum -/

omit [DecidableEq ι] in
/-- The sum of the signs is `2 #{i | ε i = 1} - card ι`. -/
theorem sum_units_eq_two_mul_card_sub (ε : ι → ℤˣ) :
    ∑ i, ((ε i : ℤ) : ℝ) = 2 * #{i | ε i = 1} - Fintype.card ι := by
  have h₁ : ∀ i ∈ ({i | ε i = 1} : Finset ι), ((ε i : ℤ) : ℝ) = 1 := fun i hi ↦ by
    simp_all
  have h₂ : ∀ i ∈ ({i | ¬ε i = 1} : Finset ι), ((ε i : ℤ) : ℝ) = -1 := fun i hi ↦ by
    rcases Int.units_eq_one_or (ε i) with h | h <;> simp_all
  have hcard := card_filter_add_card_filter_not (s := univ) (fun i ↦ ε i = 1)
  rw [card_univ] at hcard
  rw [← sum_filter_add_sum_filter_not univ (fun i ↦ ε i = 1), sum_congr rfl h₁,
    sum_congr rfl h₂, ← hcard]
  simp only [sum_const, nsmul_eq_mul, mul_one, mul_neg]
  push_cast
  ring

/-- **The law of a Rademacher sum is a shifted binomial law**: the number of signs `ε` with
`∑ i, ε i ≥ 2 k - card ι` is `∑ i ∈ Icc k (card ι), (card ι).choose i`, the number of subsets of
`ι` with at least `k` elements. -/
theorem card_filter_le_sum_units (k : ℕ) :
    #{ε : ι → ℤˣ | 2 * k - Fintype.card ι ≤ ∑ i, ((ε i : ℤ) : ℝ)} =
      ∑ i ∈ Icc k (Fintype.card ι), (Fintype.card ι).choose i := by
  have hiff (ε : ι → ℤˣ) :
      (2 * k - Fintype.card ι ≤ ∑ i, ((ε i : ℤ) : ℝ)) ↔ k ≤ #{i | ε i = 1} := by
    rw [sum_units_eq_two_mul_card_sub]
    constructor <;> intro h
    · exact_mod_cast (by linarith : (k : ℝ) ≤ #{i | ε i = 1})
    · have : (k : ℝ) ≤ #{i | ε i = 1} := by exact_mod_cast h
      linarith
  simp_rw [hiff]
  -- the signs `ε` correspond to the sets `{i | ε i = 1}`
  have hbij : #{ε : ι → ℤˣ | k ≤ #{i | ε i = 1}} = #{s : Finset ι | k ≤ #s} := by
    refine card_nbij' (fun ε ↦ ({i | ε i = 1} : Finset ι)) (fun s i ↦ if i ∈ s then 1 else -1)
      ?_ ?_ ?_ ?_
    · intro ε hε
      simpa using hε
    · intro s hs
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ⊢
      convert hs using 2
      ext i
      by_cases h : i ∈ s <;> simp [h]
    · intro ε _
      funext i
      rcases Int.units_eq_one_or (ε i) with h | h <;> simp [h]
    · intro s _
      ext i
      by_cases h : i ∈ s <;> simp [h]
  rw [hbij, card_filter, ← powerset_univ,
    sum_powerset_apply_card (fun m ↦ if k ≤ m then 1 else 0), card_univ]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range, mem_Icc]
  omega

/-- **A Rademacher sum is symmetric**: for `d > 0`, the signs `ε` with `|∑ i, ε i| ≥ d` are twice
as many as those with `∑ i, ε i ≥ d`. -/
theorem card_filter_le_abs_sum_units {d : ℝ} (hd : 0 < d) :
    #{ε : ι → ℤˣ | d ≤ |∑ i, ((ε i : ℤ) : ℝ)|} =
      2 * #{ε : ι → ℤˣ | d ≤ ∑ i, ((ε i : ℤ) : ℝ)} := by
  set P := univ.filter fun ε : ι → ℤˣ ↦ d ≤ ∑ i, ((ε i : ℤ) : ℝ)
  set N := univ.filter fun ε : ι → ℤˣ ↦ ∑ i, ((ε i : ℤ) : ℝ) ≤ -d
  have hunion : univ.filter (fun ε : ι → ℤˣ ↦ d ≤ |∑ i, ((ε i : ℤ) : ℝ)|) = P ∪ N := by
    ext ε
    simp only [P, N, mem_filter, mem_univ, true_and, mem_union, le_abs']
    tauto
  have hdisj : Disjoint P N := by
    rw [disjoint_filter]
    intro ε _ h h'
    linarith
  -- flipping all the signs exchanges the two tails
  have hneg : #N = #P := by
    refine card_nbij' (fun ε ↦ -ε) (fun ε ↦ -ε) ?_ ?_ ?_ ?_ <;> intro ε hε
    · simp only [P, N, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Pi.neg_apply,
        Units.val_neg, Int.cast_neg, sum_neg_distrib] at hε ⊢
      linarith
    · simp only [P, N, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Pi.neg_apply,
        Units.val_neg, Int.cast_neg, sum_neg_distrib] at hε ⊢
      linarith
    · exact neg_neg ε
    · exact neg_neg ε
  rw [hunion, card_union_of_disjoint hdisj, hneg, two_mul]

end LMLExplore
