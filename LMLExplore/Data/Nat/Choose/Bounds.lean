/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Bounds on binomial and multinomial coefficients

Two classical upper bounds on the number of words with prescribed letter counts.

* `Nat.choose_le_exp_one_mul_div_pow`: `n.choose k ≤ (e n / k) ^ k`, from Mathlib's
  `Nat.choose_le_pow_div` and `k ^ k / k! ≤ e ^ k`.
* `Nat.multinomial_mul_prod_pow_le_one`: for a probability vector `p` on `s`, the term
  `multinomial s f * ∏ i ∈ s, p i ^ f i` of the multinomial expansion of `(∑ i ∈ s, p i) ^ n` is at
  most `1`. It is the probability of the counts `f` in `n` independent draws from `p`. With
  `p i = f i / n`, it bounds the maximum likelihood `∏ i ∈ s, (f i / n) ^ f i` of a word with counts
  `f` by `∏ i ∈ s, (f i)! / n!`.

Both bounds control the likelihood ratios of universal (mixture) predictors against the maximum
likelihood, as in the analysis of Laplace's rule of succession.
-/

public section

open Finset Real
open scoped Nat

namespace Nat

/-- **Binomial coefficients are at most `(e n / k) ^ k`.** -/
theorem choose_le_exp_one_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (exp 1 * n / k) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  -- `k ^ k / k! ≤ e ^ k`
  have hfact : (k : ℝ) ^ k / k ! ≤ exp 1 ^ k := by
    rw [← exp_nat_mul, mul_one]
    exact pow_div_factorial_le_exp _ hkR.le k
  calc (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k ! := choose_le_pow_div k n
    _ = ((n : ℝ) / k) ^ k * ((k : ℝ) ^ k / k !) := by
        rw [div_pow]
        field_simp
    _ ≤ ((n : ℝ) / k) ^ k * exp 1 ^ k := by gcongr
    _ = (exp 1 * n / k) ^ k := by rw [← mul_pow, mul_comm, mul_div_assoc]

/-- **A multinomial probability is at most one**: for `p` nonnegative on `s` with
`∑ i ∈ s, p i = 1`, `multinomial s f * ∏ i ∈ s, p i ^ f i ≤ 1`. This term of the multinomial
expansion of `(∑ i ∈ s, p i) ^ (∑ i ∈ s, f i)` is the probability of the counts `f` under
independent draws from `p`. -/
theorem multinomial_mul_prod_pow_le_one {R ι : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] (s : Finset ι) (f : ι → ℕ) {p : ι → R} (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∑ i ∈ s, p i = 1) :
    (multinomial s f : R) * ∏ i ∈ s, p i ^ f i ≤ 1 := by
  classical
  -- the counts `f`, set to `0` outside `s`, are a term of the multinomial expansion
  set g : ι → ℕ := fun i ↦ if i ∈ s then f i else 0 with hg
  have hgf : ∀ i ∈ s, g i = f i := fun i hi ↦ by simp [hg, hi]
  have hg_mem : g ∈ piAntidiag s (∑ i ∈ s, f i) := by
    rw [mem_piAntidiag]
    refine ⟨sum_congr rfl hgf, fun i hi ↦ ?_⟩
    by_contra his
    simp [hg, his] at hi
  have hexp := sum_pow_eq_sum_piAntidiag s p (∑ i ∈ s, f i)
  rw [hp1, one_pow] at hexp
  rw [multinomial_congr (fun i hi ↦ (hgf i hi).symm),
    prod_congr rfl fun i hi ↦ by rw [← hgf i hi], hexp]
  exact single_le_sum (f := fun k ↦ (multinomial s k : R) * ∏ i ∈ s, p i ^ k i)
    (fun k _ ↦ mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun i hi ↦ pow_nonneg (hp0 i hi) _))
    hg_mem

end Nat
