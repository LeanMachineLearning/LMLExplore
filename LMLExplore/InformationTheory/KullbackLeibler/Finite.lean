/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.Analysis.Convex.Simplex
public import LMLExplore.Analysis.SpecialFunctions.Log.NegMulLog
public import LMLExplore.InformationTheory.KullbackLeibler.Bernoulli

/-!
# The relative entropy of vectors on a finite type

For nonnegative vectors `x z : α → ℝ` on a finite type `α`, with `x a = 0` whenever `z a = 0`, the
relative entropy of `x` with respect to `z` is `∑ a, x a * log (x a / z a)`. When `x` and `z` are
probability vectors, it is the Kullback–Leibler divergence of the corresponding laws on `α`.

**Gibbs' inequality** states that it is nonnegative as soon as `∑ a, z a ≤ ∑ a, x a`; it follows
from the log-sum inequality. **Pinsker's inequality** for probability vectors reads
`(∑ a, |x a - z a|) ^ 2 ≤ 2 ∑ a, x a * log (x a / z a)`, and is deduced from the binary case
`LMLExplore.two_mul_sq_le_klBerReal` by the log-sum inequality on two blocks [CT, Lemma 11.6.1].
In particular, the relative entropy of two probability vectors vanishes only when they are equal.

## Main statements

* `LMLExplore.sum_mul_log_div_nonneg`: Gibbs' inequality.
* `LMLExplore.sq_sum_abs_sub_le_two_mul_sum_mul_log_div`: Pinsker's inequality for probability
  vectors.
* `LMLExplore.sum_mul_log_div_eq_zero_iff`: the relative entropy of two probability vectors
  vanishes if and only if they are equal.

## References

* [CT] T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006.
-/

public section

open Finset Real
open scoped ENNReal

namespace LMLExplore

variable {α : Type*} [Fintype α]

/-- **Gibbs' inequality**: for nonnegative vectors `x` and `z` with `x a = 0` whenever `z a = 0`
and `∑ a, z a ≤ ∑ a, x a`, the relative entropy `∑ a, x a * log (x a / z a)` is nonnegative. This
holds in particular for two probability vectors. -/
theorem sum_mul_log_div_nonneg {x z : α → ℝ} (hx : ∀ a, 0 ≤ x a) (hz : ∀ a, 0 ≤ z a)
    (hxz : ∀ a, z a = 0 → x a = 0) (hsum : ∑ a, z a ≤ ∑ a, x a) :
    0 ≤ ∑ a, x a * log (x a / z a) := by
  refine le_trans ?_ (sum_mul_log_div_sum_le_sum_mul_log_div univ (fun a _ ↦ hx a)
    (fun a _ ↦ hz a) fun a _ ↦ hxz a)
  rcases (sum_nonneg fun a (_ : a ∈ univ) ↦ hz a).eq_or_lt with hZ | hZ
  · rw [← hZ, div_zero, log_zero, mul_zero]
  · exact mul_nonneg (sum_nonneg fun a _ ↦ hx a) (log_nonneg ((one_le_div hZ).2 hsum))

/-- **Pinsker's inequality** for probability vectors: if `x` and `z` lie in the simplex and
`x a = 0` whenever `z a = 0`, then `(∑ a, |x a - z a|) ^ 2 ≤ 2 ∑ a, x a * log (x a / z a)`.
The sum on the right is the relative entropy of `x` with respect to `z`. The proof follows
[CT, Lemma 11.6.1]: the log-sum inequality on the set where `x` is above `z` and on its complement
reduces it to the binary case `two_mul_sq_le_klBerReal`. -/
theorem sq_sum_abs_sub_le_two_mul_sum_mul_log_div {x z : α → ℝ} (hx : x ∈ simplex α)
    (hz : z ∈ simplex α) (hxz : ∀ a, z a = 0 → x a = 0) :
    (∑ a, |x a - z a|) ^ 2 ≤ 2 * ∑ a, x a * log (x a / z a) := by
  classical
  obtain ⟨hx0, hx1⟩ := mem_simplex_iff.1 hx
  obtain ⟨hz0, hz1⟩ := mem_simplex_iff.1 hz
  -- the masses `p` and `q` of `x` and `z` on the set where `x` is above `z`
  set p := ∑ a with z a ≤ x a, x a
  set q := ∑ a with z a ≤ x a, z a
  have hpc : ∑ a with ¬z a ≤ x a, x a = 1 - p := by
    rw [← hx1, ← sum_filter_add_sum_filter_not univ (fun a ↦ z a ≤ x a)]
    ring
  have hqc : ∑ a with ¬z a ≤ x a, z a = 1 - q := by
    rw [← hz1, ← sum_filter_add_sum_filter_not univ (fun a ↦ z a ≤ x a)]
    ring
  have hp0 : 0 ≤ p := sum_nonneg fun a _ ↦ hx0 a
  have hq0 : 0 ≤ q := sum_nonneg fun a _ ↦ hz0 a
  have hp1 : 0 ≤ 1 - p := hpc ▸ sum_nonneg fun a _ ↦ hx0 a
  have hq1 : 0 ≤ 1 - q := hqc ▸ sum_nonneg fun a _ ↦ hz0 a
  -- the `ℓ¹` distance is `2 (p - q)`
  have h_abs : ∑ a, |x a - z a| = 2 * (p - q) := by
    rw [← sum_filter_add_sum_filter_not univ (fun a ↦ z a ≤ x a),
      sum_congr rfl fun a ha ↦ abs_of_nonneg (sub_nonneg.2 (mem_filter.1 ha).2),
      sum_congr rfl fun a ha ↦ abs_of_neg (sub_neg.2 (not_le.1 (mem_filter.1 ha).2)),
      sum_sub_distrib, sum_neg_distrib, sum_sub_distrib, hpc, hqc]
    ring
  -- the log-sum inequality on both blocks bounds the relative entropy below by `d(p, q)`
  have h_blocks : klBerReal p q ≤ ∑ a, x a * log (x a / z a) := by
    rw [← sum_filter_add_sum_filter_not univ (fun a ↦ z a ≤ x a), klBerReal_def, ← hpc, ← hqc]
    exact add_le_add
      (sum_mul_log_div_sum_le_sum_mul_log_div _ (fun a _ ↦ hx0 a) (fun a _ ↦ hz0 a)
        fun a _ ↦ hxz a)
      (sum_mul_log_div_sum_le_sum_mul_log_div _ (fun a _ ↦ hx0 a) (fun a _ ↦ hz0 a)
        fun a _ ↦ hxz a)
  -- `d(p, q)` is finite, since `q = 0` forces `p = 0` and `q = 1` forces `p = 1`
  have h_fin : klBer p q ≠ ∞ := by
    rw [klBer_ne_top_iff ⟨hp0, by linarith⟩ ⟨hq0, by linarith⟩]
    refine ⟨fun hq ↦ sum_eq_zero fun a ha ↦ hxz a ?_, fun hq ↦ ?_⟩
    · exact (sum_eq_zero_iff_of_nonneg fun b _ ↦ hz0 b).1 hq a ha
    · have h0 : ∑ a with ¬z a ≤ x a, x a = 0 := sum_eq_zero fun a ha ↦ hxz a
        ((sum_eq_zero_iff_of_nonneg fun b _ ↦ hz0 b).1 (by rw [hqc, hq, sub_self]) a ha)
      linarith
  have h_pinsker := two_mul_sq_le_klBerReal ⟨hp0, by linarith⟩ ⟨hq0, by linarith⟩ h_fin
  rw [h_abs]
  nlinarith

/-- The relative entropy of two probability vectors `x` and `z`, with `x a = 0` whenever
`z a = 0`, vanishes if and only if `x = z`. The forward direction follows from Pinsker's
inequality. -/
theorem sum_mul_log_div_eq_zero_iff {x z : α → ℝ} (hx : x ∈ simplex α) (hz : z ∈ simplex α)
    (hxz : ∀ a, z a = 0 → x a = 0) : ∑ a, x a * log (x a / z a) = 0 ↔ x = z := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have h_pinsker := sq_sum_abs_sub_le_two_mul_sum_mul_log_div hx hz hxz
  rw [h, mul_zero] at h_pinsker
  have h_sum : ∑ a, |x a - z a| = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h_pinsker (sq_nonneg _))
  funext a
  exact sub_eq_zero.1 (abs_eq_zero.1
    ((sum_eq_zero_iff_of_nonneg fun a _ ↦ abs_nonneg _).1 h_sum a (mem_univ a)))

end LMLExplore
