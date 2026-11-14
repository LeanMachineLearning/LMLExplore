/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weighted sums of an antitone function and its integral

Mathlib's `AntitoneOn.sum_le_integral` compares the values of an antitone function at the
integers with its integral. Its weighted form compares the values at the partial sums of a
nonnegative sequence: for `f` antitone on `(c, c + ∑_{t < n} a t]` and `a t ≥ 0`,
`∑_{t < n} a t f (c + ∑_{s ≤ t} a s) ≤ ∫_c^{c + ∑_{t < n} a t} f`.

Adaptive learning rates of online learning are of the form `η_t ∝ f (∑_{s ≤ t} a s)`, where
`a s` is the squared norm of the subgradient of round `s` (as in AdaGrad), and the regret bounds
sum the terms `a t f (∑_{s ≤ t} a s)`. The two instances below are the ones these bounds use.

## Main statements

* `AntitoneOn.sum_mul_le_integral_of_integrableOn`: the weighted comparison [Ora, Lemma 4.13].
* `Real.sum_div_sqrt_le_two_mul_sqrt`: `∑_{t < n} a t / √(∑_{s ≤ t} a s) ≤ 2 √(∑_{t < n} a t)`
  for `a t ≥ 0`, the case `f x = 1 / √x`.
* `Real.sum_div_add_le_log_div`: `∑_{t < n} a t / (c + ∑_{s ≤ t} a s) ≤ log ((c + ∑_t a t) / c)`
  for `a t ≥ 0` and `c > 0`, the case `f x = 1 / x`.

In the first, a term whose denominator vanishes has `a t = 0`, and Lean's convention `x / 0 = 0`
omits it, as [Ora] does.

## References

* [Ora] F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213v10, Lemma 4.13.
-/

public section

open Finset MeasureTheory Set intervalIntegral

variable {f : ℝ → ℝ} {c : ℝ} {a : ℕ → ℝ} {n : ℕ}

/-- **Weighted sums of an antitone function** [Ora, Lemma 4.13]. Let `a t ≥ 0` for `t < n`, and
let `f` be antitone on `(c, c + ∑_{t < n} a t]` and integrable on `[c, c + ∑_{t < n} a t]`. Then
`∑_{t < n} a t f (c + ∑_{s ≤ t} a s) ≤ ∫_c^{c + ∑_{t < n} a t} f`.

The sign of `f` and its value at `c` play no role. With `a t = 1` it is Mathlib's
`AntitoneOn.sum_le_integral_of_integrableOn`. -/
theorem AntitoneOn.sum_mul_le_integral_of_integrableOn
    (hf : AntitoneOn f (Ioc c (c + ∑ t ∈ range n, a t)))
    (hfi : IntegrableOn f (Icc c (c + ∑ t ∈ range n, a t))) (ha : ∀ t < n, 0 ≤ a t) :
    ∑ t ∈ range n, a t * f (c + ∑ s ∈ range (t + 1), a s) ≤
      ∫ x in c..c + ∑ t ∈ range n, a t, f x := by
  set S : ℕ → ℝ := fun t ↦ c + ∑ s ∈ range t, a s with hS
  -- each term is at most the integral of `f` over `[S t, S (t + 1)]`, an interval of length
  -- `a t` on which `f` is at least its value at the right endpoint
  -- the partial sums `S t` increase from `S 0 = c` to `S n` on `[0, n]`
  have hmono : ∀ {k l}, k ≤ l → l ≤ n → S k ≤ S l := fun hkl hl ↦
    add_le_add le_rfl (sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hkl)
      fun t ht _ ↦ ha t ((mem_range.1 ht).trans_le hl))
  have hc : ∀ {t}, t ≤ n → c ≤ S t := fun ht ↦ by simpa [hS] using hmono (Nat.zero_le _) ht
  have hint : ∀ t < n, IntervalIntegrable f volume (S t) (S (t + 1)) := fun t ht ↦
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hmono t.le_succ ht)).2
      (hfi.mono_set (Set.Icc_subset_Icc (hc ht.le) (hmono ht le_rfl)))
  calc ∑ t ∈ range n, a t * f (S (t + 1))
      = ∑ t ∈ range n, ∫ _ in S t..S (t + 1), f (S (t + 1)) := by
        refine sum_congr rfl fun t _ ↦ ?_
        simp [hS, sum_range_succ]
    _ ≤ ∑ t ∈ range n, ∫ x in S t..S (t + 1), f x := by
        refine sum_le_sum fun t ht ↦ ?_
        have ht : t < n := mem_range.1 ht
        refine integral_mono_on_of_le_Ioo (hmono t.le_succ ht) intervalIntegrable_const
          (hint t ht) fun x hx ↦ ?_
        have h0 : c ≤ S t := hc ht.le
        have hn : S (t + 1) ≤ S n := hmono ht le_rfl
        exact hf ⟨h0.trans_lt hx.1, hx.2.le.trans hn⟩ ⟨h0.trans_lt (hx.1.trans hx.2), hn⟩
          hx.2.le
    _ = ∫ x in c..c + ∑ t ∈ range n, a t, f x := by
        rw [sum_integral_adjacent_intervals hint]
        simp [hS]

namespace Real

/-- **The square-root sum** [Ora, Lemma 4.13]: for `a t ≥ 0`,
`∑_{t < n} a t / √(∑_{s ≤ t} a s) ≤ 2 √(∑_{t < n} a t)`.

A term whose denominator vanishes is `0` (then `a t = 0`). It is the sum of the stability terms
of online subgradient descent with the adaptive rates `η_t ∝ 1 / √(∑_{s ≤ t} ‖g_s‖²)`. -/
theorem sum_div_sqrt_le_two_mul_sqrt (ha : ∀ t < n, 0 ≤ a t) :
    ∑ t ∈ range n, a t / √(∑ s ∈ range (t + 1), a s) ≤ 2 * √(∑ t ∈ range n, a t) := by
  set A := ∑ t ∈ range n, a t
  have hA : 0 ≤ A := sum_nonneg fun t ht ↦ ha t (mem_range.1 ht)
  -- `1 / √x = x ^ (-1 / 2)` on `[0, A]`, including at `0`, where both sides are `0`
  have heq : EqOn (fun x : ℝ ↦ (√x)⁻¹) (fun x ↦ x ^ (-1 / 2 : ℝ)) (uIcc 0 A) := fun x hx ↦ by
    rw [uIcc_of_le hA] at hx
    simp only [sqrt_eq_rpow, neg_div, rpow_neg hx.1, one_div]
  have hint : IntervalIntegrable (fun x : ℝ ↦ (√x)⁻¹) volume 0 A :=
    (intervalIntegral.intervalIntegrable_rpow' (r := -1 / 2) (by norm_num)).congr
      (heq.symm.mono uIoc_subset_uIcc)
  have hanti : AntitoneOn (fun x : ℝ ↦ (√x)⁻¹) (Ioc 0 (0 + A)) := fun x hx y _ hxy ↦
    inv_anti₀ (sqrt_pos.2 hx.1) (sqrt_le_sqrt hxy)
  have h := hanti.sum_mul_le_integral_of_integrableOn
    (by simpa using (intervalIntegrable_iff_integrableOn_Icc_of_le hA).1 hint) ha
  rw [zero_add, integral_congr heq, integral_rpow (Or.inl (by norm_num))] at h
  simp_rw [zero_add, ← div_eq_mul_inv] at h
  refine h.trans_eq ?_
  rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_rpow (by norm_num), sqrt_eq_rpow]
  ring

/-- **The logarithmic sum** [Ora, Lemma 4.13]: for `a t ≥ 0` and `c > 0`,
`∑_{t < n} a t / (c + ∑_{s ≤ t} a s) ≤ log ((c + ∑_{t < n} a t) / c)`.

It is the sum of the stability terms of online learning with the rates
`η_t ∝ 1 / (c + ∑_{s ≤ t} a s)`, as for strongly convex and exp-concave losses. -/
theorem sum_div_add_le_log_div (hc : 0 < c) (ha : ∀ t < n, 0 ≤ a t) :
    ∑ t ∈ range n, a t / (c + ∑ s ∈ range (t + 1), a s) ≤
      log ((c + ∑ t ∈ range n, a t) / c) := by
  set A := ∑ t ∈ range n, a t
  have hA : 0 ≤ A := sum_nonneg fun t ht ↦ ha t (mem_range.1 ht)
  have hanti : AntitoneOn (fun x : ℝ ↦ x⁻¹) (Ioc c (c + A)) := fun x hx y _ hxy ↦
    inv_anti₀ (hc.trans hx.1) hxy
  have hcont : ContinuousOn (fun x : ℝ ↦ x⁻¹) (Icc c (c + A)) :=
    continuousOn_inv₀.mono fun x hx ↦ (hc.trans_le hx.1).ne'
  have h := hanti.sum_mul_le_integral_of_integrableOn hcont.integrableOn_Icc ha
  simp_rw [← div_eq_mul_inv] at h
  exact h.trans_eq (integral_inv_of_pos hc (by linarith))

end Real
