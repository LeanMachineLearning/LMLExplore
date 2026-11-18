/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LMLExplore.Analysis.Real.Sqrt
import LMLExplore.Analysis.SpecialFunctions.Log.Basic

/-!
# Weighted sums of an antitone function and its integral, and sums over a lagging counter

Mathlib's `AntitoneOn.sum_le_integral` compares the values of an antitone function at the
integers with its integral. Its weighted form compares the values at the partial sums of a
nonnegative sequence: for `f` antitone on `(c, c + ∑_{t < n} a t]` and integrable on
`[c, c + ∑_{t < n} a t]`, and `a t ≥ 0`,
`∑_{t < n} a t f (c + ∑_{s ≤ t} a s) ≤ ∫_c^{c + ∑_{t < n} a t} f`.

Adaptive learning rates of online learning are of the form `η_t ∝ f (∑_{s ≤ t} a s)`, where
`a s` is the squared norm of the subgradient of round `s` (as in AdaGrad), and the regret bounds
sum the terms `a t f (∑_{s ≤ t} a s)`. The two instances below, and an offset form of the
first for rates that only use the past rounds, are the ones these bounds use.

The same sums appear when a natural number `N s` lags behind the partial sums `∑_{r < s} a r` by
at most a constant `c`, as the pull counts of a tracking rule lag behind the cumulated targets.
The last three bounds control `∑_{s < n} a s / √(N s)` and `∑_{s < n} a s / N s` in that case:
they bound the sums of the confidence widths of a bandit algorithm that tracks a sequence of
allocations [DKM19, Lemma 9].

## Main statements

* `AntitoneOn.sum_mul_le_integral_of_integrableOn`: the weighted comparison [Ora, Lemma 4.13].
* `Real.sum_div_sqrt_le_two_mul_sqrt`: `∑_{t < n} a t / √(∑_{s ≤ t} a s) ≤ 2 √(∑_{t < n} a t)`
  for `a t ≥ 0`, the case `f x = 1 / √x`.
* `Real.sum_div_sqrt_add_le_two_mul_sqrt`: the same bound with the denominators
  `√(M + ∑_{s < t} a s)`, for `0 ≤ a t ≤ M`.
* `Real.sum_div_add_le_log_div`: `∑_{t < n} a t / (c + ∑_{s ≤ t} a s) ≤ log ((c + ∑_t a t) / c)`
  for `a t ≥ 0` and `c > 0`, the case `f x = 1 / x`.
* `Real.sum_div_sqrt_le_add_two_mul_sqrt`: if `c ≥ 0`, `a s ≥ 0` and
  `∑_{r ≤ s} a r - c ≤ N s`, then `∑_{s < n} a s / √(N s) ≤ c + 2 √(∑_{s < n} a s)`.
* `Real.sum_div_sqrt_le_add_mul_sqrt`: if `c ≥ 0`, `0 ≤ a s ≤ 1` and
  `∑_{r < s} a r - c ≤ N s`, then `∑_{s < n} a s / √(N s) ≤ c + (√2 + 1) √(∑_{s < n} a s)`.
* `Real.sum_div_le_add_three_mul_log`: under the same assumptions,
  `∑_{s < n} a s / N s ≤ c + 3 log (∑_{s < n} a s + 1)`.

In the first, a term whose denominator vanishes has `a t = 0`, and Lean's convention `x / 0 = 0`
omits it, as [Ora] does. In the last three, the terms with `N s = 0` are `0` for the same reason.

## References

* [Ora] F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213v10, Lemma 4.13.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Lemmas 9 and 16 (in the numbering of arXiv:1906.10431).
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

/-- **The square-root sum, offset** [Ora, Lemma 4.13]: for `0 ≤ a t ≤ M`,
`∑_{t < n} a t / √(M + ∑_{s < t} a s) ≤ 2 √(∑_{t < n} a t)`.

The denominators only use the terms before `t`, as for adaptive rates computed from the past
rounds; the offset `M` makes each at least `√(∑_{s ≤ t} a s)`, which reduces it to
`Real.sum_div_sqrt_le_two_mul_sqrt`. -/
theorem sum_div_sqrt_add_le_two_mul_sqrt {M : ℝ} (ha : ∀ t < n, 0 ≤ a t)
    (hM : ∀ t < n, a t ≤ M) :
    ∑ t ∈ range n, a t / √(M + ∑ s ∈ range t, a s) ≤ 2 * √(∑ t ∈ range n, a t) := by
  refine (sum_le_sum fun t ht ↦ ?_).trans (sum_div_sqrt_le_two_mul_sqrt ha)
  have ht := mem_range.1 ht
  -- since `a t ≤ M`, the denominator is at least `√(∑_{s ≤ t} a s)`
  rcases (ha t ht).eq_or_lt with h0 | h0
  · simp [← h0]
  have hS : 0 ≤ ∑ s ∈ range t, a s := sum_nonneg fun s hs ↦ ha s ((mem_range.1 hs).trans ht)
  rw [sum_range_succ]
  exact div_le_div_of_nonneg_left h0.le (sqrt_pos.2 (by linarith))
    (sqrt_le_sqrt (by linarith [hM t ht]))

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

/-! ### Sums over a counter that lags behind the partial sums

Let `N s` be a natural number that lags behind the partial sums `∑_{r < s} a r` by at most
`c ≥ 0`, as the pull counts of a tracking rule lag behind the cumulated targets. The bounds below
control the sums of `a s / √(N s)` and `a s / N s`: the excess
`Y t = max (∑_{r < t} a r - c) 0` of the partial sums over the lag splits each `a s` into the
increment `Y (s + 1) - Y s`, which `N s` keeps up with, and a remainder, whose total is at most
`c` and whose terms are divided by `N s ≥ 1`. A term with `N s = 0` is `0`. -/

variable {N : ℕ → ℕ}

/-- The excess `max (∑_{r < t} a r - c) 0` of the partial sums of `a` over the lag `c`. -/
private noncomputable def lagExcess (a : ℕ → ℝ) (c : ℝ) (t : ℕ) : ℝ :=
  max (∑ r ∈ range t, a r - c) 0

private lemma lagExcess_nonneg (t : ℕ) : 0 ≤ lagExcess a c t := le_max_right _ _

private lemma lagExcess_le_lagExcess_add_one {t : ℕ} (ht : 0 ≤ a t) :
    lagExcess a c t ≤ lagExcess a c (t + 1) := by
  unfold lagExcess
  rw [sum_range_succ]
  exact max_le_max (by linarith) le_rfl

private lemma lagExcess_add_one_sub_le {t : ℕ} (ht : 0 ≤ a t) :
    lagExcess a c (t + 1) - lagExcess a c t ≤ a t := by
  unfold lagExcess
  rw [sum_range_succ, sub_le_iff_le_add]
  have := le_max_left (∑ r ∈ range t, a r - c) 0
  exact max_le (by linarith) (by linarith [le_max_right (∑ r ∈ range t, a r - c) 0])

/-- The excess is the sum of its increments. -/
private lemma sum_lagExcess_sub (hc : 0 ≤ c) (t : ℕ) :
    ∑ s ∈ range t, (lagExcess a c (s + 1) - lagExcess a c s) = lagExcess a c t := by
  rw [sum_range_sub]
  simp [lagExcess, hc]

/-- The remainders `a s - (Y (s + 1) - Y s)` sum to at most the lag. -/
private lemma sum_sub_lagExcess_le (hc : 0 ≤ c) (n : ℕ) :
    ∑ s ∈ range n, (a s - (lagExcess a c (s + 1) - lagExcess a c s)) ≤ c := by
  rw [sum_sub_distrib, sum_lagExcess_sub hc]
  have : ∑ s ∈ range n, a s - c ≤ lagExcess a c n := le_max_left _ _
  linarith

private lemma lagExcess_le_sum (hc : 0 ≤ c) (ha : ∀ t < n, 0 ≤ a t) :
    lagExcess a c n ≤ ∑ t ∈ range n, a t :=
  max_le (by linarith) (sum_nonneg fun t ht ↦ ha t (mem_range.1 ht))

/-- A counter with lag at most `c` is either `0` or at least `1` and the excess. -/
private lemma eq_zero_or_max_one_lagExcess_le {t : ℕ} {x : ℕ}
    (hx : ∑ r ∈ range t, a r - c ≤ x) : (x : ℝ) = 0 ∨ max 1 (lagExcess a c t) ≤ x := by
  rcases Nat.eq_zero_or_pos x with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr (max_le (Nat.one_le_cast.2 h) (max_le hx (Nat.cast_nonneg x)))

/-- Splitting a term: `(r + y) / √x ≤ r + y / √m` when `x = 0` or `1 ≤ m ≤ x`. -/
private lemma add_div_sqrt_le {r y m x : ℝ} (hr : 0 ≤ r) (hy : 0 ≤ y) (hm : 1 ≤ m)
    (hx : x = 0 ∨ m ≤ x) : (r + y) / √x ≤ r + y / √m := by
  rcases hx with rfl | hx
  · simp only [sqrt_zero, div_zero]
    positivity
  have h1 : 1 ≤ √m := one_le_sqrt.2 hm
  have h2 : √m ≤ √x := sqrt_le_sqrt hx
  rw [add_div]
  exact add_le_add (div_le_self hr (h1.trans h2)) (div_le_div_of_nonneg_left hy (by linarith) h2)

/-- Splitting a term: `(r + y) / x ≤ r + y / m` when `x = 0` or `1 ≤ m ≤ x`. -/
private lemma add_div_le {r y m x : ℝ} (hr : 0 ≤ r) (hy : 0 ≤ y) (hm : 1 ≤ m)
    (hx : x = 0 ∨ m ≤ x) : (r + y) / x ≤ r + y / m := by
  rcases hx with rfl | hx
  · simp only [div_zero]
    positivity
  rw [add_div]
  exact add_le_add (div_le_self hr (hm.trans hx)) (div_le_div_of_nonneg_left hy (by linarith) hx)

/-- **Sums over a lagging counter, square roots** [DKM19, Lemma 9]. Let `c ≥ 0`, `a s ≥ 0`, and
let `N s` be at least `∑_{r ≤ s} a r - c` for every `s < n`. Then
`∑_{s < n} a s / √(N s) ≤ c + 2 √(∑_{s < n} a s)`.

For the pull counts `N s = N_k(s + 1)` of an arm `k` after the round `s` of cumulative tracking,
which lag behind the cumulated targets `a s = w_k(s)` by `c = K - 1`, it is the per-arm form of
the first bound of [DKM19, Lemma 9], with the remainder `K - 1` in place of `K`. -/
theorem sum_div_sqrt_le_add_two_mul_sqrt (hc : 0 ≤ c) (ha : ∀ s < n, 0 ≤ a s)
    (hN : ∀ s < n, ∑ r ∈ range (s + 1), a r - c ≤ N s) :
    ∑ s ∈ range n, a s / √(N s) ≤ c + 2 * √(∑ s ∈ range n, a s) := by
  set y : ℕ → ℝ := fun s ↦ lagExcess a c (s + 1) - lagExcess a c s
  have hy0 : ∀ s < n, 0 ≤ y s := fun s hs ↦ sub_nonneg.2 (lagExcess_le_lagExcess_add_one (ha s hs))
  have hY (t : ℕ) : lagExcess a c t = ∑ s ∈ range t, y s := (sum_lagExcess_sub hc t).symm
  -- each term is a remainder plus the increment `y s` divided by `√(Y (s + 1))`
  have hterm : ∀ s ∈ range n, a s / √(N s) ≤
      (a s - y s) + y s / √(∑ r ∈ range (s + 1), y r) := by
    intro s hs
    have hs := mem_range.1 hs
    have hya : y s ≤ a s := lagExcess_add_one_sub_le (ha s hs)
    have hyY : y s ≤ lagExcess a c (s + 1) := by
      linarith [lagExcess_nonneg (a := a) (c := c) s]
    calc a s / √(N s) = ((a s - y s) + y s) / √(N s) := by ring_nf
      _ ≤ (a s - y s) + y s / √(max 1 (lagExcess a c (s + 1))) :=
        add_div_sqrt_le (by linarith) (hy0 s hs) (le_max_left _ _)
          (eq_zero_or_max_one_lagExcess_le (hN s hs))
      _ ≤ (a s - y s) + y s / √(∑ r ∈ range (s + 1), y r) := by
        rw [← hY]
        refine add_le_add le_rfl ?_
        rcases (lagExcess_nonneg (a := a) (c := c) (s + 1)).eq_or_lt with h0 | h0
        · rw [← h0] at hyY
          simp [le_antisymm hyY (hy0 s hs)]
        · exact div_le_div_of_nonneg_left (hy0 s hs) (sqrt_pos.2 h0)
            (sqrt_le_sqrt (le_max_right _ _))
  calc ∑ s ∈ range n, a s / √(N s)
      ≤ ∑ s ∈ range n, ((a s - y s) + y s / √(∑ r ∈ range (s + 1), y r)) := sum_le_sum hterm
    _ ≤ c + 2 * √(∑ s ∈ range n, y s) := by
      rw [sum_add_distrib]
      exact add_le_add (sum_sub_lagExcess_le hc n) (sum_div_sqrt_le_two_mul_sqrt hy0)
    _ ≤ c + 2 * √(∑ s ∈ range n, a s) := by
      rw [← hY]
      gcongr
      exact lagExcess_le_sum hc ha

/-- **Sums over a lagging counter, square roots of the past** [DKM19, Lemma 9]. Let `c ≥ 0` and
`0 ≤ a s ≤ 1`, and let `N s` be at least `∑_{r < s} a r - c` for every `s < n`. Then
`∑_{s < n} a s / √(N s) ≤ c + (√2 + 1) √(∑_{s < n} a s)`.

For the pull counts `N s = N_k(s)` of an arm `k` before the round `s` of cumulative tracking, which
lag behind the cumulated targets `a s = w_k(s)` by `c = K - 1`, it is the per-arm form of the
second bound of [DKM19, Lemma 9], with the remainder `K - 1` in place of `K` and the constant
`√2 + 1` of the doubling bound `Real.sum_div_sqrt_max_one_le` in place of `2 √2`. -/
theorem sum_div_sqrt_le_add_mul_sqrt (hc : 0 ≤ c) (ha : ∀ s < n, 0 ≤ a s)
    (ha1 : ∀ s < n, a s ≤ 1) (hN : ∀ s < n, ∑ r ∈ range s, a r - c ≤ N s) :
    ∑ s ∈ range n, a s / √(N s) ≤ c + (√2 + 1) * √(∑ s ∈ range n, a s) := by
  set y : ℕ → ℝ := fun s ↦ lagExcess a c (s + 1) - lagExcess a c s
  have hy0 : ∀ s < n, 0 ≤ y s := fun s hs ↦ sub_nonneg.2 (lagExcess_le_lagExcess_add_one (ha s hs))
  have hya : ∀ s < n, y s ≤ a s := fun s hs ↦ lagExcess_add_one_sub_le (ha s hs)
  have hY (t : ℕ) : lagExcess a c t = ∑ s ∈ range t, y s := (sum_lagExcess_sub hc t).symm
  -- each term is a remainder plus the increment `y s` divided by `√(max 1 (Y s))`
  have hterm : ∀ s ∈ range n, a s / √(N s) ≤
      (a s - y s) + y s / √(max 1 (∑ r ∈ range s, y r)) := by
    intro s hs
    have hs := mem_range.1 hs
    rw [← hY]
    calc a s / √(N s) = ((a s - y s) + y s) / √(N s) := by ring_nf
      _ ≤ _ := add_div_sqrt_le (by linarith [hya s hs]) (hy0 s hs) (le_max_left _ _)
          (eq_zero_or_max_one_lagExcess_le (hN s hs))
  calc ∑ s ∈ range n, a s / √(N s)
      ≤ ∑ s ∈ range n, ((a s - y s) + y s / √(max 1 (∑ r ∈ range s, y r))) := sum_le_sum hterm
    _ ≤ c + (√2 + 1) * √(∑ s ∈ range n, y s) := by
      rw [sum_add_distrib]
      exact add_le_add (sum_sub_lagExcess_le hc n) (sum_div_sqrt_max_one_le hy0
        fun s hs ↦ ((hya s hs).trans (ha1 s hs)).trans (le_max_left _ _))
    _ ≤ c + (√2 + 1) * √(∑ s ∈ range n, a s) := by
      rw [← hY]
      gcongr
      exact lagExcess_le_sum hc ha

/-- **Sums over a lagging counter, inverses** [DKM19, Lemma 9]. Let `c ≥ 0` and `0 ≤ a s ≤ 1`, and
let `N s` be at least `∑_{r < s} a r - c` for every `s < n`. Then
`∑_{s < n} a s / N s ≤ c + 3 log (∑_{s < n} a s + 1)`.

For the pull counts `N s = N_k(s)` of an arm `k` before the round `s` of cumulative tracking, it is
the per-arm form of the logarithmic bound used in the proof of [DKM19, Lemma 16], with the
constant `3` of `Real.sum_div_max_one_le_three_mul_log`. -/
theorem sum_div_le_add_three_mul_log (hc : 0 ≤ c) (ha : ∀ s < n, 0 ≤ a s)
    (ha1 : ∀ s < n, a s ≤ 1) (hN : ∀ s < n, ∑ r ∈ range s, a r - c ≤ N s) :
    ∑ s ∈ range n, a s / N s ≤ c + 3 * log (∑ s ∈ range n, a s + 1) := by
  set y : ℕ → ℝ := fun s ↦ lagExcess a c (s + 1) - lagExcess a c s
  have hy0 : ∀ s < n, 0 ≤ y s := fun s hs ↦ sub_nonneg.2 (lagExcess_le_lagExcess_add_one (ha s hs))
  have hya : ∀ s < n, y s ≤ a s := fun s hs ↦ lagExcess_add_one_sub_le (ha s hs)
  have hY (t : ℕ) : lagExcess a c t = ∑ s ∈ range t, y s := (sum_lagExcess_sub hc t).symm
  -- each term is a remainder plus the increment `y s` divided by `max 1 (Y s)`
  have hterm : ∀ s ∈ range n, a s / N s ≤ (a s - y s) + y s / max 1 (∑ r ∈ range s, y r) := by
    intro s hs
    have hs := mem_range.1 hs
    rw [← hY]
    calc a s / N s = ((a s - y s) + y s) / N s := by ring_nf
      _ ≤ _ := add_div_le (by linarith [hya s hs]) (hy0 s hs) (le_max_left _ _)
          (eq_zero_or_max_one_lagExcess_le (hN s hs))
  calc ∑ s ∈ range n, a s / N s
      ≤ ∑ s ∈ range n, ((a s - y s) + y s / max 1 (∑ r ∈ range s, y r)) := sum_le_sum hterm
    _ ≤ c + 3 * log (∑ s ∈ range n, y s + 1) := by
      rw [sum_add_distrib]
      exact add_le_add (sum_sub_lagExcess_le hc n) (sum_div_max_one_le_three_mul_log hy0
        fun s hs ↦ ((hya s hs).trans (ha1 s hs)).trans (le_max_left _ _))
    _ ≤ c + 3 * log (∑ s ∈ range n, a s + 1) := by
      rw [← hY]
      gcongr
      · linarith [lagExcess_nonneg (a := a) (c := c) n]
      · exact lagExcess_le_sum hc ha

end Real
