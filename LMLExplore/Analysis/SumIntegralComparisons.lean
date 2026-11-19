/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import LMLExplore.Analysis.Real.Sqrt
import LMLExplore.Analysis.SpecialFunctions.Log.Basic

/-!
# Weighted sums of an antitone function, sums over a lagging counter, and sums of powers

Mathlib's `AntitoneOn.sum_le_integral` compares the values of an antitone function at the
integers with its integral. Its weighted form compares the values at the partial sums of a
nonnegative sequence: for `f` antitone on `(c, c + ∑_{t < n} a t]` and integrable on
`[c, c + ∑_{t < n} a t]`, and `a t ≥ 0`,
`∑_{t < n} a t f (c + ∑_{s ≤ t} a s) ≤ ∫_c^{c + ∑_{t < n} a t} f`.
For an antitone `C : ℝ≥0∞ → ℝ≥0∞`, with possibly infinite values, the Lebesgue integral of `C`
over `(1 / K, 1]` is likewise at most its upper Riemann sum on the grid of mesh `1 / K`.

Adaptive learning rates of online learning are of the form `η_t ∝ f (∑_{s ≤ t} a s)`, where
`a s` is the squared norm of the subgradient of round `s` (as in AdaGrad), and the regret bounds
sum the terms `a t f (∑_{s ≤ t} a s)`. The instances `f x = 1 / √x` and `f x = 1 / x` below,
and an offset form of the first for rates that only use the past rounds, are the ones these
bounds use.

The same sums appear when a natural number `N s` lags behind the partial sums `∑_{r < s} a r` by
at most a constant `c`, as the pull counts of a tracking rule lag behind the cumulated targets.
Three further bounds control `∑_{s < n} a s / √(N s)` and `∑_{s < n} a s / N s` in that case:
they bound the sums of the confidence widths of a bandit algorithm that tracks a sequence of
allocations, the square-root sums [DKM19, Lemma 9] and the logarithmic sum used in the proof of
[DKM19, Lemma 16].

The file also compares the sums `∑_{m ≤ i < n} (i + 1) ^ r` with the integral of `x ^ r` over
`[m, n]`, using Mathlib's unweighted comparisons. They bound the sums of the learning rates
`(t + 1) ^ (-α)` of online subgradient descent, as in its lower bound [Ora, Theorem 5.4].

## Main statements

* `AntitoneOn.sum_mul_le_integral_of_integrableOn`: the weighted comparison [Ora, Lemma 4.13].
* `Antitone.setLIntegral_Ioc_le_sum`: for `C : ℝ≥0∞ → ℝ≥0∞` antitone, the integral of `C` over
  `(1 / K, 1]` is at most its upper Riemann sum on the grid of mesh `1 / K`.
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
* `Real.sum_Ico_add_one_rpow_le`, `Real.sub_div_le_sum_Ico_add_one_rpow`: the sums
  `∑_{m ≤ i < n} (i + 1) ^ r` compared with `(n ^ (r + 1) - m ^ (r + 1)) / (r + 1)`, the integral
  of `x ^ r` over `[m, n]`, from above for `-1 < r ≤ 0` and from below for `r ≥ 0`. The learning
  rates `(t + 1) ^ (-α)` of online subgradient descent are of this form.
* `Real.sum_range_add_one_rpow_le`, `Real.div_le_sum_range_add_one_rpow`: their cases `m = 0`,
  comparing `∑_{i < n} (i + 1) ^ r` with `n ^ (r + 1) / (r + 1)`.

In `Real.sum_div_sqrt_le_two_mul_sqrt`, a term whose denominator vanishes has `a t = 0`, and
Lean's convention `x / 0 = 0` omits it, as [Ora] does. In the bounds over a lagging counter,
the terms with `N s = 0` are `0` for the same reason.

## References

* [Ora] F. Orabona, *A Modern Introduction to Online Learning*, arXiv:1912.13213v10, Lemma 4.13
  and Theorem 5.4.
* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Lemmas 9 and 16 (in the numbering of arXiv:1906.10431).
-/

public section

open Finset MeasureTheory Set intervalIntegral
open scoped ENNReal

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

/-- **An upper Riemann sum of an antitone function of `ℝ≥0∞`.** For `C : ℝ≥0∞ → ℝ≥0∞`
antitone and `K > 0`, the integral of `C` over `(1 / K, 1]` is at most the upper Riemann sum
`∑_{j < K} C ((K - j) / K) / K` on the grid of mesh `1 / K`. The values of `C` may be infinite. -/
theorem Antitone.setLIntegral_Ioc_le_sum {C : ℝ≥0∞ → ℝ≥0∞} (hC : Antitone C) {K : ℕ}
    (hK : 0 < K) :
    ∫⁻ u in Ioc (K : ℝ)⁻¹ 1, C (ENNReal.ofReal u) ≤
      ∑ j : Fin K, (K : ℝ≥0∞)⁻¹ * C (((K - j : ℕ) : ℝ≥0∞) / K) := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  set I : Fin K → Set ℝ := fun j ↦ Ico (((K - j : ℕ) : ℝ) / K) ((((K - j : ℕ) : ℝ) + 1) / K)
  -- on `(1 / K, 1]`, `C` is below the step function of its values at the left endpoints
  have h_le : ∀ u ∈ Ioc (K : ℝ)⁻¹ 1, C (ENNReal.ofReal u) ≤
      ∑ j : Fin K, (I j).indicator (fun _ ↦ C (((K - j : ℕ) : ℝ≥0∞) / K)) u := by
    rintro u ⟨hu0, hu1⟩
    have huK : 1 < u * K := by
      have := mul_lt_mul_of_pos_right hu0 hK'
      rwa [inv_mul_cancel₀ hK'.ne'] at this
    have h1 : 1 ≤ ⌊u * K⌋₊ := Nat.one_le_floor_iff _ |>.2 huK.le
    have h2 : ⌊u * K⌋₊ ≤ K := Nat.floor_le_of_le (by nlinarith)
    have hfl := Nat.floor_le (zero_le_one.trans huK.le)
    have hfl' := Nat.lt_floor_add_one (u * K)
    let j : Fin K := ⟨K - ⌊u * K⌋₊, by omega⟩
    have hj : K - (j : ℕ) = ⌊u * K⌋₊ := by simp only [j]; omega
    refine le_trans ?_ (Finset.single_le_sum (f := fun j : Fin K ↦
      (I j).indicator (fun _ ↦ C (((K - j : ℕ) : ℝ≥0∞) / K)) u) (fun _ _ ↦ zero_le)
      (Finset.mem_univ j))
    have hu_mem : u ∈ I j := by
      simp only [I, hj, Set.mem_Ico]
      exact ⟨(div_le_iff₀ hK').2 hfl, (lt_div_iff₀ hK').2 hfl'⟩
    simp only [indicator_of_mem hu_mem, hj]
    refine hC ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast K,
      ← ENNReal.ofReal_div_of_pos hK']
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hK').2 hfl)
  calc ∫⁻ u in Ioc (K : ℝ)⁻¹ 1, C (ENNReal.ofReal u)
      ≤ ∫⁻ u in Ioc (K : ℝ)⁻¹ 1, ∑ j : Fin K,
          (I j).indicator (fun _ ↦ C (((K - j : ℕ) : ℝ≥0∞) / K)) u :=
        setLIntegral_mono' measurableSet_Ioc h_le
    _ ≤ ∫⁻ u, ∑ j : Fin K, (I j).indicator (fun _ ↦ C (((K - j : ℕ) : ℝ≥0∞) / K)) u :=
        setLIntegral_le_lintegral _ _
    _ = ∑ j : Fin K, (K : ℝ≥0∞)⁻¹ * C (((K - j : ℕ) : ℝ≥0∞) / K) := by
        rw [lintegral_finsetSum _ fun j _ ↦ measurable_const.indicator measurableSet_Ico]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, mul_comm,
          show (((K - j : ℕ) : ℝ) + 1) / K - ((K - j : ℕ) : ℝ) / K = (K : ℝ)⁻¹ by
            field_simp; ring,
          ENNReal.ofReal_inv_of_pos hK', ENNReal.ofReal_natCast]

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
`c` and whose terms are divided by `N s ≥ 1` (`sum_div_le_add_sum_lagIncrement_div`). A term with
`N s = 0` is `0`. Each bound then applies a doubling bound to the increments. -/

variable {N : ℕ → ℕ}

/-- The excess `max (∑_{r < t} a r - c) 0` of the partial sums of `a` over the lag `c`. -/
private noncomputable def lagExcess (a : ℕ → ℝ) (c : ℝ) (t : ℕ) : ℝ :=
  max (∑ r ∈ range t, a r - c) 0

/-- The increment `Y (s + 1) - Y s` of the excess `Y = lagExcess a c`: the part of `a s` that a
counter with lag at most `c` keeps up with. -/
private noncomputable def lagIncrement (a : ℕ → ℝ) (c : ℝ) (s : ℕ) : ℝ :=
  lagExcess a c (s + 1) - lagExcess a c s

private lemma lagIncrement_nonneg {s : ℕ} (hs : 0 ≤ a s) : 0 ≤ lagIncrement a c s := by
  unfold lagIncrement lagExcess
  rw [sum_range_succ, sub_nonneg]
  exact max_le_max (by linarith) le_rfl

private lemma lagIncrement_le {s : ℕ} (hs : 0 ≤ a s) : lagIncrement a c s ≤ a s := by
  unfold lagIncrement lagExcess
  rw [sum_range_succ, sub_le_iff_le_add]
  have h := le_max_left (∑ r ∈ range s, a r - c) 0
  exact max_le (by linarith) (by linarith [le_max_right (∑ r ∈ range s, a r - c) 0])

/-- The excess is the sum of its increments. -/
private lemma sum_lagIncrement (hc : 0 ≤ c) (t : ℕ) :
    ∑ s ∈ range t, lagIncrement a c s = lagExcess a c t := by
  unfold lagIncrement
  rw [sum_range_sub]
  simp [lagExcess, hc]

/-- A counter with lag at most `c` is either `0` or at least `1` and the excess. -/
private lemma eq_zero_or_max_one_sum_lagIncrement_le (hc : 0 ≤ c) {t x : ℕ}
    (hx : ∑ r ∈ range t, a r - c ≤ x) :
    (x : ℝ) = 0 ∨ max 1 (∑ r ∈ range t, lagIncrement a c r) ≤ x := by
  rw [sum_lagIncrement hc]
  rcases Nat.eq_zero_or_pos x with h | h
  · exact Or.inl (by simp [h])
  · exact Or.inr (max_le (Nat.one_le_cast.2 h) (max_le hx (Nat.cast_nonneg x)))

/-- **The lag split.** If every denominator `x s` is `0` or at least `m s ≥ 1`, then
`∑_{s < n} a s / x s ≤ c + ∑_{s < n} y s / m s` for the increments `y = lagIncrement a c`: the
remainders `a s - y s` sum to at most `c`, and dividing them by `x s` does not increase them. -/
private lemma sum_div_le_add_sum_lagIncrement_div {x m : ℕ → ℝ} (hc : 0 ≤ c)
    (ha : ∀ s < n, 0 ≤ a s) (hm : ∀ s < n, 1 ≤ m s) (hx : ∀ s < n, x s = 0 ∨ m s ≤ x s) :
    ∑ s ∈ range n, a s / x s ≤ c + ∑ s ∈ range n, lagIncrement a c s / m s := by
  have hterm : ∀ s ∈ range n,
      a s / x s ≤ (a s - lagIncrement a c s) + lagIncrement a c s / m s := by
    intro s hs
    have hs := mem_range.1 hs
    have hy := lagIncrement_nonneg (c := c) (ha s hs)
    have hr : 0 ≤ a s - lagIncrement a c s := sub_nonneg.2 (lagIncrement_le (ha s hs))
    rcases hx s hs with h | hmx
    · rw [h, div_zero]
      exact add_nonneg hr (div_nonneg hy (by linarith [hm s hs]))
    · rw [← sub_add_cancel (a s) (lagIncrement a c s), add_div, add_sub_cancel_right]
      exact add_le_add (div_le_self hr ((hm s hs).trans hmx))
        (div_le_div_of_nonneg_left hy (by linarith [hm s hs]) hmx)
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_sub_distrib, sum_lagIncrement hc]
  have : ∑ s ∈ range n, a s - c ≤ lagExcess a c n := le_max_left _ _
  linarith

/-- **Sums over a lagging counter, square roots** [DKM19, Lemma 9]. Let `c ≥ 0`, `a s ≥ 0`, and
let `N s` be at least `∑_{r ≤ s} a r - c` for every `s < n`. Then
`∑_{s < n} a s / √(N s) ≤ c + 2 √(∑_{s < n} a s)`.

For the pull counts `N s = N_k(s + 1)` of an arm `k` after the round `s` of cumulative tracking,
which lag behind the cumulated targets `a s = w_k(s)` by `c = K - 1`, it is the per-arm form of
the first bound of [DKM19, Lemma 9], with the remainder `K - 1` in place of `K`. -/
theorem sum_div_sqrt_le_add_two_mul_sqrt (hc : 0 ≤ c) (ha : ∀ s < n, 0 ≤ a s)
    (hN : ∀ s < n, ∑ r ∈ range (s + 1), a r - c ≤ N s) :
    ∑ s ∈ range n, a s / √(N s) ≤ c + 2 * √(∑ s ∈ range n, a s) := by
  have hy0 : ∀ s < n, 0 ≤ lagIncrement a c s := fun s hs ↦ lagIncrement_nonneg (ha s hs)
  calc ∑ s ∈ range n, a s / √(N s)
      ≤ c + ∑ s ∈ range n,
          lagIncrement a c s / √(max 1 (∑ r ∈ range (s + 1), lagIncrement a c r)) := by
        refine sum_div_le_add_sum_lagIncrement_div hc ha (fun _ _ ↦ one_le_sqrt.2 (le_max_left _ _))
          fun s hs ↦ (eq_zero_or_max_one_sum_lagIncrement_le hc (hN s hs)).imp (by simp [·])
            sqrt_le_sqrt
    -- the increment `y s` is at most `Y (s + 1)`, so that the clipping at `1` can be dropped
    _ ≤ c + ∑ s ∈ range n, lagIncrement a c s / √(∑ r ∈ range (s + 1), lagIncrement a c r) := by
        refine add_le_add le_rfl (sum_le_sum fun s hs ↦ ?_)
        have hs := mem_range.1 hs
        have hY : 0 ≤ ∑ r ∈ range s, lagIncrement a c r :=
          sum_nonneg fun r hr ↦ hy0 r ((mem_range.1 hr).trans hs)
        rw [sum_range_succ]
        rcases (add_nonneg hY (hy0 s hs)).eq_or_lt with h0 | h0
        · simp [show lagIncrement a c s = 0 by linarith [hy0 s hs]]
        · exact div_le_div_of_nonneg_left (hy0 s hs) (sqrt_pos.2 h0)
            (sqrt_le_sqrt (le_max_right _ _))
    _ ≤ c + 2 * √(∑ s ∈ range n, lagIncrement a c s) := by
        gcongr
        exact sum_div_sqrt_le_two_mul_sqrt hy0
    _ ≤ c + 2 * √(∑ s ∈ range n, a s) := by
        gcongr with s hs
        exact lagIncrement_le (ha s (mem_range.1 hs))

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
  have hy0 : ∀ s < n, 0 ≤ lagIncrement a c s := fun s hs ↦ lagIncrement_nonneg (ha s hs)
  calc ∑ s ∈ range n, a s / √(N s)
      ≤ c + ∑ s ∈ range n,
          lagIncrement a c s / √(max 1 (∑ r ∈ range s, lagIncrement a c r)) := by
        refine sum_div_le_add_sum_lagIncrement_div hc ha (fun _ _ ↦ one_le_sqrt.2 (le_max_left _ _))
          fun s hs ↦ (eq_zero_or_max_one_sum_lagIncrement_le hc (hN s hs)).imp (by simp [·])
            sqrt_le_sqrt
    _ ≤ c + (√2 + 1) * √(∑ s ∈ range n, lagIncrement a c s) := by
        gcongr
        exact sum_div_sqrt_max_one_le hy0
          fun s hs ↦ ((lagIncrement_le (ha s hs)).trans (ha1 s hs)).trans (le_max_left _ _)
    _ ≤ c + (√2 + 1) * √(∑ s ∈ range n, a s) := by
        gcongr with s hs
        exact lagIncrement_le (ha s (mem_range.1 hs))

/-- **Sums over a lagging counter, inverses** [DKM19, Lemma 16]. Let `c ≥ 0` and `0 ≤ a s ≤ 1`,
and let `N s` be at least `∑_{r < s} a r - c` for every `s < n`. Then
`∑_{s < n} a s / N s ≤ c + 3 log (∑_{s < n} a s + 1)`.

For the pull counts `N s = N_k(s)` of an arm `k` before the round `s` of cumulative tracking, it is
the per-arm form of the logarithmic bound used in the proof of [DKM19, Lemma 16], with the
constant `3` of `Real.sum_div_max_one_le_three_mul_log`. -/
theorem sum_div_le_add_three_mul_log (hc : 0 ≤ c) (ha : ∀ s < n, 0 ≤ a s)
    (ha1 : ∀ s < n, a s ≤ 1) (hN : ∀ s < n, ∑ r ∈ range s, a r - c ≤ N s) :
    ∑ s ∈ range n, a s / N s ≤ c + 3 * log (∑ s ∈ range n, a s + 1) := by
  have hy0 : ∀ s < n, 0 ≤ lagIncrement a c s := fun s hs ↦ lagIncrement_nonneg (ha s hs)
  calc ∑ s ∈ range n, a s / N s
      ≤ c + ∑ s ∈ range n, lagIncrement a c s / max 1 (∑ r ∈ range s, lagIncrement a c r) :=
        sum_div_le_add_sum_lagIncrement_div hc ha (fun _ _ ↦ le_max_left _ _)
          fun s hs ↦ eq_zero_or_max_one_sum_lagIncrement_le hc (hN s hs)
    _ ≤ c + 3 * log (∑ s ∈ range n, lagIncrement a c s + 1) := by
        gcongr
        exact sum_div_max_one_le_three_mul_log hy0
          fun s hs ↦ ((lagIncrement_le (ha s hs)).trans (ha1 s hs)).trans (le_max_left _ _)
    _ ≤ c + 3 * log (∑ s ∈ range n, a s + 1) := by
        gcongr with s hs
        · linarith [sum_nonneg fun s (hs : s ∈ range n) ↦ hy0 s (mem_range.1 hs)]
        · exact lagIncrement_le (ha s (mem_range.1 hs))

/-! ### Sums of powers -/

/-- **Sums of a nonpositive power** compared with its integral: for `-1 < r ≤ 0` and `m ≤ n`,
`∑_{m ≤ i < n} (i + 1) ^ r ≤ (n ^ (r + 1) - m ^ (r + 1)) / (r + 1)`.

For `m = 0`, it is `Real.sum_range_add_one_rpow_le`. -/
theorem sum_Ico_add_one_rpow_le {r : ℝ} (hr₁ : -1 < r) (hr : r ≤ 0) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, ((i : ℝ) + 1) ^ r ≤
      ((n : ℝ) ^ (r + 1) - (m : ℝ) ^ (r + 1)) / (r + 1) := by
  have hcast : (m : ℝ) + ((n - m : ℕ) : ℝ) = n := by rw [Nat.cast_sub hmn]; ring
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ r) (Ioc (m : ℝ) (m + ((n - m : ℕ) : ℝ))) :=
    (antitoneOn_rpow_Ioi_of_exponent_nonpos hr).mono fun x hx ↦
      (Nat.cast_nonneg m).trans_lt hx.1
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ r) (Icc (m : ℝ) (m + ((n - m : ℕ) : ℝ))) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by simp)).1
      (intervalIntegral.intervalIntegrable_rpow' hr₁)
  have h := hanti.sum_le_integral_of_integrableOn hint
  rw [hcast, integral_rpow (Or.inl hr₁)] at h
  refine le_of_eq_of_le ?_ h
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  push_cast
  ring

/-- **Sums of a nonnegative power** compared with its integral: for `0 ≤ r` and `m ≤ n`,
`(n ^ (r + 1) - m ^ (r + 1)) / (r + 1) ≤ ∑_{m ≤ i < n} (i + 1) ^ r`.

For `m = 0`, it is `Real.div_le_sum_range_add_one_rpow`. -/
theorem sub_div_le_sum_Ico_add_one_rpow {r : ℝ} (hr : 0 ≤ r) {m n : ℕ} (hmn : m ≤ n) :
    ((n : ℝ) ^ (r + 1) - (m : ℝ) ^ (r + 1)) / (r + 1) ≤
      ∑ i ∈ Finset.Ico m n, ((i : ℝ) + 1) ^ r := by
  have hmono : MonotoneOn (fun x : ℝ ↦ x ^ r) (Icc (m : ℝ) n) :=
    (monotoneOn_rpow_Ici_of_exponent_nonneg hr).mono fun x hx ↦ (Nat.cast_nonneg m).trans hx.1
  have h := hmono.integral_le_sum_Ico hmn
  rw [integral_rpow (Or.inl (by linarith))] at h
  exact h.trans_eq (Finset.sum_congr rfl fun i _ ↦ by rw [Nat.cast_add_one])

/-- **Sums of a nonpositive power** from `0` compared with its integral: for `-1 < r ≤ 0`,
`∑_{i < n} (i + 1) ^ r ≤ n ^ (r + 1) / (r + 1)`, the case `m = 0` of
`Real.sum_Ico_add_one_rpow_le`. The learning rates `(t + 1) ^ (-α)`, `0 ≤ α < 1`, of online
subgradient descent sum to at most `n ^ (1 - α) / (1 - α)` over the first `n` rounds. -/
theorem sum_range_add_one_rpow_le {r : ℝ} (hr₁ : -1 < r) (hr : r ≤ 0) :
    ∑ i ∈ range n, ((i : ℝ) + 1) ^ r ≤ (n : ℝ) ^ (r + 1) / (r + 1) := by
  have h := sum_Ico_add_one_rpow_le hr₁ hr (Nat.zero_le n)
  rwa [Nat.cast_zero, zero_rpow (by linarith), sub_zero, ← range_eq_Ico] at h

/-- **Sums of a nonnegative power** from `0` compared with its integral: for `0 ≤ r`,
`n ^ (r + 1) / (r + 1) ≤ ∑_{i < n} (i + 1) ^ r`, the case `m = 0` of
`Real.sub_div_le_sum_Ico_add_one_rpow`. -/
theorem div_le_sum_range_add_one_rpow {r : ℝ} (hr : 0 ≤ r) :
    (n : ℝ) ^ (r + 1) / (r + 1) ≤ ∑ i ∈ range n, ((i : ℝ) + 1) ^ r := by
  have h := sub_div_le_sum_Ico_add_one_rpow hr (Nat.zero_le n)
  rwa [Nat.cast_zero, zero_rpow (by linarith), sub_zero, ← range_eq_Ico] at h

end Real
