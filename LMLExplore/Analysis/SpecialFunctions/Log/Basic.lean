/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Elementary bounds on the real logarithm

## Main statements

* `Real.min_one_le_two_mul_log_one_add`: `min 1 u ≤ 2 log (1 + u)` for `u ≥ 0`.
* `Real.monotoneOn_log_one_add_mul_log_sq`: `x ↦ log (1 + x log² x)` is monotone on `[1, ∞)`.
* `Real.log_natCast_le_log_natCast`: `log` is monotone on natural numbers.
* `Real.one_le_log_natCast_of_three_le`: `1 ≤ log n` for a natural number `n ≥ 3`.
* `Real.one_le_log_mul`: `1 ≤ log (x y)` for `x ≥ e` and `y ≥ 1`.
* `Real.log_div_rpow_le_exp_neg_one`: `log x / x ^ p ≤ 1 / e` for `x ≥ 1` and `p ≥ 1`.
* `Real.log_le_rpow_div_exp_one_mul`: `log y ≤ y ^ γ / (e γ)` for `y ≥ 0` and `γ > 0`, Mathlib's
  `Real.log_le_rpow_div` sharpened by the factor `e`.
* `Real.log_le_of_le_mul_sq_log`: if `1 ≤ y ≤ M log² y`, then
  `log y ≤ (8 / 5) log (4 M)`. It bounds the logarithm in the self-bounding inequality
  `Real.le_of_le_sqrt_mul_add`.
* `Real.monotone_log_two_mul_mul_add_one`: `n ↦ log (2 n (n + 1))` is monotone on `ℕ`.
* `Real.tendsto_log_one_add_mul_log_sq_div_log_atTop`: `log (1 + x log² x) / log x → 1` as
  `x → ∞`.
* `Real.eventually_lt_mul_log_of_tendsto_div_log`: if `g n / log n → D` and `D < c`, then
  eventually `g n < c log n`.
* `Real.tendsto_div_add_div_log`: if `L n / log n → 1`, then `(L n / D + K) / log n → 1 / D`.
* `Real.tendsto_add_mul_add_sqrt_add_one_div_log`: if `L n / log n → 1`, then
  `(K + D (L n + √(b L n) + 1)) / log n → D`.
* `Real.eventually_le_mul_log_of_forall_le_add_mul_add_sqrt_add_one`: if for every `ε ∈ (0, Δ)`,
  `x n ≤ K_ε + C / (Δ - ε)² (L n + √(b L n) + 1)` and `L n / log n → 1`, then eventually
  `x n ≤ c log n` for every `c > C / Δ²`.
* `Real.tendsto_natCeil_sub_div_log`: if `f n / log n → ∞`, then `⌈f n - c⌉₊ / log n → ∞`.
* `Real.mul_log_add_lt`: `a log x + b < x` as soon as `x ≥ 2 a log (2 a) + 2 b`, for `a, x > 0`.
* `Real.log_one_add_div`: `log (1 + y / x) = log (x + y) - log x` for `x ≠ 0` and `x + y ≠ 0`.
* `Real.one_le_add_half_mul_log_one_add_inv`: `1 ≤ (x + 1 / 2) log (1 + 1 / x)` for `x > 0`.
* `Real.one_add_mul_log_one_add_sub_sub_mul_log_nonpos`:
  `(1 + t) log (1 + t) - t - t log (1 + t / 2) ≤ 0` for `t ≥ 0`.
* `Real.add_one_mul_log_sub_le_one`: `(m + 1) log (m + 1) - m log m - log (m + 1 / 2) ≤ 1` for
  `m : ℕ`.
* `Real.log_div_le_log_one_div_add_log`: `log (x / δ) ≤ log (1 / δ) + log x` for `δ ∈ (0, 1]`.
* `Real.eventually_log_le_mul_of_isBigO`: if `r n = O(n ^ p)`, then `log (r n) ≤ ε n` for all
  large `n`, for every `ε > 0`.
* `Real.eventually_exists_add_le_mul_and_forall_ofReal_add_lt_mul`: for `1 < κ c` and
  `f T = o(T)` from above, for all small enough `δ` the thresholds `log (1 / δ) + f T` are below
  `κ T` from a round `N ≤ c log (1 / δ)` on.

## References

* [GK16] A. Garivier and E. Kaufmann, *Optimal best arm identification with fixed confidence*,
  COLT 2016, proof of Theorem 14.
* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Filter Topology

open scoped NNReal ENNReal

namespace Real

/-- For `u ≥ 0`, `min 1 u ≤ 2 log (1 + u)`. -/
theorem min_one_le_two_mul_log_one_add {u : ℝ} (hu : 0 ≤ u) : min 1 u ≤ 2 * log (1 + u) := by
  have hpos : 0 < u + 2 := by linarith
  have h : min 1 u ≤ 2 * (2 * u / (u + 2)) := by
    rw [show 2 * (2 * u / (u + 2)) = 4 * u / (u + 2) by ring, le_div_iff₀ hpos]
    rcases le_total u 2 with hu2 | hu2
    · nlinarith [mul_le_mul_of_nonneg_right (min_le_right 1 u) hpos.le,
        mul_nonneg hu (sub_nonneg.2 hu2)]
    · nlinarith [mul_le_mul_of_nonneg_right (min_le_left 1 u) hpos.le]
  linarith [le_log_one_add_of_nonneg hu]

/-- The function `x ↦ log (1 + x log² x)` is monotone on `[1, ∞)`. It is the logarithm of the
exploration function `f(x) = 1 + x log² x` of the asymptotically optimal UCB and KL-UCB
algorithms. -/
theorem monotoneOn_log_one_add_mul_log_sq :
    MonotoneOn (fun x ↦ log (1 + x * log x ^ 2)) (Set.Ici 1) := by
  intro x hx y hy hxy
  rw [Set.mem_Ici] at hx hy
  have hx0 : 0 ≤ log x := log_nonneg hx
  have hlog : log x ≤ log y := log_le_log (by linarith) hxy
  have hy0 : 0 ≤ y := by linarith
  dsimp only
  gcongr

/-- The logarithm is monotone on natural numbers, including `0` where `log 0 = 0 = log 1`. -/
theorem log_natCast_le_log_natCast {m n : ℕ} (h : m ≤ n) : log m ≤ log n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using log_natCast_nonneg n
  · exact log_le_log (by positivity) (by exact_mod_cast h)

/-- The logarithm of a natural number `n ≥ 3` is at least `1`, since `exp 1 < 3`. -/
theorem one_le_log_natCast_of_three_le {n : ℕ} (hn : 3 ≤ n) : 1 ≤ log n := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [le_log_iff_exp_le (by positivity)]
  linarith [exp_one_lt_three]

/-- `1 ≤ log (x y)` for `x ≥ e` and `y ≥ 1`.

Adapted from the formalization in the paper project RemyDegenne/Essakine2026Tight (same author),
file `ForLMLExplore/Analysis/SpecialFunctions/Log/SelfBounding.lean`. -/
theorem one_le_log_mul {x y : ℝ} (hx : exp 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ log (x * y) := by
  have hx0 : 0 < x := (exp_pos 1).trans_le hx
  exact (le_log_iff_exp_le (mul_pos hx0 (by linarith))).2
    (hx.trans (le_mul_of_one_le_right hx0.le hy))

/-- The function `n ↦ log (2 n (n + 1))` on `ℕ` is monotone. It is the boundary of the
sub-Gaussian, two-tailed form of the time-uniform deviation bound of [LS, Lemma 33.8]: Lattimore
and Szepesvári state that lemma for unit-variance Gaussians with the boundary `log (n (n + 1))`,
and the factor `2` accounts for the two tails. -/
theorem monotone_log_two_mul_mul_add_one : Monotone fun n : ℕ ↦ log (2 * n * (n + 1)) := by
  intro n m hnm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using log_natCast_nonneg (2 * m * (m + 1))
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
    exact log_le_log (by positivity) (by gcongr)

/-- `log (1 + x log² x) / log x → 1` as `x → ∞`: the exploration level `log f(x)` of the
asymptotically optimal UCB and KL-UCB algorithms, with `f(x) = 1 + x log² x`, is asymptotically
`log x`. -/
theorem tendsto_log_one_add_mul_log_sq_div_log_atTop :
    Tendsto (fun x ↦ log (1 + x * log x ^ 2) / log x) atTop (𝓝 1) := by
  have h_rem : Tendsto (fun x ↦ 1 + (log 2 + 2 * log (log x)) / log x) atTop (𝓝 1) := by
    have h_div : Tendsto (fun y ↦ log y / y) atTop (𝓝 0) := by
      simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h := ((tendsto_const_nhds (x := log 2)).div_atTop tendsto_log_atTop).add
      ((h_div.comp tendsto_log_atTop).const_mul 2)
    simpa [add_div, mul_div_assoc] using h.const_add 1
  -- For `x ≥ e`, `log x ≤ log (1 + x log² x) ≤ log (2 x log² x) = log 2 + log x + 2 log log x`.
  have h_large : ∀ᶠ x in atTop, 1 ≤ x ∧ 1 ≤ log x := by
    filter_upwards [eventually_ge_atTop (exp 1)] with x hx
    have hx0 : 0 < x := (exp_pos 1).trans_le hx
    exact ⟨(one_le_exp zero_le_one).trans hx, (le_log_iff_exp_le hx0).mpr hx⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_rem ?_ ?_
  · filter_upwards [h_large] with x ⟨hx1, hlog⟩
    have hsq : 1 ≤ log x ^ 2 := one_le_pow₀ hlog
    rw [le_div_iff₀ (by linarith), one_mul]
    exact log_le_log (by linarith) (by nlinarith)
  · filter_upwards [h_large] with x ⟨hx1, hlog⟩
    have hsq : 1 ≤ log x ^ 2 := one_le_pow₀ hlog
    have hL : log (1 + x * log x ^ 2) ≤ log 2 + log x + 2 * log (log x) := by
      calc log (1 + x * log x ^ 2) ≤ log (2 * x * log x ^ 2) :=
        log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith)])
      _ = log 2 + log x + 2 * log (log x) := by
        rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity),
          log_pow]
        push_cast
        ring
    rw [div_le_iff₀ (by linarith), add_mul, div_mul_cancel₀ _ (by linarith)]
    linarith

/-- For `p ≥ 1` and `x ≥ 1`, `log x / x ^ p ≤ 1 / e`, since `log x ≤ x / e` and `x ≤ x ^ p`. -/
theorem log_div_rpow_le_exp_neg_one {x p : ℝ} (hx : 1 ≤ x) (hp : 1 ≤ p) :
    log x / x ^ p ≤ exp (-1) := by
  have hx0 : 0 < x := by linarith
  have h_log : log x / x ≤ exp (-1) := by
    simpa [exp_neg, exp_log hx0, div_eq_mul_inv] using mul_exp_neg_le_exp_neg_one (log x)
  calc log x / x ^ p
  _ ≤ log x / x := div_le_div_of_nonneg_left (log_nonneg hx) hx0
    (by simpa using rpow_le_rpow_of_exponent_le hx hp)
  _ ≤ exp (-1) := h_log

/-- `log y ≤ y ^ γ / (e γ)` for `y ≥ 0` and `γ > 0`: Mathlib's `Real.log_le_rpow_div` sharpened by
the factor `e`.

Adapted from the formalization in the paper project RemyDegenne/Essakine2026Tight (same author),
file `ForLMLExplore/Analysis/SpecialFunctions/Pow/Real.lean`. -/
theorem log_le_rpow_div_exp_one_mul {y γ : ℝ} (hy : 0 ≤ y) (hγ : 0 < γ) :
    log y ≤ y ^ γ / (exp 1 * γ) := by
  rcases hy.eq_or_lt with rfl | hy
  · rw [log_zero, zero_rpow hγ.ne', zero_div]
  have hz : 0 < y ^ γ := rpow_pos_of_pos hy γ
  -- `log (y ^ γ / e) ≤ y ^ γ / e - 1`, and `log (y ^ γ / e) = γ log y - 1`
  have h := log_le_sub_one_of_pos (show 0 < y ^ γ / exp 1 by positivity)
  rw [log_div hz.ne' (exp_pos 1).ne', log_exp, log_rpow hy, sub_le_sub_iff_right] at h
  rw [le_div_iff₀ (exp_pos 1)] at h
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- If `1 ≤ y ≤ M (log y)²`, then `log y ≤ (8 / 5) log (4 M)`.

Adapted from the formalization in the paper project RemyDegenne/Essakine2026Tight (same author),
file `ForLMLExplore/Analysis/SpecialFunctions/Pow/Real.lean`, where `M > 0` is assumed. -/
theorem log_le_of_le_mul_sq_log {y M : ℝ} (hy : 1 ≤ y) (h : y ≤ M * log y ^ 2) :
    log y ≤ 8 / 5 * log (4 * M) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ log y := log_nonneg hy
  have hM : 0 < M := by
    by_contra! hM
    nlinarith [mul_nonneg (neg_nonneg.2 hM) (sq_nonneg (log y))]
  have he : 2.7 < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  -- `log y ≤ 16 / (3 e) y ^ (3 / 16)`, hence `log² y ≤ 4 y ^ (3 / 8)`
  have h1 : log y ≤ 16 / (3 * exp 1) * y ^ (3 / 16 : ℝ) := by
    calc log y ≤ y ^ (3 / 16 : ℝ) / (exp 1 * (3 / 16)) :=
          log_le_rpow_div_exp_one_mul hy0.le (by norm_num)
      _ = 16 / (3 * exp 1) * y ^ (3 / 16 : ℝ) := by field_simp
  have h2 : log y ^ 2 ≤ 4 * y ^ (3 / 8 : ℝ) := by
    calc log y ^ 2 ≤ (16 / (3 * exp 1) * y ^ (3 / 16 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog h1 2
      _ = (16 / (3 * exp 1)) ^ 2 * y ^ (3 / 8 : ℝ) := by
          rw [mul_pow, sq (y ^ (3 / 16 : ℝ)), ← rpow_add hy0]; norm_num
      _ ≤ 4 * y ^ (3 / 8 : ℝ) := by
          gcongr
          rw [div_pow, div_le_iff₀ (by positivity)]
          nlinarith
  -- so `y = y ^ (5 / 8) y ^ (3 / 8) ≤ 4 M y ^ (3 / 8)`, that is `y ^ (5 / 8) ≤ 4 M`
  have h3 : y ^ (5 / 8 : ℝ) ≤ 4 * M := by
    have hy38 : 0 < y ^ (3 / 8 : ℝ) := rpow_pos_of_pos hy0 _
    refine le_of_mul_le_mul_right ?_ hy38
    rw [← rpow_add hy0, show (5 / 8 : ℝ) + 3 / 8 = 1 by norm_num, rpow_one]
    calc y ≤ M * log y ^ 2 := h
      _ ≤ M * (4 * y ^ (3 / 8 : ℝ)) := by gcongr
      _ = 4 * M * y ^ (3 / 8 : ℝ) := by ring
  have h5 : 5 / 8 * log y ≤ log (4 * M) := by
    rw [← log_rpow hy0]
    exact log_le_log (rpow_pos_of_pos hy0 _) h3
  linarith

/-- If `g n / log n → D` as `n → ∞` and `D < c`, then eventually `g n < c log n`. -/
theorem eventually_lt_mul_log_of_tendsto_div_log {g : ℕ → ℝ} {D c : ℝ}
    (hg : Tendsto (fun n : ℕ ↦ g n / log n) atTop (𝓝 D)) (hc : D < c) :
    ∀ᶠ n : ℕ in atTop, g n < c * log n := by
  filter_upwards [hg.eventually_lt_const hc,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0] with n hn hlog
  exact (div_lt_iff₀ hlog).mp hn

/-- If `L n / log n → 1` as `n → ∞`, then `(L n / D + K) / log n → 1 / D`. Bounds of this shape
on the expected number of pulls of an arm come from the analysis of KL-UCB [LS, Theorem 10.6] at
an exploration level `L n`, for example `log (1 + n log² n)`. -/
theorem tendsto_div_add_div_log {L : ℕ → ℝ} (hL : Tendsto (fun n : ℕ ↦ L n / log n) atTop (𝓝 1))
    (D K : ℝ) : Tendsto (fun n : ℕ ↦ (L n / D + K) / log n) atTop (𝓝 D⁻¹) := by
  have h_log : Tendsto (fun n : ℕ ↦ log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have := (hL.mul_const D⁻¹).add ((tendsto_inv_atTop_zero.comp h_log).const_mul K)
  simp only [one_mul, mul_zero, add_zero] at this
  refine this.congr fun n ↦ ?_
  simp only [Function.comp_apply]
  ring

/-- If `L n / log n → 1` as `n → ∞`, then `(K + D (L n + √(b L n) + 1)) / log n → D` for every
`b ≥ 0`. Bounds of this shape on the expected number of pulls of an arm come from [LS, Lemma 8.2]
(with `b = π`) at an exploration level `L n`, for example `log n` or `log (1 + n log² n)`. -/
theorem tendsto_add_mul_add_sqrt_add_one_div_log {L : ℕ → ℝ}
    (hL : Tendsto (fun n : ℕ ↦ L n / log n) atTop (𝓝 1)) (K D : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ ↦ (K + D * (L n + √(b * L n) + 1)) / log n) atTop (𝓝 D) := by
  have h_log : Tendsto (fun n : ℕ ↦ log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_inv : Tendsto (fun n : ℕ ↦ (log n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp h_log
  -- `√(L n) / log n = √(L n / log n · (log n)⁻¹)` tends to `√(1 · 0) = 0`
  have h_sqrt : Tendsto (fun n : ℕ ↦ √(L n) / log n) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ √(L n / log n * (log n)⁻¹)) atTop (𝓝 0) := by
      simpa using (hL.mul h_inv).sqrt
    refine this.congr' ?_
    filter_upwards [h_log.eventually_gt_atTop 0] with n hn
    field_simp
    simp [sqrt_div', hn.le, mul_div_cancel₀ _ hn.ne']
  have := ((h_inv.const_mul (K + D)).add (hL.const_mul D)).add (h_sqrt.const_mul (D * √b))
  simp only [mul_zero, mul_one, zero_add, add_zero] at this
  refine this.congr fun n ↦ ?_
  rw [sqrt_mul hb]
  ring

/-- Let `0 < Δ`, `b ≥ 0`, `L n / log n → 1` and `C / Δ² < c`. If for every `ε ∈ (0, Δ)` some
constant `K` gives `x n ≤ K + C / (Δ - ε)² (L n + √(b L n) + 1)` for all `n`, then eventually
`x n ≤ c log n`; that is, `limsup_n x n / log n ≤ C / Δ²`. This turns finite-time bounds of the
shape of [LS, Lemma 8.2] on the expected number of pulls of an arm with gap `Δ` into asymptotic
ones. -/
theorem eventually_le_mul_log_of_forall_le_add_mul_add_sqrt_add_one {x L : ℕ → ℝ} {Δ C b c : ℝ}
    (hΔ : 0 < Δ) (hL : Tendsto (fun n : ℕ ↦ L n / log n) atTop (𝓝 1)) (hb : 0 ≤ b)
    (hx : ∀ ε ∈ Set.Ioo 0 Δ, ∃ K, ∀ n, x n ≤ K + C / (Δ - ε) ^ 2 * (L n + √(b * L n) + 1))
    (hc : C / Δ ^ 2 < c) :
    ∀ᶠ n : ℕ in atTop, x n ≤ c * log n := by
  -- choose `ε ∈ (0, Δ)` with `C / (Δ - ε)² < c`, by continuity at `ε = 0`
  have h_cont : ContinuousAt (fun ε : ℝ ↦ C / (Δ - ε) ^ 2) 0 :=
    continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 2)
      (by simpa using hΔ.ne')
  obtain ⟨ε, hεc, hε⟩ := ((h_cont.tendsto.mono_left nhdsWithin_le_nhds).eventually_lt_const
    (by simpa using hc)).and (Ioo_mem_nhdsGT hΔ) |>.exists
  obtain ⟨K, hK⟩ := hx ε hε
  filter_upwards [eventually_lt_mul_log_of_tendsto_div_log
    (tendsto_add_mul_add_sqrt_add_one_div_log hL K _ hb) hεc] with n hn
  exact (hK n).trans hn.le

/-- If `f n / log n → ∞` as `n → ∞`, then the natural ceilings `⌈f n - c⌉₊` also grow faster than
`log n`, which turns a real lower bound `f n - c` on a natural quantity into a natural one. -/
theorem tendsto_natCeil_sub_div_log {f : ℕ → ℝ} (c : ℝ)
    (hf : Tendsto (fun n : ℕ ↦ f n / log n) atTop atTop) :
    Tendsto (fun n : ℕ ↦ (⌈f n - c⌉₊ : ℝ) / log n) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ ↦ -c / log n) atTop (𝓝 0) := hlog.const_div_atTop _
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_add hc)
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  rw [← add_div, ← sub_eq_add_neg]
  exact div_le_div_of_nonneg_right (Nat.le_ceil _) hn.le

/-- **Inverting `x ↦ x - a log x`.** For `a > 0` and `x > 0`, `a log x + b < x` as soon as
`x ≥ 2 a log (2 a) + 2 b`. This turns a sample size condition of the form `a log n + b < n`, which
defines `n` only implicitly, into an explicit lower bound on `n`. -/
theorem mul_log_add_lt {a b x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (h : 2 * a * log (2 * a) + 2 * b ≤ x) : a * log x + b < x := by
  -- `log x = log (2 a) + log (x / (2 a)) ≤ log (2 a) + x / (2 a) - 1`.
  have hlog : log x ≤ log (2 * a) + x / (2 * a) - 1 := by
    have h_div := log_le_sub_one_of_pos (div_pos hx (mul_pos two_pos ha))
    rw [log_div hx.ne' (by positivity)] at h_div
    linarith
  have h_mul : a * log x ≤ a * log (2 * a) + x / 2 - a := by
    have := mul_le_mul_of_nonneg_left hlog ha.le
    rw [show a * (log (2 * a) + x / (2 * a) - 1) = a * log (2 * a) + x / 2 - a by
      field_simp] at this
    exact this
  linarith

/-- For `δ ∈ (0, 1]`, `log (x / δ) ≤ log (1 / δ) + log x`, with equality for `x ≠ 0`. The
thresholds `log (r n / δ)` of fixed-confidence identification are thus at most
`log (1 / δ) + log (r n)`. -/
theorem log_div_le_log_one_div_add_log (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    log (x / δ) ≤ log (1 / δ) + log x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [zero_div, log_zero, add_zero]
    exact log_nonneg (one_le_one_div hδ hδ1)
  · rw [log_div hx hδ.ne', one_div, log_inv]
    linarith

/-- If `r n = O(n ^ p)`, then `log (r n) ≤ ε n` for all large `n`, for every `ε > 0`. -/
theorem eventually_log_le_mul_of_isBigO {r : ℕ → ℝ} {p : ℝ}
    (hr : r =O[atTop] fun n ↦ (n : ℝ) ^ p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, log (r n) ≤ ε * n := by
  -- `log (r n) ≤ log C + p log n = o(n)`.
  obtain ⟨C, hC, hrC⟩ := hr.exists_pos
  have hg : (fun n : ℕ ↦ log C + p * log n) =o[atTop] fun n : ℕ ↦ (n : ℝ) :=
    ((Asymptotics.isLittleO_const_id_atTop (log C)).add
      (isLittleO_log_id_atTop.const_mul_left p)).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [hrC.bound, hg.bound hε, eventually_gt_atTop 0] with n hrn hgn hn
  rcases eq_or_ne (r n) 0 with h | h
  · simp only [h, log_zero]
    positivity
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (rpow_nonneg hn'.le p)] at hrn
  rw [Real.norm_of_nonneg hn'.le] at hgn
  calc log (r n)
  _ = log |r n| := (log_abs _).symm
  _ ≤ log (C * n ^ p) := log_le_log (abs_pos.2 h) hrn
  _ = log C + p * log n := by rw [log_mul hC.ne' (rpow_pos_of_pos hn' p).ne', log_rpow hn']
  _ ≤ ε * n := (le_abs_self _).trans hgn

/-- **The crossing time of the thresholds `log (1 / δ) + f T` by a statistic growing like `κ T`**
(the counting step of the asymptotic sample complexity of the GLRT, [GK16, proof of Theorem 14]).
Let `1 < κ c`, and let `f T ≤ ε T` eventually for every `ε > 0`. For every round `T₀` and every
finite `S`, for all small enough `δ`, there is a round `N ≥ T₀` with `N + S ≤ c log (1 / δ)`
such that `log (1 / δ) + f T < κ T` for every `T ≥ N`. -/
lemma eventually_exists_add_le_mul_and_forall_ofReal_add_lt_mul {κ c : ℝ≥0} (hκc : 1 < κ * c)
    {f : ℕ → ℝ} (hf : ∀ ε > 0, ∀ᶠ T in atTop, f T ≤ ε * T) (T₀ : ℕ) {S : ℝ≥0∞} (hS : S ≠ ∞) :
    ∀ᶠ δ in 𝓝[>] 0, ∃ N ≥ T₀, N + S ≤ c * ENNReal.ofReal (log (1 / δ)) ∧
      ∀ T ≥ N, ENNReal.ofReal (log (1 / δ) + f T) < κ * T := by
  have hκc' : 1 < (κ : ℝ) * c := mod_cast hκc
  have hc : 0 < (c : ℝ) := pos_of_mul_pos_right (one_pos.trans hκc') κ.coe_nonneg
  -- Choose `η` with `1 / c < η < κ`: if `log (1 / δ) ≤ η T`, the threshold is below `κ T`.
  obtain ⟨η, hcη, hηκ⟩ : ∃ η, (c : ℝ)⁻¹ < η ∧ η < κ :=
    exists_between ((inv_lt_iff_one_lt_mul₀' hc).2 (by linarith))
  have hη : 0 < η := (inv_pos.2 hc).trans hcη
  have hκ : 0 < (κ : ℝ) := hη.trans hηκ
  have hηc : 0 < (c : ℝ) - η⁻¹ := sub_pos.2 (inv_lt_of_inv_lt₀ hc hcη)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 (hf ((κ - η) / 2) (by linarith))
  set M := max (max T₀ T₁) 1
  have hL : Tendsto (fun δ : ℝ ↦ log (1 / δ)) (𝓝[>] 0) atTop := by
    simpa only [one_div, Function.comp_def] using tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  filter_upwards [hL.eventually_ge_atTop ((M + 1 + S.toReal) / (c - η⁻¹)),
    hL.eventually_ge_atTop 0] with δ hLδ hL0
  set L := log (1 / δ)
  -- From `N = max M ⌈L / η⌉` rounds on, `L ≤ η T`, so that `L + f T < κ T`.
  set N := max M ⌈L / η⌉₊
  refine ⟨N, by omega, ?_, fun T hT ↦ ?_⟩
  · -- `N + S ≤ M + L / η + 1 + S ≤ c L`.
    have hceil : (⌈L / η⌉₊ : ℝ) ≤ L / η + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have hN : (N : ℝ) ≤ M + (L / η + 1) := by
      rw [Nat.cast_max]
      have hM : (0 : ℝ) ≤ M := M.cast_nonneg
      exact max_le (by linarith [div_nonneg hL0 hη.le]) (by linarith)
    rw [div_le_iff₀ hηc] at hLδ
    have h_div : L / η = η⁻¹ * L := by ring
    calc (N : ℝ≥0∞) + S
    _ = ENNReal.ofReal (N + S.toReal) := by
      rw [ENNReal.ofReal_add N.cast_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_natCast,
        ENNReal.ofReal_toReal hS]
    _ ≤ ENNReal.ofReal (c * L) := ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = c * ENNReal.ofReal L := by rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  · have hT1 : (1 : ℝ) ≤ T := mod_cast (show 1 ≤ T by omega)
    have hLT : L ≤ η * T := by
      rw [← div_le_iff₀' hη]
      exact (Nat.le_ceil _).trans (mod_cast (le_max_right _ _).trans hT)
    have hfT := hT₁ T (by omega)
    calc ENNReal.ofReal (L + f T)
    _ < ENNReal.ofReal (κ * T) := by
      refine (ENNReal.ofReal_lt_ofReal_iff (mul_pos hκ (by linarith))).2 ?_
      nlinarith
    _ = κ * T := by
      rw [ENNReal.ofReal_mul κ.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast]

/-- `log (1 + y / x) = log (x + y) - log x` for `x ≠ 0` and `x + y ≠ 0`. -/
theorem log_one_add_div {x y : ℝ} (hx : x ≠ 0) (hxy : x + y ≠ 0) :
    log (1 + y / x) = log (x + y) - log x := by
  rw [← log_div hxy hx, one_add_div hx]

/-- `1 ≤ (x + 1 / 2) log (1 + x⁻¹)` for `x > 0`: the first term of the series of
`log (1 + 1 / x)` in powers of `1 / (2 x + 1)` (`Real.hasSum_log_one_add_inv`). -/
theorem one_le_add_half_mul_log_one_add_inv {x : ℝ} (hx : 0 < x) :
    1 ≤ (x + 1 / 2) * log (1 + x⁻¹) := by
  have h0 := le_hasSum (hasSum_log_one_add_inv hx) 0 (fun j _ ↦ by positivity)
  simp only [CharP.cast_eq_zero, mul_zero, zero_add, div_one, mul_one, pow_one] at h0
  have hpos : 0 < 2 * x + 1 := by linarith
  calc (1 : ℝ) = (x + 1 / 2) * (2 * (1 / (2 * x + 1))) := by field_simp
    _ ≤ _ := by gcongr

/-- `(1 + t) log (1 + t) - t - t log (1 + t / 2) ≤ 0` for `t ≥ 0`: the function vanishes at `0`
and its derivative `log ((1 + t) / (1 + t / 2)) - t / (2 + t)` is nonpositive. -/
theorem one_add_mul_log_one_add_sub_sub_mul_log_nonpos {t : ℝ} (ht : 0 ≤ t) :
    (1 + t) * log (1 + t) - t - t * log (1 + t / 2) ≤ 0 := by
  set f : ℝ → ℝ := fun t ↦ (1 + t) * log (1 + t) - t - t * log (1 + t / 2) with hf
  have hderiv : ∀ x, 0 ≤ x →
      HasDerivAt f (log (1 + x) - log (1 + x / 2) - x / (2 + x)) x := by
    intro x hx
    have h1 : (1 + x) ≠ 0 := by linarith
    have h2 : (1 + x / 2) ≠ 0 := by linarith
    have := ((((hasDerivAt_id' x).const_add 1).mul
      (((hasDerivAt_id' x).const_add 1).log h1)).sub (hasDerivAt_id' x)).sub
      ((hasDerivAt_id' x).mul ((((hasDerivAt_id' x).div_const 2).const_add 1).log h2))
    convert this using 1
    field_simp
    ring
  have hanti : AntitoneOn f (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x hx ↦ (hderiv x hx).continuousAt.continuousWithinAt) ?_ ?_
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (le_of_lt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : 0 < x := hx
      rw [(hderiv x hx'.le).deriv]
      have hx0 : 0 < 1 + x / 2 := by linarith
      have : log (1 + x) - log (1 + x / 2) ≤ x / (2 + x) := by
        rw [← log_div (by linarith) hx0.ne']
        refine (log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
        field_simp
        ring
      linarith
  have := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  simpa [hf] using this

/-- `(m + 1) log (m + 1) - m log m - log (m + 1 / 2) ≤ 1` for every `m : ℕ`. -/
theorem add_one_mul_log_sub_le_one (m : ℕ) :
    ((m : ℝ) + 1) * log ((m : ℝ) + 1) - m * log m - log ((m : ℝ) + 1 / 2) ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : log (1 / 2 : ℝ) = - log 2 := by rw [one_div, log_inv]
    simp only [CharP.cast_eq_zero, zero_add, one_mul, log_one, zero_mul, sub_zero, this]
    linarith [log_two_lt_d9]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h := one_add_mul_log_one_add_sub_sub_mul_log_nonpos (t := (m : ℝ)⁻¹) (by positivity)
  have e1 : log (1 + (m : ℝ)⁻¹) = log ((m : ℝ) + 1) - log m := by
    rw [inv_eq_one_div, log_one_add_div hm'.ne' (by positivity)]
  have e2 : log (1 + (m : ℝ)⁻¹ / 2) = log ((m : ℝ) + 1 / 2) - log m := by
    rw [← log_one_add_div hm'.ne' (by positivity), div_div, mul_comm, ← div_div, one_div]
  rw [e1, e2] at h
  have h' := mul_le_mul_of_nonneg_left h hm'.le
  have : (m : ℝ) * ((1 + (m : ℝ)⁻¹) * (log (↑m + 1) - log ↑m) - (m : ℝ)⁻¹ -
      (m : ℝ)⁻¹ * (log (↑m + 1 / 2) - log ↑m)) =
      ((m : ℝ) + 1) * log ((m : ℝ) + 1) - m * log m - log ((m : ℝ) + 1 / 2) - 1 := by
    field_simp
    ring
  rw [this] at h'
  linarith

end Real
