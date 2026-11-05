/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary bounds on the real logarithm

## Main statements

* `Real.min_one_le_two_mul_log_one_add`: `min 1 u ≤ 2 log (1 + u)` for `u ≥ 0`.
* `Real.monotoneOn_log_one_add_mul_log_sq`: `x ↦ log (1 + x log² x)` is monotone on `[1, ∞)`.
* `Real.log_natCast_le_log_natCast`: `log` is monotone on natural numbers.
* `Real.monotone_log_two_mul_mul_add_one`: `n ↦ log (2 n (n + 1))` is monotone on `ℕ`.
* `Real.tendsto_log_one_add_mul_log_sq_div_log_atTop`: `log (1 + x log² x) / log x → 1` as
  `x → ∞`.
* `Real.eventually_lt_mul_log_of_tendsto_div_log`: if `g n / log n → D` and `D < c`, then
  eventually `g n < c log n`.
* `Real.tendsto_add_mul_add_sqrt_add_one_div_log`: if `L n / log n → 1`, then
  `(K + D (L n + √(b L n) + 1)) / log n → D`.
* `Real.eventually_le_mul_log_of_forall_le_add_mul_add_sqrt_add_one`: if for every `ε ∈ (0, Δ)`,
  `x n ≤ K_ε + C / (Δ - ε)² (L n + √(b L n) + 1)` and `L n / log n → 1`, then eventually
  `x n ≤ c log n` for every `c > C / Δ²`.
* `Real.tendsto_natCeil_sub_div_log`: if `f n / log n → ∞`, then `⌈f n - c⌉₊ / log n → ∞`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Filter Topology

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

/-- If `g n / log n → D` as `n → ∞` and `D < c`, then eventually `g n < c log n`. -/
theorem eventually_lt_mul_log_of_tendsto_div_log {g : ℕ → ℝ} {D c : ℝ}
    (hg : Tendsto (fun n : ℕ ↦ g n / log n) atTop (𝓝 D)) (hc : D < c) :
    ∀ᶠ n : ℕ in atTop, g n < c * log n := by
  filter_upwards [hg.eventually_lt_const hc,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0] with n hn hlog
  exact (div_lt_iff₀ hlog).mp hn

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

end Real
