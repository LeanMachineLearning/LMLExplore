/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Solving the inequality `t - C √(t log t) ≤ T`

The sample complexity analyses of pure exploration algorithms with non-asymptotic guarantees
[DKM19] end with an inequality satisfied by every round `t` at which the algorithm has not stopped:
the stopping statistic grows like `D t` up to a deviation of order `√(t log t)`, so that
`t - C √(t log t) ≤ T` with `T = log (1 / δ) / D`. This file solves that inequality for `t`.

The function `t ↦ √(t log t)` is concave on `[1, ∞)`, so it lies below its tangent lines: for
`T > 1` and `t ≥ 1`,
`√(t log t) ≤ √(T log T) + (1 + log T) / (2 √(T log T)) (t - T)`.
The proof writes `2 √(t log t) ≤ t s + log t / s` with `s = √(log T / T)` (the arithmetic-geometric
mean inequality, with equality at `t = T`) and bounds `log t` by its tangent `log T + t / T - 1`.
With `κ = C (1 + log T) / (2 √(T log T)) < 1`, the inequality `t - C √(t log t) ≤ T` then gives
`(t - T) (1 - κ) ≤ C √(T log T)`, that is
`t ≤ T + C √(T log T) / (1 - κ) = T (1 + C √(log T / T) / (1 - κ))` [DKM19, Lemma 2].
Since `√(T log T) = o(T)` and `κ → 0` as `T → ∞`, the bound is `T (1 + o(1))`.

The function `t ↦ √(t log t)` is not Mathlib's `x ↦ √x * log x`, whose strict concavity on
`(1, ∞)` is `strictConcaveOn_sqrt_mul_log_Ioi`.

## Main statements

* `Real.sqrt_mul_log_le_add_mul_sub`: the tangent line bound on `√(t log t)`.
* `Real.le_add_mul_sqrt_mul_log_div_of_sub_le` [DKM19, Lemma 2]: if `C ≥ 0`, `T > 1`,
  `κ = C (1 + log T) / (2 √(T log T)) < 1` and `t - C √(t log t) ≤ T`, then
  `t ≤ T + C √(T log T) / (1 - κ)`.
* `Real.isLittleO_mul_sqrt_mul_log_div_atTop`: the excess `C √(T log T) / (1 - κ)` of this bound
  over `T` is `o(T)` as `T → ∞`.

## References

* [DKM19] R. Degenne, W. M. Koolen and P. Ménard, *Non-asymptotic pure exploration by solving
  games*, NeurIPS 2019, Lemma 2 (in the numbering of arXiv:1906.10431).
-/

public section

open Filter Asymptotics

namespace Real

/-- **The tangent lines of `t ↦ √(t log t)`.** For `T > 1` and `t ≥ 1`,
`√(t log t) ≤ √(T log T) + (1 + log T) / (2 √(T log T)) (t - T)`: the function `t ↦ √(t log t)`,
concave on `[1, ∞)`, lies below its tangent line at `T`. -/
theorem sqrt_mul_log_le_add_mul_sub {t T : ℝ} (ht : 1 ≤ t) (hT : 1 < T) :
    √(t * log t) ≤ √(T * log T) + (1 + log T) / (2 * √(T * log T)) * (t - T) := by
  have hT0 : 0 < T := one_pos.trans hT
  have ht0 : 0 < t := one_pos.trans_le ht
  have hTL : 0 < T * log T := mul_pos hT0 (log_pos hT)
  set r := √(T * log T) with hr
  have hr0 : 0 < r := sqrt_pos.2 hTL
  have hr2 : r ^ 2 = T * log T := sq_sqrt hTL.le
  set s := r / T with hs
  have hs0 : 0 < s := div_pos hr0 hT0
  -- the arithmetic-geometric mean inequality `2 √(t log t) ≤ t s + log t / s`
  have hamgm : 2 * √(t * log t) ≤ t * s + log t / s := by
    have hprod : √(t * log t) = √(t * s) * √(log t / s) := by
      rw [← sqrt_mul (by positivity)]
      congr 1
      field_simp
    have h := two_mul_le_add_sq (√(t * s)) (√(log t / s))
    rwa [sq_sqrt (by positivity), sq_sqrt (div_nonneg (log_nonneg ht) hs0.le), mul_assoc,
      ← hprod] at h
  -- the tangent line `log t ≤ log T + t / T - 1` of the logarithm
  have hlog : log t ≤ log T + t / T - 1 := by
    have h := log_le_sub_one_of_pos (div_pos ht0 hT0)
    rw [log_div ht0.ne' hT0.ne'] at h
    linarith
  -- with `s = √(T log T) / T`, the bound is twice the tangent line at `T`
  have hkey : t * s + (log T + t / T - 1) / s = 2 * (r + (1 + log T) / (2 * r) * (t - T)) := by
    rw [hs]
    field_simp
    linear_combination (t - 2 * T) * hr2
  have hdiv : log t / s ≤ (log T + t / T - 1) / s := div_le_div_of_nonneg_right hlog hs0.le
  linarith

/-- **Solving `t - C √(t log t) ≤ T`** [DKM19, Lemma 2]. Let `C ≥ 0` and `T > 1` with
`κ = C (1 + log T) / (2 √(T log T)) < 1`. Every real `t` with `t - C √(t log t) ≤ T` satisfies
`t ≤ T + C √(T log T) / (1 - κ)`.

Since `C √(T log T) = T · C √(log T / T)`, this is the bound
`t ≤ T (1 + C √(log T / T) / (1 - κ))` of [DKM19, Lemma 2], where `T = log (1 / δ) / D` is the
leading term of the sample complexity. -/
theorem le_add_mul_sqrt_mul_log_div_of_sub_le {C T t : ℝ} (hC : 0 ≤ C) (hT : 1 < T)
    (hκ : C * (1 + log T) / (2 * √(T * log T)) < 1) (ht : t - C * √(t * log t) ≤ T) :
    t ≤ T + C * √(T * log T) / (1 - C * (1 + log T) / (2 * √(T * log T))) := by
  set κ := C * (1 + log T) / (2 * √(T * log T)) with hκdef
  have hκ' : 0 < 1 - κ := sub_pos.2 hκ
  have hB : 0 ≤ C * √(T * log T) / (1 - κ) := div_nonneg (mul_nonneg hC (sqrt_nonneg _)) hκ'.le
  rcases lt_or_ge t 1 with h1 | h1
  · linarith
  -- by the tangent line at `T`, `C √(t log t) ≤ C √(T log T) + κ (t - T)`
  have htan := mul_le_mul_of_nonneg_left (sqrt_mul_log_le_add_mul_sub h1 hT) hC
  have hκeq : C * ((1 + log T) / (2 * √(T * log T)) * (t - T)) = κ * (t - T) := by
    rw [hκdef]
    ring
  have h : (t - T) * (1 - κ) ≤ C * √(T * log T) := by nlinarith
  rw [← le_div_iff₀ hκ'] at h
  linarith

/-- `√(T log T) = o(T)` as `T → ∞`. -/
theorem isLittleO_sqrt_mul_log_atTop : (fun T ↦ √(T * log T)) =o[atTop] id := by
  refine isLittleO_iff.2 fun c hc ↦ ?_
  filter_upwards [isLittleO_iff.1 isLittleO_log_id_atTop (pow_pos hc 2), eventually_ge_atTop 1]
    with T hT hT1
  have hT0 : 0 ≤ T := zero_le_one.trans hT1
  rw [norm_of_nonneg (sqrt_nonneg _), id, norm_of_nonneg hT0]
  rw [norm_of_nonneg (log_nonneg hT1), id, norm_of_nonneg hT0] at hT
  calc √(T * log T) ≤ √((c * T) ^ 2) :=
        sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hT hT0])
    _ = c * T := sqrt_sq (by positivity)

/-- `(1 + log T) / (2 √(T log T)) → 0` as `T → ∞`. -/
theorem tendsto_one_add_log_div_two_mul_sqrt_mul_log_atTop :
    Tendsto (fun T ↦ (1 + log T) / (2 * √(T * log T))) atTop (nhds 0) := by
  -- for `T ≥ e`, `(1 + log T) / (2 √(T log T)) ≤ log T / √(T log T) = √(T log T) / T`
  have hlim : Tendsto (fun T ↦ √(T * log T) / T) atTop (nhds 0) := by
    simpa using isLittleO_sqrt_mul_log_atTop.tendsto_div_nhds_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg (by linarith [log_nonneg hT]) (by positivity)
  · filter_upwards [eventually_ge_atTop (exp 1)] with T hT
    have hT1 : 1 < T := (one_lt_exp_iff.2 one_pos).trans_le hT
    have hT0 : 0 < T := one_pos.trans hT1
    have hL1 : 1 ≤ log T := by rwa [le_log_iff_exp_le hT0]
    have hTL : 0 < T * log T := mul_pos hT0 (log_pos hT1)
    have hr0 : 0 < √(T * log T) := sqrt_pos.2 hTL
    have hr2 : √(T * log T) ^ 2 = T * log T := sq_sqrt hTL.le
    rw [div_le_div_iff₀ (by positivity) hT0]
    nlinarith

/-- **The bound of [DKM19, Lemma 2] is `T (1 + o(1))`.** For every `C`, the excess
`C √(T log T) / (1 - κ)`, with `κ = C (1 + log T) / (2 √(T log T))`, of the bound of
`Real.le_add_mul_sqrt_mul_log_div_of_sub_le` over `T` is `o(T)` as `T → ∞`. -/
theorem isLittleO_mul_sqrt_mul_log_div_atTop (C : ℝ) :
    (fun T ↦ C * √(T * log T) / (1 - C * (1 + log T) / (2 * √(T * log T)))) =o[atTop] id := by
  have hκ : Tendsto (fun T ↦ 1 - C * (1 + log T) / (2 * √(T * log T))) atTop (nhds 1) := by
    simpa [mul_div_assoc] using
      (tendsto_one_add_log_div_two_mul_sqrt_mul_log_atTop.const_mul C).const_sub 1
  have hinv : (fun T ↦ (1 - C * (1 + log T) / (2 * √(T * log T)))⁻¹) =O[atTop]
      (fun _ ↦ (1 : ℝ)) := by
    simpa using (hκ.inv₀ one_ne_zero).isBigO_one ℝ
  exact ((isLittleO_sqrt_mul_log_atTop.const_mul_left C).mul_isBigO hinv).congr
    (fun T ↦ (div_eq_mul_inv _ _).symm) fun T ↦ mul_one _

end Real
