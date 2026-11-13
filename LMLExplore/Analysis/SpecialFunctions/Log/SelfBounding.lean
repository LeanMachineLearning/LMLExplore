/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Real.Sqrt
public import LMLExplore.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The self-bounding inequality

Sample complexity analyses of exploration algorithms bound the number of rounds `τ` by an
implicit inequality in which `τ` appears on both sides, under a square root and inside
logarithms: with `L = log (α τ)`,
`τ ≤ C √(τ (A L + B L²)) + D (A L + E L²)`.
This file solves it for `τ`, for `α ≥ e`, `A, B, C, D ≥ 0` and `B ≤ E`. Write
`K = C² (A + B) + (D + 2 √D C) (A + E)`.

## Main statements

* `Real.le_mul_sq_of_le_sqrt_mul_add`: the same hypothesis with any `L ≥ 1` in place of
  `log (α τ)` gives `τ ≤ K L²`.
* `Real.log_le_of_le_sqrt_mul_add`: if `τ ≥ 1`, then `L ≤ (8 / 5) log (4 α K)`.
* `Real.le_mul_sq_log_add_one_of_le_sqrt_mul_add`: `τ ≤ K ((8 / 5) log M)² + 1` for every
  `M ≥ 4 α K`.
* `Real.le_of_le_sqrt_mul_add`: **the self-bounding inequality** [MDJKLV21, Lemma 13],
  `τ ≤ C² (A + B) C₁² + (D + 2 √D C) (A + E) C₁² + 1` with
  `C₁ = (8 / 5) log (11 α² (A + E) (C + √D)²)`.
* `Real.le_of_le_sqrt_mul_add'`: the same bound with `C₁ = (8 / 5) log (11 α² (A + E) (C + D)²)`,
  for `D ≥ 1`.

[MDJKLV21, Lemma 13] and [EV26, Lemma 29] state the bound with
`C₁ = (8 / 5) log (11 α² (A + E) (C + D))` and assume `A, B, C, D > 0` and `B ≥ 1`. That constant
is too small: `α = e`, `B = E = 1`, `C = 1000`, `A = D = 10⁻⁶` and `τ = 4 · 10⁸` satisfy the
hypothesis but not the conclusion. The corrected bound `Real.le_of_le_sqrt_mul_add`, with
`(C + √D)²`, holds for all `D ≥ 0` and needs neither the positivity assumptions nor `B ≥ 1`.
Squaring `C + D` also gives a valid bound when `D ≥ 1` (an assumption the paper does not make),
which is `Real.le_of_le_sqrt_mul_add'`.

## Implementation notes

The statements and proofs are adapted from the formalization in the paper project
RemyDegenne/Essakine2026Tight (same author), file
`ForLMLExplore/Analysis/SpecialFunctions/Log/SelfBounding.lean`. Here the quadratic part
`Real.le_mul_sq_of_le_sqrt_mul_add` holds for any `L ≥ 1` rather than only `L = log (α τ)`, and
the final bounds do not assume `τ ≥ 0`.

## References

* [MDJKLV21] P. Ménard, O. D. Domingues, A. Jonsson, E. Kaufmann, E. Leurent and M. Valko,
  *Fast active learning for pure exploration in reinforcement learning*, ICML 2021,
  arXiv:2007.13442, Lemma 13.
* [EV26] A. Essakine and C. Vernade, *Tight sample complexity bounds for entropic best policy
  identification*, COLT 2026, arXiv:2605.13717, Lemma 29.
-/

public section

namespace Real

variable {A B C D E α τ : ℝ}

/-- The quadratic part of the self-bounding inequality: if `L ≥ 1` and
`τ ≤ C √(τ (A L + B L²)) + D (A L + E L²)` with `A, B, C, D ≥ 0` and `B ≤ E`, then `τ ≤ K L²` for
`K = C² (A + B) + (D + 2 √D C) (A + E)`. -/
theorem le_mul_sq_of_le_sqrt_mul_add {L : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : B ≤ E) (hL : 1 ≤ L)
    (h : τ ≤ C * √(τ * (A * L + B * L ^ 2)) + D * (A * L + E * L ^ 2)) :
    τ ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * L ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hAB : 0 ≤ A + B := by linarith
  have hAE : 0 ≤ A + E := by linarith
  rcases lt_or_ge τ 0 with hτ | hτ
  · have : 0 ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * L ^ 2 := by positivity
    linarith
  -- `A L ≤ A L²` since `L ≥ 1`
  have hAL : A * L ≤ A * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hA
  -- the quadratic inequality `τ ≤ C L √(A + B) √τ + D (A + E) L²` in `√τ`
  have hτ' : τ ≤ C * L * √(A + B) * √τ + D * (A + E) * L ^ 2 := by
    calc τ ≤ C * √(τ * (A * L + B * L ^ 2)) + D * (A * L + E * L ^ 2) := h
      _ ≤ C * √(τ * ((A + B) * L ^ 2)) + D * ((A + E) * L ^ 2) := by gcongr <;> linarith
      _ = C * L * √(A + B) * √τ + D * (A + E) * L ^ 2 := by
          rw [show τ * ((A + B) * L ^ 2) = L ^ 2 * ((A + B) * τ) by ring,
            sqrt_mul (by positivity), sqrt_sq hL0, sqrt_mul hAB]
          ring
  -- its solution `√τ ≤ C L √(A + B) + √D √(A + E) L`
  have hx : √τ ≤ C * L * √(A + B) + √D * √(A + E) * L := by
    have := le_add_sqrt_of_sq_le (x := √τ) (b := C * L * √(A + B)) (c := D * (A + E) * L ^ 2)
      (by positivity) (mul_nonneg (mul_nonneg hD hAE) (sq_nonneg L))
      (by rw [sq_sqrt hτ]; linarith)
    rwa [sqrt_mul (mul_nonneg hD hAE), sqrt_mul hD, sqrt_sq hL0] at this
  have hae : √(A + B) * √(A + E) ≤ A + E := by
    calc √(A + B) * √(A + E) ≤ √(A + E) * √(A + E) := by gcongr
      _ = A + E := mul_self_sqrt hAE
  calc τ = √τ ^ 2 := (sq_sqrt hτ).symm
    _ ≤ (C * L * √(A + B) + √D * √(A + E) * L) ^ 2 := by gcongr
    _ = L ^ 2 * (C ^ 2 * (A + B) + D * (A + E))
        + 2 * C * √D * L ^ 2 * (√(A + B) * √(A + E)) := by
        linear_combination (C ^ 2 * L ^ 2) * sq_sqrt hAB + (L ^ 2 * √D ^ 2) * sq_sqrt hAE
          + (L ^ 2 * (A + E)) * sq_sqrt hD
    _ ≤ L ^ 2 * (C ^ 2 * (A + B) + D * (A + E)) + 2 * C * √D * L ^ 2 * (A + E) := by gcongr
    _ = (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * L ^ 2 := by ring

/-- The logarithm in the self-bounding inequality: `log (α τ) ≤ (8 / 5) log (4 α K)` with
`K = C² (A + B) + (D + 2 √D C) (A + E)`, for `α ≥ e` and `τ ≥ 1`. -/
theorem log_le_of_le_sqrt_mul_add (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hE : B ≤ E) (hα : exp 1 ≤ α) (hτ : 1 ≤ τ)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2)) :
    log (α * τ) ≤ 8 / 5 * log (4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))) := by
  set K := C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)
  have hα0 : 0 < α := (exp_pos 1).trans_le hα
  have hτK := le_mul_sq_of_le_sqrt_mul_add hA hB hC hD hE (one_le_log_mul hα hτ) h
  rw [mul_assoc]
  refine log_le_of_le_mul_sq_log (one_le_mul_of_one_le_of_one_le
    ((one_le_exp zero_le_one).trans hα) hτ) ?_
  calc α * τ ≤ α * (K * log (α * τ) ^ 2) := by gcongr
    _ = α * K * log (α * τ) ^ 2 := by ring

/-- The self-bounding inequality, general form: if `τ` satisfies
`τ ≤ C √(τ (A L + B L²)) + D (A L + E L²)` with `L = log (α τ)`, `α ≥ e`, `A, B, C, D ≥ 0` and
`B ≤ E`, then `τ ≤ K ((8 / 5) log M)² + 1` for every `M ≥ 4 α K`, where
`K = C² (A + B) + (D + 2 √D C) (A + E)`. -/
theorem le_mul_sq_log_add_one_of_le_sqrt_mul_add (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : B ≤ E) (hα : exp 1 ≤ α)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2))
    {M : ℝ} (hM : 4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) ≤ M) :
    τ ≤ (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)) * (8 / 5 * log M) ^ 2 + 1 := by
  set K := C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E)
  have hK : 0 ≤ K := by have := hB.trans hE; positivity
  rcases le_or_gt τ 1 with h1 | h1
  · nlinarith [sq_nonneg (8 / 5 * log M)]
  have hα0 : 0 < α := (exp_pos 1).trans_le hα
  have hL1 := one_le_log_mul hα h1.le
  have hτK := le_mul_sq_of_le_sqrt_mul_add hA hB hC hD hE hL1 h
  have hK0 : 0 < K := by
    by_contra! hK
    nlinarith [sq_nonneg (log (α * τ))]
  have hL : log (α * τ) ≤ 8 / 5 * log M :=
    (log_le_of_le_sqrt_mul_add hA hB hC hD hE hα h1.le h).trans (by gcongr)
  calc τ ≤ K * log (α * τ) ^ 2 := hτK
    _ ≤ K * (8 / 5 * log M) ^ 2 := by gcongr
    _ ≤ K * (8 / 5 * log M) ^ 2 + 1 := by linarith

/-- `4 α K ≤ 11 α² (A + E) (C + √D)²` for `K = C² (A + B) + (D + 2 √D C) (A + E)` and `α ≥ e`. -/
private lemma four_mul_mul_le_mul_sq_add_sqrt (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hE : B ≤ E) (hα : exp 1 ≤ α) :
    4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))
      ≤ 11 * α ^ 2 * (A + E) * (C + √D) ^ 2 := by
  have hE0 : 0 ≤ E := hB.trans hE
  have he : 2.7 < exp 1 := lt_trans (by norm_num) exp_one_gt_d9
  -- `K ≤ (A + E) (C + √D)²` since `B ≤ E`, and `4 α ≤ 11 α²` since `α ≥ e`
  have hK : C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E) ≤ (A + E) * (C + √D) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hE (sq_nonneg C), sq_sqrt hD]
  have h4 : 4 * α ≤ 11 * α ^ 2 := by nlinarith
  calc 4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))
      ≤ 11 * α ^ 2 * ((A + E) * (C + √D) ^ 2) := by
        gcongr
    _ = 11 * α ^ 2 * (A + E) * (C + √D) ^ 2 := by ring

/-- **The self-bounding inequality** [MDJKLV21, Lemma 13], with the corrected constant: if `τ`
satisfies `τ ≤ C √(τ (A L + B L²)) + D (A L + E L²)` with `L = log (α τ)`, `α ≥ e`,
`A, B, C, D ≥ 0` and `B ≤ E`, then `τ ≤ C² (A + B) C₁² + (D + 2 √D C) (A + E) C₁² + 1` with
`C₁ = (8 / 5) log (11 α² (A + E) (C + √D)²)`. -/
theorem le_of_le_sqrt_mul_add (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : B ≤ E)
    (hα : exp 1 ≤ α)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2)) :
    τ ≤ C ^ 2 * (A + B) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + √D) ^ 2)) ^ 2
      + (D + 2 * √D * C) * (A + E) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + √D) ^ 2)) ^ 2
      + 1 := by
  have := le_mul_sq_log_add_one_of_le_sqrt_mul_add hA hB hC hD hE hα h
    (four_mul_mul_le_mul_sq_add_sqrt hA hB hC hD hE hα)
  linarith

/-- **The self-bounding inequality** [MDJKLV21, Lemma 13] for `D ≥ 1`, with the constant
`C₁ = (8 / 5) log (11 α² (A + E) (C + D)²)`: if `τ` satisfies
`τ ≤ C √(τ (A L + B L²)) + D (A L + E L²)` with `L = log (α τ)`, `α ≥ e`, `A, B, C ≥ 0` and
`B ≤ E`, then `τ ≤ C² (A + B) C₁² + (D + 2 √D C) (A + E) C₁² + 1`. -/
theorem le_of_le_sqrt_mul_add' (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 1 ≤ D) (hE : B ≤ E)
    (hα : exp 1 ≤ α)
    (h : τ ≤ C * √(τ * (A * log (α * τ) + B * log (α * τ) ^ 2))
      + D * (A * log (α * τ) + E * log (α * τ) ^ 2)) :
    τ ≤ C ^ 2 * (A + B) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + D) ^ 2)) ^ 2
      + (D + 2 * √D * C) * (A + E) * (8 / 5 * log (11 * α ^ 2 * (A + E) * (C + D) ^ 2)) ^ 2
      + 1 := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hE0 : 0 ≤ E := hB.trans hE
  have hsqrt : √D ≤ D := (sqrt_le_left hD0).2 (by nlinarith)
  have hM : 4 * α * (C ^ 2 * (A + B) + (D + 2 * √D * C) * (A + E))
      ≤ 11 * α ^ 2 * (A + E) * (C + D) ^ 2 :=
    (four_mul_mul_le_mul_sq_add_sqrt hA hB hC hD0 hE hα).trans (by gcongr)
  have := le_mul_sq_log_add_one_of_le_sqrt_mul_add hA hB hC hD0 hE hα h hM
  linarith

end Real
