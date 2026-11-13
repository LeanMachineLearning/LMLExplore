/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The log-sum inequality

For nonnegative numbers `x i` and `z i` indexed by a finite set `s`, with `x i = 0` whenever
`z i = 0`, the **log-sum inequality** states
`(∑ i ∈ s, x i) * log ((∑ i ∈ s, x i) / ∑ i ∈ s, z i) ≤ ∑ i ∈ s, x i * log (x i / z i)`.
It is Jensen's inequality for the convex function `t ↦ t log t` (`Real.convexOn_mul_log`), with
the weights `z i / ∑ j ∈ s, z j` at the points `x i / z i`. Applied to the two blocks of a
partition of a finite set, it bounds the relative entropy between two probability vectors from
below by the binary relative entropy of the masses of one block, which is how Pinsker's inequality
for probability vectors follows from its binary case.

## Main statements

* `Real.sum_mul_log_div_sum_le_sum_mul_log_div`: the log-sum inequality.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
  Theorem 2.7.1.
-/

public section

open Finset

namespace Real

/-- **Log-sum inequality.** For `x i ≥ 0` and `z i ≥ 0` on a finite set `s`, with `x i = 0`
whenever `z i = 0`,
`(∑ i ∈ s, x i) * log ((∑ i ∈ s, x i) / ∑ i ∈ s, z i) ≤ ∑ i ∈ s, x i * log (x i / z i)`. -/
theorem sum_mul_log_div_sum_le_sum_mul_log_div {ι : Type*} (s : Finset ι) {x z : ι → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hz : ∀ i ∈ s, 0 ≤ z i) (hxz : ∀ i ∈ s, z i = 0 → x i = 0) :
    (∑ i ∈ s, x i) * log ((∑ i ∈ s, x i) / ∑ i ∈ s, z i) ≤
      ∑ i ∈ s, x i * log (x i / z i) := by
  set X := ∑ i ∈ s, x i
  set Z := ∑ i ∈ s, z i
  rcases (sum_nonneg hz).eq_or_lt with hZ | hZ
  · -- all `z i`, hence all `x i`, vanish
    have hx0 : ∀ i ∈ s, x i = 0 :=
      fun i hi ↦ hxz i hi ((sum_eq_zero_iff_of_nonneg hz).1 hZ.symm i hi)
    have hX : X = 0 := sum_eq_zero hx0
    rw [hX, zero_mul, sum_eq_zero fun i hi ↦ by rw [hx0 i hi, zero_mul]]
  have hzx (i : ι) (hi : i ∈ s) : z i * (x i / z i) = x i := by
    rcases eq_or_ne (z i) 0 with h | h
    · rw [h, hxz i hi h, zero_mul]
    · exact mul_div_cancel₀ (x i) h
  -- Jensen's inequality for `t ↦ t log t`, with the weights `z i / Z` at the points `x i / z i`
  have h := convexOn_mul_log.map_sum_le (t := s) (w := fun i ↦ z i / Z)
    (p := fun i ↦ x i / z i) (fun i hi ↦ div_nonneg (hz i hi) hZ.le)
    (by rw [← sum_div, div_self hZ.ne'])
    (fun i hi ↦ Set.mem_Ici.2 (div_nonneg (hx i hi) (hz i hi)))
  have h_pt : ∑ i ∈ s, (z i / Z) • (x i / z i) = X / Z := by
    rw [sum_div]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [smul_eq_mul, div_mul_eq_mul_div, hzx i hi]
  have h_val : ∑ i ∈ s, (z i / Z) • (x i / z i * log (x i / z i)) =
      (∑ i ∈ s, x i * log (x i / z i)) / Z := by
    rw [sum_div]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [smul_eq_mul, div_mul_eq_mul_div, ← mul_assoc, hzx i hi]
  rw [h_pt, h_val, le_div_iff₀ hZ] at h
  have hZ' : Z ≠ 0 := hZ.ne'
  calc X * log (X / Z) = X / Z * log (X / Z) * Z := by field_simp
    _ ≤ _ := h

end Real
