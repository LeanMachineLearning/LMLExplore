/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# The inequality of arithmetic and geometric means, product form

Mathlib states the AM-GM inequality with real powers, as
`(∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ ≤ (∑ i ∈ s, w i * z i) / ∑ i ∈ s, w i`
(`Real.geom_mean_le_arith_mean`). We record its unweighted form with natural powers, as a bound
on a product by a power of the average.

## Main statements

* `Real.prod_le_sum_div_card_pow`: for `z ≥ 0` on `s`,
  `∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / #s) ^ #s`.
-/

public section

open Finset

namespace Real

/-- **AM-GM inequality**, product form: for `z ≥ 0` on `s`,
`∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / #s) ^ #s`. -/
theorem prod_le_sum_div_card_pow {ι : Type*} (s : Finset ι) {z : ι → ℝ}
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / #s) ^ #s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hcard : (0 : ℝ) < #s := by exact_mod_cast hs.card_pos
  have h := Real.geom_mean_le_arith_mean s (fun _ ↦ 1) z (fun _ _ ↦ zero_le_one)
    (by simpa using hcard) hz
  simp only [Real.rpow_one, sum_const, nsmul_eq_mul, mul_one, one_mul] at h
  have hprod : 0 ≤ ∏ i ∈ s, z i := prod_nonneg hz
  calc ∏ i ∈ s, z i = ((∏ i ∈ s, z i) ^ ((#s : ℝ)⁻¹)) ^ #s :=
        (Real.rpow_inv_natCast_pow hprod hs.card_pos.ne').symm
    _ ≤ ((∑ i ∈ s, z i) / #s) ^ #s := by gcongr

end Real
