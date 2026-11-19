/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.MeanInequalities

/-!
# The inequality of arithmetic and geometric means, product form, and two-term Hölder

Mathlib states the AM-GM inequality with real powers, as
`(∏ i ∈ s, z i ^ w i) ^ (∑ i ∈ s, w i)⁻¹ ≤ (∑ i ∈ s, w i * z i) / ∑ i ∈ s, w i`
(`Real.geom_mean_le_arith_mean`). We record its unweighted form with natural powers, as a bound
on a product by a power of the average.

We also record Hölder's inequality for two terms in the form of the superadditivity of the
weighted geometric mean `(a, b) ↦ a ^ p * b ^ q`, `p + q = 1`, on the nonnegative quadrant. Being
also positively homogeneous, this mean is concave, which is what makes products of powers of
nonnegative concave functions concave.

## Main statements

* `Real.prod_le_sum_div_card_pow`: for `z ≥ 0` on `s`,
  `∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / #s) ^ #s`.
* `Real.rpow_mul_rpow_add_rpow_mul_rpow_le`: for nonnegative `a₁, a₂, b₁, b₂` and `p, q ≥ 0` with
  `p + q = 1`, `a₁ ^ p * b₁ ^ q + a₂ ^ p * b₂ ^ q ≤ (a₁ + a₂) ^ p * (b₁ + b₂) ^ q`.
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

/-- **Hölder's inequality for two terms**, with exponents `p, q ≥ 0` summing to `1`: the weighted
geometric mean `(a, b) ↦ a ^ p * b ^ q` is superadditive on the nonnegative quadrant,
`a₁ ^ p * b₁ ^ q + a₂ ^ p * b₂ ^ q ≤ (a₁ + a₂) ^ p * (b₁ + b₂) ^ q`. -/
theorem rpow_mul_rpow_add_rpow_mul_rpow_le {a₁ a₂ b₁ b₂ p q : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    a₁ ^ p * b₁ ^ q + a₂ ^ p * b₂ ^ q ≤ (a₁ + a₂) ^ p * (b₁ + b₂) ^ q := by
  rcases hp.eq_or_lt with rfl | hp
  · obtain rfl : q = 1 := by linarith
    simp
  rcases hq.eq_or_lt with rfl | hq
  · obtain rfl : p = 1 := by linarith
    simp
  -- Hölder's inequality for the exponents `p⁻¹` and `q⁻¹` and the families `aᵢ ^ p`, `bᵢ ^ q`
  have h := inner_le_Lp_mul_Lq_of_nonneg (s := univ) (f := ![a₁ ^ p, a₂ ^ p])
    (g := ![b₁ ^ q, b₂ ^ q]) (HolderConjugate.inv_inv hp hq hpq)
    (by simp [Fin.forall_fin_two, rpow_nonneg, ha₁, ha₂])
    (by simp [Fin.forall_fin_two, rpow_nonneg, hb₁, hb₂])
  simpa [Fin.sum_univ_two, rpow_rpow_inv, ha₁, ha₂, hb₁, hb₂, hp.ne', hq.ne'] using h

end Real
