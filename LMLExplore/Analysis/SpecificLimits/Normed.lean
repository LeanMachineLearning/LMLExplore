/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Geometric-type series

Mathlib computes the sum of the series `∑ n, n * r ^ n` for `‖r‖ < 1`
(`hasSum_coe_mul_geometric_of_norm_lt_one`). We record the resulting bound on its partial sums
for a nonnegative real ratio. We also sum the series `∑ n, r ^ (n / m)`, in which each power of
`r` is repeated `m` times: it bounds sums of quantities that decay geometrically along blocks of
length `m`, such as the Dobrushin coefficients `δ(κ ^ n) ≤ δ(κ ^ m) ^ (n / m)`.

## Main statements

* `LMLExplore.sum_range_natCast_mul_pow_le`: for `0 ≤ r < 1`,
  `∑ j ∈ range n, j * r ^ j ≤ r / (1 - r) ^ 2`.
* `LMLExplore.hasSum_pow_div_of_lt_one`: for `0 ≤ r < 1` and `m ≠ 0`,
  `∑ n, r ^ (n / m) = m / (1 - r)`.
* `LMLExplore.summable_pow_of_tendsto_pow_atTop_nhds_zero`: in a complete normed ring, the
  geometric series `∑ n, a ^ n` converges when the powers of `a` tend to `0`.
* `LMLExplore.tsum_neg_pow_smul_pow_succ`: in a normed algebra with summable geometric series,
  `∑ n, (-u) ^ n • a ^ (n + 1) = a * (1 + u • a)⁻¹` for `‖u‖ * ‖a‖ < 1`.
-/

public section

open Filter Finset Topology
open scoped Ring

namespace LMLExplore

/-- The partial sums of the series `∑ j, j * r ^ j` are at most `r / (1 - r) ^ 2` for
`0 ≤ r < 1`. -/
lemma sum_range_natCast_mul_pow_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ range n, (j * r ^ j : ℝ) ≤ r / (1 - r) ^ 2 :=
  sum_le_hasSum (range n) (fun j _ ↦ by positivity)
    (hasSum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hr0]))

/-- `∑ n, r ^ (n / m) = m / (1 - r)` for `0 ≤ r < 1` and `m ≠ 0`: each power `r ^ k` appears `m`
times. -/
theorem hasSum_pow_div_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m : ℕ} [NeZero m] :
    HasSum (fun n ↦ r ^ (n / m)) (m / (1 - r)) := by
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have hfin : HasSum (fun _ : Fin m ↦ (1 : ℝ)) m := by
    simpa using hasSum_fintype (fun _ : Fin m ↦ (1 : ℝ))
  have hs : Summable fun k : ℕ ↦ ‖r ^ k‖ := by
    simpa [norm_pow, Real.norm_of_nonneg hr0] using hgeom.summable
  have hprod : HasSum (fun p : ℕ × Fin m ↦ r ^ p.1 * 1) ((1 - r)⁻¹ * m) :=
    hgeom.mul hfin (summable_mul_of_summable_norm (f := fun k : ℕ ↦ r ^ k)
      (g := fun _ : Fin m ↦ (1 : ℝ)) hs .of_finite)
  -- reindex by `n ↦ (n / m, n % m)`
  have he (p : ℕ × Fin m) : r ^ p.1 * 1 = (fun n ↦ r ^ (n / m)) ((Nat.divModEquiv m).symm p) := by
    simp only [Nat.divModEquiv_symm_apply, mul_one]
    rw [add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_neZero m), Nat.div_eq_of_lt p.2.isLt,
      zero_add]
  rw [div_eq_inv_mul]
  exact (Nat.divModEquiv m).symm.hasSum_iff.1 (hprod.congr_fun fun p ↦ (he p).symm)

/-- In a complete normed ring, the geometric series `∑ n, a ^ n` converges as soon as the powers
of `a` tend to `0`, even if `‖a‖ ≥ 1`: some power `a ^ m` has norm `ρ < 1`, and then
`‖a ^ n‖ ≤ ρ ^ (n / m) * ∑ r < m, ‖a ^ r‖`. -/
theorem summable_pow_of_tendsto_pow_atTop_nhds_zero {R : Type*} [NormedRing R] [CompleteSpace R]
    {a : R} (h : Tendsto (fun n ↦ a ^ n) atTop (𝓝 0)) : Summable fun n ↦ a ^ n := by
  obtain ⟨m, hm, hm₁⟩ := ((tendsto_norm_zero.comp h).eventually
    (gt_mem_nhds zero_lt_one)).and (eventually_ge_atTop 1) |>.exists
  have : NeZero m := ⟨by omega⟩
  refine .of_norm_bounded (((hasSum_pow_div_of_lt_one (m := m) (norm_nonneg _) hm).summable
    ).mul_right (∑ r ∈ range m, ‖a ^ r‖)) fun n ↦ ?_
  have hr : ‖a ^ (n % m)‖ ≤ ∑ r ∈ range m, ‖a ^ r‖ :=
    single_le_sum (fun r _ ↦ norm_nonneg (a ^ r)) (mem_range.2 (Nat.mod_lt n (by omega)))
  conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul]
  rcases (n / m).eq_zero_or_pos with h0 | h0
  · rw [h0, pow_zero, pow_zero, one_mul, one_mul]
    exact hr
  · exact (norm_mul_le _ _).trans
      (mul_le_mul (norm_pow_le' _ h0) hr (norm_nonneg _) (by positivity))

/-- In a normed algebra with summable geometric series, `a` times the Neumann series of
`(1 + u • a)⁻¹` is `∑ n, (-u) ^ n • a ^ (n + 1) = a * (1 + u • a)⁻¹` for `‖u‖ * ‖a‖ < 1`. -/
theorem tsum_neg_pow_smul_pow_succ {𝕜 R : Type*} [NormedField 𝕜] [NormedRing R]
    [NormedAlgebra 𝕜 R] [HasSummableGeomSeries R] {a : R} {u : 𝕜} (h : ‖u‖ * ‖a‖ < 1) :
    ∑' n : ℕ, (-u) ^ n • a ^ (n + 1) = a * (1 + u • a)⁻¹ʳ := by
  have hx : ‖-(u • a)‖ < 1 := by
    rw [norm_neg]
    exact (norm_smul_le u a).trans_lt h
  rw [← sub_neg_eq_add, ← geom_series_eq_inverse _ hx,
    ← (summable_geometric_of_norm_lt_one hx).tsum_mul_left]
  congr 1
  ext1 n
  rw [← neg_smul, smul_pow, mul_smul_comm, pow_succ']

end LMLExplore
