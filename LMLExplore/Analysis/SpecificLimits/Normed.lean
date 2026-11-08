/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
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
-/

public section

open Finset

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

end LMLExplore
