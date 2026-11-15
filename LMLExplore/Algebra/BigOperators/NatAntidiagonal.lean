/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Geometric sums over an antidiagonal

The sum of `a ^ i * b ^ j` over the pairs `(i, j)` with `i + j = n` is the two-variable geometric
sum of Mathlib's `geom_sum₂_mul`: multiplied by `a - b`, it is `a ^ (n + 1) - b ^ (n + 1)`.

## Main statements

* `Finset.Nat.sum_antidiagonal_pow_mul_pow_mul_sub`:
  `(∑ x ∈ antidiagonal n, a ^ x.1 * b ^ x.2) * (a - b) = a ^ (n + 1) - b ^ (n + 1)`.
-/

public section

namespace Finset.Nat

/-- **The geometric sum over an antidiagonal**, a form of `geom_sum₂_mul`:
`(∑ i + j = n, a ^ i * b ^ j) * (a - b) = a ^ (n + 1) - b ^ (n + 1)`. -/
theorem sum_antidiagonal_pow_mul_pow_mul_sub {R : Type*} [CommRing R] (a b : R) (n : ℕ) :
    (∑ x ∈ antidiagonal n, a ^ x.1 * b ^ x.2) * (a - b) = a ^ (n + 1) - b ^ (n + 1) := by
  rw [sum_antidiagonal_eq_sum_range_succ_mk, ← geom_sum₂_mul]
  simp

end Finset.Nat
