/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Affinely independent points on a hyperplane

Affine independence is weaker than linear independence: in a module of dimension `D`, a family of
`D + 1` points can be affinely independent, but not linearly independent. The two notions agree
for points on an affine hyperplane that does not pass through the origin, the level set
`{x | f x = c}` of a linear form `f` at a level `c ≠ 0`. Combined with Carathéodory's theorem, this
bounds by `D` rather than `D + 1` the number of points needed to write a point of the convex hull
of a subset of such a hyperplane as a convex combination; this is the bound on the support of
optimal designs in the Kiefer–Wolfowitz theorem.

## Main statements

* `AffineIndependent.linearIndependent_of_forall_apply_eq`: affinely independent points on the
  hyperplane `{x | f x = c}` with `c ≠ 0` are linearly independent.
-/

public section

open Finset

variable {k V ι : Type*} [Ring k] [NoZeroDivisors k] [AddCommGroup V] [Module k V]

/-- Affinely independent points `p i` on an affine hyperplane `{x | f x = c}` that does not pass
through the origin (`c ≠ 0`) are linearly independent. -/
theorem AffineIndependent.linearIndependent_of_forall_apply_eq {p : ι → V}
    (hp : AffineIndependent k p) (f : V →ₗ[k] k) {c : k} (hc : c ≠ 0) (hf : ∀ i, f (p i) = c) :
    LinearIndependent k p := by
  rw [linearIndependent_iff']
  intro s g hg
  -- applying `f` to the linear relation shows that its coefficients sum to zero
  have hsum : ∑ i ∈ s, g i = 0 := by
    have h := congrArg f hg
    simp only [map_sum, map_smul, hf, smul_eq_mul, map_zero, ← sum_mul] at h
    exact (mul_eq_zero.1 h).resolve_right hc
  exact hp s g hsum (by rw [s.weightedVSub_eq_linear_combination hsum, hg])
