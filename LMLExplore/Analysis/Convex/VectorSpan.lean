/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# The vector span of a convex set

The vector span of a set `s` (the direction of its affine span) is the submodule spanned by the
differences `a - b` of points of `s`. When `s` is convex, no linear combinations are needed: every
vector of the span is a nonnegative multiple `t • (a - b)` of a single difference. Indeed the set
of these multiples is closed under addition, since
`t₁ • (a₁ - b₁) + t₂ • (a₂ - b₂) = (t₁ + t₂) • (a - b)` for the convex combinations
`a = (t₁ • a₁ + t₂ • a₂) / (t₁ + t₂)` and `b = (t₁ • b₁ + t₂ • b₂) / (t₁ + t₂)` of points of `s`.

A positively homogeneous condition of degree two, such as the nonnegativity of a quadratic form,
therefore holds on the whole direction of the affine span of a convex set as soon as it holds on
the differences of its points. This is how second-order conditions on sets with empty interior
are stated.

## Main statements

* `Convex.exists_eq_smul_sub_of_mem_vectorSpan`: a vector of the vector span of a nonempty convex
  set `s` is `t • (a - b)` for some `t ≥ 0` and `a, b ∈ s`.
-/

public section

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {s : Set E}

/-- A vector of the vector span of a nonempty convex set `s` is a nonnegative multiple
`t • (a - b)` of the difference of two points `a, b ∈ s`. -/
theorem Convex.exists_eq_smul_sub_of_mem_vectorSpan (hs : Convex 𝕜 s) (hne : s.Nonempty) {v : E}
    (hv : v ∈ vectorSpan 𝕜 s) : ∃ t : 𝕜, 0 ≤ t ∧ ∃ a ∈ s, ∃ b ∈ s, v = t • (a - b) := by
  obtain ⟨x, hx⟩ := hne
  rw [vectorSpan_def] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    exact ⟨1, zero_le_one, a, ha, b, hb, by simp [vsub_eq_sub]⟩
  | zero => exact ⟨0, le_rfl, x, hx, x, hx, by rw [zero_smul]⟩
  | add v w _ _ hv hw =>
    obtain ⟨t₁, ht₁, a₁, ha₁, b₁, hb₁, rfl⟩ := hv
    obtain ⟨t₂, ht₂, a₂, ha₂, b₂, hb₂, rfl⟩ := hw
    rcases (add_nonneg ht₁ ht₂).eq_or_lt with h | h
    · obtain rfl : t₁ = 0 := by linarith
      obtain rfl : t₂ = 0 := by linarith
      exact ⟨0, le_rfl, x, hx, x, hx, by simp⟩
    · have hsum : t₁ / (t₁ + t₂) + t₂ / (t₁ + t₂) = 1 := by field_simp
      refine ⟨t₁ + t₂, h.le, (t₁ / (t₁ + t₂)) • a₁ + (t₂ / (t₁ + t₂)) • a₂,
        hs ha₁ ha₂ (by positivity) (by positivity) hsum,
        (t₁ / (t₁ + t₂)) • b₁ + (t₂ / (t₁ + t₂)) • b₂,
        hs hb₁ hb₂ (by positivity) (by positivity) hsum, ?_⟩
      match_scalars <;> field_simp
  | smul c v _ hv =>
    obtain ⟨t, ht, a, ha, b, hb, rfl⟩ := hv
    rcases le_total 0 c with hc | hc
    · exact ⟨c * t, mul_nonneg hc ht, a, ha, b, hb, by rw [smul_smul]⟩
    · refine ⟨-c * t, mul_nonneg (neg_nonneg.2 hc) ht, b, hb, a, ha, ?_⟩
      rw [smul_smul, ← neg_sub a b, smul_neg, neg_mul, neg_smul, neg_neg]
