/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# Supports of convex combinations of finitely supported probability measures

Mathlib's `Convexity.StdSimplex R X` is the type of finitely supported probability measures on
`X`, and `Convexity.convexCombPair s t _ _ _ w w'` is the convex combination `s • w + t • w'` of
two of them (`Convexity.StdSimplex.weights_convexCombPair`). Its support is contained in the union
of the supports of `w` and `w'`: the measures supported in a set `𝒜` form a convex subset of
`StdSimplex R X`. This is what makes the designs on a set of vectors, and their design operators,
a convex set.

## Main statements

* `Convexity.StdSimplex.support_weights_convexCombPair_subset`: the support of a convex combination
  of two finitely supported probability measures is contained in the union of their supports.
-/

public section

namespace Convexity.StdSimplex

variable {R X : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]

/-- The support of a convex combination of two finitely supported probability measures is
contained in the union of their supports. -/
theorem support_weights_convexCombPair_subset (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) (w w' : StdSimplex R X) :
    ((convexCombPair s t hs ht hst w w').weights.support : Set X) ⊆
      ↑w.weights.support ∪ ↑w'.weights.support := by
  classical
  intro a ha
  rw [weights_convexCombPair, Finset.mem_coe] at ha
  rcases Finset.mem_union.1 (Finsupp.support_add ha) with h | h
  exacts [Or.inl (Finsupp.support_smul h), Or.inr (Finsupp.support_smul h)]

end Convexity.StdSimplex
