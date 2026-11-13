/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Convex.Topology

/-!
# Segments from an interior point of a convex set

For a convex set `s` in a topological vector space, the points `x + t (y - x)`, `0 ≤ t < 1`, of
the segment from an interior point `x` to a point `y` of the closure of `s` are interior. This is
Mathlib's `Convex.add_smul_sub_mem_interior'` read from the interior endpoint, in the
parametrization used along segments starting at an interior point.

## Main statements

* `Convex.add_smul_sub_mem_interior_of_mem_closure`: if `x ∈ interior s` and `y ∈ closure s`,
  then `x + t • (y - x) ∈ interior s` for `0 ≤ t < 1`.
-/

public section

open Set

namespace Convex

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E] {s : Set E} {x y : E} {t : 𝕜}

/-- If `x ∈ interior s` and `y ∈ closure s` for a convex set `s`, then the segment `[x, y)` is
included in `interior s`: `x + t • (y - x) ∈ interior s` for `0 ≤ t < 1`. -/
theorem add_smul_sub_mem_interior_of_mem_closure (hs : Convex 𝕜 s) (hx : x ∈ interior s)
    (hy : y ∈ closure s) (ht₀ : 0 ≤ t) (ht₁ : t < 1) : x + t • (y - x) ∈ interior s := by
  convert hs.add_smul_sub_mem_interior' hy hx ⟨sub_pos.2 ht₁, sub_le_self 1 ht₀⟩ using 1
  module

end Convex
