/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.Subgradient
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The distance to a convex set

For a set `V` of a real normed space `E`, the distance `x ↦ Metric.infDist x V` to `V` is
`1`-Lipschitz (`Metric.lipschitz_infDist_pt`) and, for nonempty `V`, vanishes exactly on the
closure of `V` (`Metric.mem_closure_iff_infDist_zero`). This file adds its convex-analytic
properties for a convex `V` [Ora, Definition 12.1, Lemma 12.2, Example 12.3]: it is convex, it has
a subgradient at every point, and its subgradients at `x` are supporting functionals of `V` that
separate `x` from `V` by the distance. In particular, every subgradient `q` at `x` satisfies
`q (x - p) = ‖x - p‖` for a nearest point `p` of the closure of `V` to `x` (which exists in finite
dimension, `IsClosed.exists_infDist_eq_dist`).

These are the facts used to turn a constrained online learning problem on `V` into an
unconstrained one, through surrogate losses built from `‖y‖ * infDist · V` and a subgradient of
`infDist · V` at the unconstrained play [Ora, Section 12.1].

## Main statements

* `Convex.convexOn_infDist`: the distance to a convex set is convex.
* `Convex.exists_hasSubgradientWithinAt_infDist`: it has a subgradient at every point.
* `LMLExplore.hasSubgradientWithinAt_zero_infDist`: `0` is a subgradient at the points of the
  closure.
* `HasSubgradientWithinAt.infDist_le_apply_sub`: a subgradient `q` at `x` satisfies
  `infDist x V ≤ q (x - v)` for every `v` in the closure of `V`.
* `HasSubgradientWithinAt.apply_sub_eq_norm_of_infDist_eq`: a subgradient `q` at `x` satisfies
  `q (x - p) = ‖x - p‖` at a nearest point `p` of the closure of `V`. With
  `Convex.exists_hasSubgradientWithinAt_infDist`, the distance to a convex `V` has, at every point
  `x` with a nearest point `p`, a subgradient `q` with `q (x - p) = ‖x - p‖`.

## References

* [Ora] F. Orabona, *Online Learning: A Modern Introduction Using Convex Optimization*,
  arXiv:1912.13213v10, Section 12.1.
-/

public section

open Set Metric

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {V s : Set E} {x p v : E}
  {q : E →L[ℝ] ℝ}

/-- The distance to a convex set is a convex function. -/
theorem Convex.convexOn_infDist (hV : Convex ℝ V) : ConvexOn ℝ univ (infDist · V) := by
  rcases V.eq_empty_or_nonempty with rfl | hne
  · simpa only [infDist_empty] using convexOn_const (0 : ℝ) convex_univ
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  -- Compare with convex combinations of almost nearest points of `V` to `x` and to `y`.
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨v, hv, hxv⟩ := (infDist_lt_iff hne).1 (lt_add_of_pos_right (infDist x V) hε)
  obtain ⟨w, hw, hyw⟩ := (infDist_lt_iff hne).1 (lt_add_of_pos_right (infDist y V) hε)
  calc infDist (a • x + b • y) V ≤ ‖a • (x - v) + b • (y - w)‖ := by
        rw [smul_sub, smul_sub, sub_add_sub_comm, ← dist_eq_norm]
        exact infDist_le_dist_of_mem (hV hv hw ha hb hab)
    _ ≤ a * ‖x - v‖ + b * ‖y - w‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * (infDist x V + ε) + b * (infDist y V + ε) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        gcongr
    _ = a * infDist x V + b * infDist y V + ε := by linear_combination ε * hab

/-- The distance to a convex set has a subgradient at every point. -/
theorem Convex.exists_hasSubgradientWithinAt_infDist (hV : Convex ℝ V) (x : E) :
    ∃ q : E →L[ℝ] ℝ, HasSubgradientWithinAt (infDist · V) q univ x :=
  hV.convexOn_infDist.exists_hasSubgradientWithinAt_univ (continuous_infDist_pt V) x

namespace LMLExplore

/-- At a point of the closure of `V`, the zero functional is a subgradient of the distance to `V`,
which is minimal there. -/
theorem hasSubgradientWithinAt_zero_infDist (hx : x ∈ closure V) :
    HasSubgradientWithinAt (infDist · V) (0 : E →L[ℝ] ℝ) s x :=
  hasSubgradientWithinAt_iff_le.2 fun _ _ ↦ by
    simpa [infDist_zero_of_mem_closure hx] using infDist_nonneg

end LMLExplore

/-- A subgradient `q` of the distance to `V` at `x` separates `x` from `V` by the distance:
`infDist x V ≤ q (x - v)` for every point `v` of the closure of `V`. -/
theorem HasSubgradientWithinAt.infDist_le_apply_sub
    (hq : HasSubgradientWithinAt (infDist · V) q s x) (hvs : v ∈ s) (hv : v ∈ closure V) :
    infDist x V ≤ q (x - v) := by
  have := hasSubgradientWithinAt_iff_le.1 hq v hvs
  rw [infDist_zero_of_mem_closure hv, ← neg_sub x v, map_neg] at this
  linarith

/-- A subgradient `q` of the distance to `V` at `x` attains the norm on the direction of a nearest
point: if `p` is a point of the closure of `V` with `infDist x V = dist x p`, then
`q (x - p) = ‖x - p‖`. -/
theorem HasSubgradientWithinAt.apply_sub_eq_norm_of_infDist_eq
    (hq : HasSubgradientWithinAt (infDist · V) q univ x) (hp : p ∈ closure V)
    (hpx : infDist x V = dist x p) : q (x - p) = ‖x - p‖ := by
  rw [dist_eq_norm] at hpx
  refine le_antisymm ?_ (hpx ▸ hq.infDist_le_apply_sub (mem_univ p) hp)
  -- Compare with the point `x + (x - p)`, at distance at most `2 * ‖x - p‖` from `V`.
  have hle := hasSubgradientWithinAt_iff_le.1 hq (x + (x - p)) (mem_univ _)
  have h2 : x + (x - p) - p = (2 : ℝ) • (x - p) := by module
  have hdist : infDist (x + (x - p)) V ≤ 2 * ‖x - p‖ := by
    calc infDist (x + (x - p)) V ≤ infDist p V + dist (x + (x - p)) p :=
          infDist_le_infDist_add_dist
      _ = 2 * ‖x - p‖ := by
          rw [infDist_zero_of_mem_closure hp, zero_add, dist_eq_norm, h2, norm_smul,
            Real.norm_two]
  rw [add_sub_cancel_left, hpx] at hle
  linarith
