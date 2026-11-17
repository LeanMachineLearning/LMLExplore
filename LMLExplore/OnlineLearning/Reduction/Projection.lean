/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.InfDist
public import LMLExplore.Analysis.InnerProductSpace.Dual
public import LMLExplore.Analysis.Normed.Operator.Basic
public import LMLExplore.OnlineLearning.Learner.Operations
public import LMLExplore.OnlineLearning.SubgradientDescent

/-!
# Constrained online learning through projections

An online learner `A` with plays in a set `W` of a real normed space `E` can be turned into a
learner with plays in a nonempty convex set `V ⊆ W` [CO18], [Ora, Section 12.1, Algorithm 12.1]. At
each round, `A` plays `z t`, the reduction plays a nearest point `x t` of `V` to `z t`, so that
`‖x t - z t‖ = infDist (z t) V`, it suffers the loss `ℓ t (x t)` with a subgradient `y t` within `V`
at `x t`, and it feeds `A` a *surrogate loss*. With a subgradient `q t` of the distance
`infDist · V` at `z t`, the four surrogates of [Ora, Theorem 12.5] are
`w ↦ y t w + a t * infDist w V` (`penalizedLoss V (y t) (a t)`) and its linearization
`y t + a t • q t` at `z t`, for two choices of the weight `a t` of the distance:

* `a t = ‖y t‖`, the first surrogate [CO18] and its linearization, the second;
* `a t = surrogateCoeff (y t) (x t) (z t) = max (y t (x t - z t)) 0 / ‖x t - z t‖`, the third
  surrogate [Cut20] and its linearization, the fourth. The weight vanishes unless the projection
  increases the loss.

For each of them, the loss `y t (x t - u)` of the projected play relative to every `u ∈ V` is at
most the surrogate loss of `z t` relative to `u` (`apply_sub_le_penalizedLoss_sub`,
`apply_sub_le_add_smul_apply_sub` and their instances). Summed over the rounds, the regret of the
plays `x t` against `u ∈ V` for convex losses is at most the regret of the plays `z t` of `A` for
the surrogate losses (`regret_le_regret_penalizedLoss`,
`regret_le_regret_add_smul`). The surrogates have subgradients of dual norm at most `2 ‖y t‖`, and
in an inner product space the subgradients of the third surrogate and the fourth surrogate have
dual norm at most `‖y t‖` [Ora, Remark 12.6]
(`HasSubgradientWithinAt.norm_le_of_penalizedLoss_surrogateCoeff`,
`norm_add_surrogateCoeff_smul_le_norm`). So a guarantee of `A` for losses of dual norm at most
`2 L` transfers to the reduction for losses of dual norm at most `L`
(`OnlineLearner.HasRegretBound.constrain_of_norm_le`), and in an inner product space a guarantee
of `A` for losses of dual norm at most `L` transfers for the same `L`
(`OnlineLearner.HasRegretBound.constrain_of_norm_le_of_inner`).

The learner `A.constrain p q` runs the reduction with the fourth surrogate
`constrainSurrogate p q z y`, for a choice `p z` of nearest points of `V` and `q z` of subgradients
of the distance (both exist when `V` is closed and `E` is finite-dimensional, by
`IsClosed.exists_infDist_eq_dist` and `Convex.exists_hasSubgradientWithinAt_infDist`). It is the
black-box reduction `OnlineLearner.reduce`. When the `p z` are nearest points, the `q z` are
subgradients of the distance and the surrogates of the admissible losses are admissible for `A`, a
regret bound `B` of `A` against the comparators of `V` transfers to `A.constrain p q`, with `B`
evaluated at the surrogate losses fed to `A` (`OnlineLearner.HasRegretBound.constrain`). In
dimension one,
clipping a learner on `ℝ` to `[0, ∞)` plays `max (z t) 0` and feeds `A` the surrogate loss
`min (g t) 0` when `z t < 0` and `g t` otherwise [Ora, Example 12.9]
(`OnlineLearner.clipNonneg`, `OnlineLearner.HasRegretBound.clipNonneg`).

## Main definitions

* `LMLExplore.OnlineLearning.penalizedLoss V y a`: the loss `w ↦ y w + a * infDist w V`.
* `LMLExplore.OnlineLearning.surrogateCoeff y x z`: the weight `max (y (x - z)) 0 / ‖x - z‖`.
* `LMLExplore.OnlineLearning.constrainSurrogate p q z y`: the fourth surrogate for the projection
  `p z` of the play `z`.
* `LMLExplore.OnlineLearning.OnlineLearner.constrain A p q`: the learner `A` constrained to `V` by
  the projection `p`, fed the fourth surrogate.
* `LMLExplore.OnlineLearning.OnlineLearner.clipNonneg A`: a learner on `ℝ` clipped to `[0, ∞)`.

## Main statements

* `regret_le_regret_penalizedLoss`, `regret_le_regret_add_smul` [Ora, Theorem 12.5]: the regret of
  the projected plays is at most the regret of the unconstrained plays for the surrogate losses.
* `HasSubgradientWithinAt.norm_le_of_penalizedLoss`, `norm_add_smul_le_two_mul`,
  `norm_add_norm_smul_le`, `norm_add_surrogateCoeff_smul_le` [Ora, Theorem 12.5]: the subgradients
  of the surrogates have dual norm at most `‖y‖ + a`, hence at most `2 ‖y‖` for both weights.
* `HasSubgradientWithinAt.norm_le_of_penalizedLoss_surrogateCoeff`,
  `norm_add_surrogateCoeff_smul_le_norm` [Ora, Remark 12.6]: in an inner product space, the
  subgradients of the third surrogate and the fourth surrogate have dual norm at most `‖y‖`.
* `OnlineLearner.HasRegretBound.constrain`, `OnlineLearner.HasRegretBound.constrain_of_norm_le`,
  `OnlineLearner.HasRegretBound.constrain_of_norm_le_of_inner`: regret guarantees of the
  constrained learner.
* `OnlineLearner.HasRegretBound.clipNonneg` [Ora, Example 12.9]: the regret guarantee of a clipped
  one-dimensional learner.

## References

* [CO18] A. Cutkosky and F. Orabona, *Black-box reductions for parameter-free online learning in
  Banach spaces*, COLT 2018.
* [Cut20] A. Cutkosky, *Parameter-free, dynamic, and strongly-adaptive online learning*, ICML 2020.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Section 12.1.
-/

public section

open Finset Set Metric Topology
open scoped RealInnerProductSpace

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V s : Set E}
  {y q g : E →L[ℝ] ℝ} {a : ℝ} {x z u w : E} {n : ℕ}

section Surrogate

/-- The loss `y` penalized by `a` times the distance to `V`: `w ↦ y w + a * infDist w V`. With
`a = ‖y‖` or `a = surrogateCoeff y x z`, it is the first or the third surrogate loss of
[Ora, Theorem 12.5] for the projection `x` of the play `z` onto `V`. -/
noncomputable def penalizedLoss (V : Set E) (y : E →L[ℝ] ℝ) (a : ℝ) (w : E) : ℝ :=
  y w + a * infDist w V

lemma penalizedLoss_def (V : Set E) (y : E →L[ℝ] ℝ) (a : ℝ) (w : E) :
    penalizedLoss V y a w = y w + a * infDist w V := (rfl)

/-- On the closure of `V`, the penalized loss is the loss. -/
lemma penalizedLoss_of_mem_closure (hw : w ∈ closure V) : penalizedLoss V y a w = y w := by
  rw [penalizedLoss_def, infDist_zero_of_mem_closure hw, mul_zero, add_zero]

/-- On `V`, the penalized loss is the loss. -/
lemma penalizedLoss_of_mem (hw : w ∈ V) : penalizedLoss V y a w = y w :=
  penalizedLoss_of_mem_closure (subset_closure hw)

/-- The weight of the distance in the third and fourth surrogate losses of [Ora, Theorem 12.5],
for the projection `x` of the play `z`: the positive part of the increase `y (x - z)` of the loss
from `z` to `x`, per unit of the distance `‖x - z‖`. It is `y ((x - z) / ‖x - z‖)` when this is
positive, and `0` otherwise. -/
noncomputable def surrogateCoeff (y : E →L[ℝ] ℝ) (x z : E) : ℝ :=
  max (y (x - z)) 0 / ‖x - z‖

lemma surrogateCoeff_def (y : E →L[ℝ] ℝ) (x z : E) :
    surrogateCoeff y x z = max (y (x - z)) 0 / ‖x - z‖ := (rfl)

lemma surrogateCoeff_nonneg : 0 ≤ surrogateCoeff y x z :=
  div_nonneg (le_max_right _ _) (norm_nonneg _)

/-- The weight vanishes when the projection does not increase the loss. -/
lemma surrogateCoeff_eq_zero_of_apply_sub_nonpos (h : y (x - z) ≤ 0) :
    surrogateCoeff y x z = 0 := by
  rw [surrogateCoeff_def, max_eq_right h, zero_div]

@[simp]
lemma surrogateCoeff_self : surrogateCoeff y x x = 0 :=
  surrogateCoeff_eq_zero_of_apply_sub_nonpos (by simp)

/-- The weight times the distance from `z` to `x` is the positive part of `y (x - z)`. -/
lemma surrogateCoeff_mul_norm_sub : surrogateCoeff y x z * ‖x - z‖ = max (y (x - z)) 0 := by
  rcases eq_or_ne x z with rfl | hxz
  · simp
  rw [surrogateCoeff_def, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxz))]

/-- The weight is at most the dual norm of the loss. -/
lemma surrogateCoeff_le_norm : surrogateCoeff y x z ≤ ‖y‖ := by
  rw [surrogateCoeff_def]
  exact div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) (y.max_apply_zero_le_opNorm_mul_norm _)

/-- The penalized loss is convex for a convex `V` and a nonnegative weight. -/
theorem convexOn_penalizedLoss (hV : Convex ℝ V) (ha : 0 ≤ a) :
    ConvexOn ℝ univ (penalizedLoss V y a) := by
  have h := ((y : E →ₗ[ℝ] ℝ).convexOn convex_univ).add (hV.convexOn_infDist.smul ha)
  convert h using 1
  ext w
  simp [penalizedLoss_def]

/-- The linearized surrogate `y + a • q` is a subgradient of the penalized loss at `z`, for a
subgradient `q` of the distance to `V` at `z` and a nonnegative weight. -/
theorem hasSubgradientWithinAt_penalizedLoss
    (hq : HasSubgradientWithinAt (infDist · V) q s z) (ha : 0 ≤ a) :
    HasSubgradientWithinAt (penalizedLoss V y a) (y + a • q) s z := by
  have h := (hasSubgradientWithinAt_linear (s := s) (x := z) y).add (hq.smul ha)
  convert h using 1
  ext w
  simp [penalizedLoss_def]

/-- The penalized loss is `(‖y‖ + a)`-Lipschitz for a nonnegative weight. -/
lemma lipschitzWith_penalizedLoss (ha : 0 ≤ a) :
    LipschitzWith (‖y‖ + a).toNNReal (penalizedLoss V y a) := by
  convert y.lipschitzWith.add ((lipschitzWith_smul a).comp (lipschitz_infDist_pt V)) using 1
  · ext
    simp [Real.coe_toNNReal _ (by positivity : 0 ≤ ‖y‖ + a), abs_of_nonneg ha]
  · ext w
    simp [penalizedLoss_def]

/-- **The subgradients of the first and third surrogates are bounded** [Ora, Theorem 12.5]: every
subgradient of the penalized loss within a neighbourhood of a point has dual norm at most
`‖y‖ + a`, hence at most `2 ‖y‖` for the weights `‖y‖` and `surrogateCoeff y x z`. -/
theorem _root_.HasSubgradientWithinAt.norm_le_of_penalizedLoss
    (hg : HasSubgradientWithinAt (penalizedLoss V y a) g s w) (hs : s ∈ 𝓝 w) (ha : 0 ≤ a) :
    ‖g‖ ≤ ‖y‖ + a := by
  have h := hg.norm_le_of_lipschitzOnWith hs (lipschitzWith_penalizedLoss ha).lipschitzOnWith
  rwa [Real.coe_toNNReal _ (by positivity)] at h

/-- **The linearized surrogates are bounded** [Ora, Theorem 12.5]: for a weight `0 ≤ a ≤ ‖y‖` and
`‖q‖ ≤ 1`, as for the subgradients of the distance to `V`
(`HasSubgradientWithinAt.norm_le_one_of_infDist`), `‖y + a • q‖ ≤ 2 ‖y‖`. -/
theorem norm_add_smul_le_two_mul (ha₀ : 0 ≤ a) (ha : a ≤ ‖y‖) (hq : ‖q‖ ≤ 1) :
    ‖y + a • q‖ ≤ 2 * ‖y‖ := by
  calc ‖y + a • q‖ ≤ ‖y‖ + a * ‖q‖ := by
        simpa [norm_smul, abs_of_nonneg ha₀] using norm_add_le y (a • q)
    _ ≤ 2 * ‖y‖ := by nlinarith

/-- **The second surrogate is bounded** [Ora, Theorem 12.5]: for `‖q‖ ≤ 1`, as for the
subgradients of the distance to `V` (`HasSubgradientWithinAt.norm_le_one_of_infDist`),
`‖y + ‖y‖ • q‖ ≤ 2 ‖y‖`. -/
theorem norm_add_norm_smul_le (hq : ‖q‖ ≤ 1) : ‖y + ‖y‖ • q‖ ≤ 2 * ‖y‖ :=
  norm_add_smul_le_two_mul (norm_nonneg _) le_rfl hq

/-- **The fourth surrogate is bounded** [Ora, Theorem 12.5]: for `‖q‖ ≤ 1`, as for the
subgradients of the distance to `V`, `‖y + surrogateCoeff y x z • q‖ ≤ 2 ‖y‖`. -/
theorem norm_add_surrogateCoeff_smul_le (hq : ‖q‖ ≤ 1) :
    ‖y + surrogateCoeff y x z • q‖ ≤ 2 * ‖y‖ :=
  norm_add_smul_le_two_mul surrogateCoeff_nonneg surrogateCoeff_le_norm hq

end Surrogate

section Round

/-- **The surrogate inequality** [Ora, Theorem 12.5]. Let `x` be a nearest point of `V` to `z`, and
let the weight `a` dominate the positive part of the increase of the loss from `z` to `x`:
`max (y (x - z)) 0 ≤ a * ‖x - z‖`. Then for every `u` in the closure of `V`, the loss of `x`
relative to `u` is at most the penalized loss of `z` relative to `u`. -/
theorem apply_sub_le_penalizedLoss_sub (hx : infDist z V = dist z x)
    (ha : max (y (x - z)) 0 ≤ a * ‖x - z‖) (hu : u ∈ closure V) :
    y (x - u) ≤ penalizedLoss V y a z - penalizedLoss V y a u := by
  rw [penalizedLoss_of_mem_closure hu, penalizedLoss_def, hx, dist_comm, dist_eq_norm]
  have h : y (x - u) = y (z - u) + y (x - z) := by rw [← map_add]; congr 1; abel
  rw [h, map_sub]
  linarith [le_max_left (y (x - z)) 0]

/-- The surrogate inequality for the first surrogate `w ↦ y w + ‖y‖ * infDist w V`
[CO18, Ora, Theorem 12.5]. -/
theorem apply_sub_le_penalizedLoss_norm_sub (hx : infDist z V = dist z x) (hu : u ∈ closure V) :
    y (x - u) ≤ penalizedLoss V y ‖y‖ z - penalizedLoss V y ‖y‖ u :=
  apply_sub_le_penalizedLoss_sub hx (y.max_apply_zero_le_opNorm_mul_norm _) hu

/-- The surrogate inequality for the third surrogate
`w ↦ y w + surrogateCoeff y x z * infDist w V` [Cut20, Ora, Theorem 12.5]. -/
theorem apply_sub_le_penalizedLoss_surrogateCoeff_sub (hx : infDist z V = dist z x)
    (hu : u ∈ closure V) :
    y (x - u) ≤ penalizedLoss V y (surrogateCoeff y x z) z -
      penalizedLoss V y (surrogateCoeff y x z) u :=
  apply_sub_le_penalizedLoss_sub hx surrogateCoeff_mul_norm_sub.ge hu

/-- **The linearized surrogate inequality** [Ora, Theorem 12.5]. Under the hypotheses of
`apply_sub_le_penalizedLoss_sub`, with a nonnegative weight and a subgradient `q` of the distance
to `V` within `s` at `z`, the loss of `x` relative to `u ∈ s` is at most the linear loss
`y + a • q` of `z` relative to `u`. -/
theorem apply_sub_le_add_smul_apply_sub (hx : infDist z V = dist z x)
    (ha : max (y (x - z)) 0 ≤ a * ‖x - z‖) (ha₀ : 0 ≤ a)
    (hq : HasSubgradientWithinAt (infDist · V) q s z) (hus : u ∈ s) (hu : u ∈ closure V) :
    y (x - u) ≤ (y + a • q) (z - u) := by
  have h := hasSubgradientWithinAt_iff_le.mp
    (hasSubgradientWithinAt_penalizedLoss (y := y) hq ha₀) u hus
  linarith [apply_sub_le_penalizedLoss_sub hx ha hu, map_sub (y + a • q) u z,
    map_sub (y + a • q) z u]

/-- The surrogate inequality for the second surrogate `y + ‖y‖ • q` [Ora, Theorem 12.5]. -/
theorem apply_sub_le_add_norm_smul_apply_sub (hx : infDist z V = dist z x)
    (hq : HasSubgradientWithinAt (infDist · V) q s z) (hus : u ∈ s) (hu : u ∈ closure V) :
    y (x - u) ≤ (y + ‖y‖ • q) (z - u) :=
  apply_sub_le_add_smul_apply_sub hx (y.max_apply_zero_le_opNorm_mul_norm _) (norm_nonneg _) hq
    hus hu

/-- The surrogate inequality for the fourth surrogate `y + surrogateCoeff y x z • q`
[Ora, Theorem 12.5]. -/
theorem apply_sub_le_add_surrogateCoeff_smul_apply_sub (hx : infDist z V = dist z x)
    (hq : HasSubgradientWithinAt (infDist · V) q s z) (hus : u ∈ s) (hu : u ∈ closure V) :
    y (x - u) ≤ (y + surrogateCoeff y x z • q) (z - u) :=
  apply_sub_le_add_smul_apply_sub hx surrogateCoeff_mul_norm_sub.ge surrogateCoeff_nonneg hq hus hu

end Round

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {V : Set F}
  {y q : F →L[ℝ] ℝ} {x z : F}

/-- **The fourth surrogate is not larger than the loss in an inner product space**
[Ora, Remark 12.6]. If `x` is a nearest point of the closure of `V` to `z` and `q` is a subgradient
of the distance to `V` at `z` within `univ`, then `‖y + surrogateCoeff y x z • q‖ ≤ ‖y‖`. -/
theorem norm_add_surrogateCoeff_smul_le_norm (hq : HasSubgradientWithinAt (infDist · V) q univ z)
    (hx : x ∈ closure V) (hxz : infDist z V = dist z x) :
    ‖y + surrogateCoeff y x z • q‖ ≤ ‖y‖ := by
  rcases le_or_gt (y (x - z)) 0 with hyxz | hyxz
  · simp [surrogateCoeff_eq_zero_of_apply_sub_nonpos hyxz]
  have hzx : z - x ≠ 0 := fun h ↦ by simp [sub_eq_zero.mp h] at hyxz
  have hnorm : 0 < ‖z - x‖ := norm_pos_iff.mpr hzx
  -- `q` is the inner product with the unit vector `e` from `x` to `z`.
  set e := ‖z - x‖⁻¹ • (z - x) with he_def
  have he : ‖e‖ = 1 := by rw [he_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnorm.ne']
  have hqe : q e = 1 := by
    rw [he_def, map_smul, hq.apply_sub_eq_norm_of_infDist_eq hx hxz, smul_eq_mul,
      inv_mul_cancel₀ hnorm.ne']
  have hq_eq := ContinuousLinearMap.eq_innerSL_of_norm_le_one
    (hq.norm_le_one_of_infDist Filter.univ_mem) he hqe
  -- The weight is `-y e`, so the surrogate maps `v` to `y (v - ⟪e, v⟫ • e)`.
  have hcoeff : surrogateCoeff y x z = -y e := by
    rw [surrogateCoeff_def, max_eq_left hyxz.le, norm_sub_rev]
    simp [he_def, div_eq_inv_mul, ← mul_neg]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  have happ : (y + surrogateCoeff y x z • q) v = y (v - ⟪e, v⟫ • e) := by
    simp only [hcoeff, hq_eq, add_apply, smul_apply,
      innerSL_apply_apply, map_sub, map_smul, smul_eq_mul]
    ring
  -- The component of `v` orthogonal to `e` is not longer than `v`.
  rw [happ, ← Submodule.starProjection_unit_singleton ℝ he v,
    ← Submodule.starProjection_orthogonal_val]
  exact (y.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((ℝ ∙ e)ᗮ.norm_starProjection_apply_le v) (norm_nonneg _))

/-- **The third surrogate is not larger than the loss in an inner product space**
[Ora, Remark 12.6]. If `x` is a nearest point of the closure of `V` to `z`, then every subgradient
`g` within `univ` of the third surrogate `penalizedLoss V y (surrogateCoeff y x z)` at `z` has dual
norm at most `‖y‖`. -/
theorem _root_.HasSubgradientWithinAt.norm_le_of_penalizedLoss_surrogateCoeff {g : F →L[ℝ] ℝ}
    (hg : HasSubgradientWithinAt (penalizedLoss V y (surrogateCoeff y x z)) g univ z)
    (hx : x ∈ closure V) (hxz : infDist z V = dist z x) : ‖g‖ ≤ ‖y‖ := by
  -- If the weight vanishes, this is `HasSubgradientWithinAt.norm_le_of_penalizedLoss`. Otherwise
  -- `g` is a fourth surrogate, to which `norm_add_surrogateCoeff_smul_le_norm` applies.
  rcases (surrogateCoeff_nonneg (y := y) (x := x) (z := z)).eq_or_lt with ha | ha
  · have h := hg.norm_le_of_penalizedLoss Filter.univ_mem surrogateCoeff_nonneg
    rwa [← ha, add_zero] at h
  set a := surrogateCoeff y x z
  -- `a⁻¹ • (g - y)` is a subgradient of the distance to `V` at `z`.
  have hq : HasSubgradientWithinAt (infDist · V) (a⁻¹ • (g - y)) univ z := by
    refine hasSubgradientWithinAt_iff_le.2 fun w hw ↦ ?_
    have h := hasSubgradientWithinAt_iff_le.1 hg w hw
    rw [penalizedLoss_def, penalizedLoss_def] at h
    have h' : g (w - z) - y (w - z) ≤ a * (infDist w V - infDist z V) := by
      linarith [map_sub y w z]
    have h'' := mul_le_mul_of_nonneg_left h' (inv_nonneg.2 ha.le)
    rw [inv_mul_cancel_left₀ ha.ne'] at h''
    simp only [smul_apply, sub_apply, smul_eq_mul]
    linarith
  have hg_eq : g = y + a • a⁻¹ • (g - y) := by rw [smul_inv_smul₀ ha.ne', add_sub_cancel]
  rw [hg_eq]
  exact norm_add_surrogateCoeff_smul_le_norm hq hx hxz

end InnerProductSpace

section Regret

variable {ℓ : ℕ → E → ℝ} {y q : ℕ → E →L[ℝ] ℝ} {a : ℕ → ℝ} {x z : ℕ → E}

/-- **Constrained online convex optimization through projections, with the penalized surrogates**
[Ora, Theorem 12.5]. Let `x t` be a nearest point of `V` to `z t`, let `y t` be a subgradient
of `ℓ t` within `V` at `x t`, and let the weights `a t` dominate the positive parts of the
increases `y t (x t - z t)` relative to the distances, as `‖y t‖` and
`surrogateCoeff (y t) (x t) (z t)` do. Then the regret of the plays `x t` against `u ∈ V` is at
most the regret of the plays `z t` for the penalized losses `penalizedLoss V (y t) (a t)`. -/
theorem regret_le_regret_penalizedLoss
    (hy : ∀ t < n, HasSubgradientWithinAt (ℓ t) (y t) V (x t))
    (hx : ∀ t < n, infDist (z t) V = dist (z t) (x t))
    (ha : ∀ t < n, max (y t (x t - z t)) 0 ≤ a t * ‖x t - z t‖) (hu : u ∈ V) :
    regret ℓ x u n ≤ regret (fun t ↦ penalizedLoss V (y t) (a t)) z u n := by
  rw [regret_def ℓ, regret_def (fun t ↦ penalizedLoss V (y t) (a t))]
  refine (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt ℓ y x hy hu).trans
    (sum_le_sum fun t ht ↦ ?_)
  have ht := mem_range.mp ht
  exact apply_sub_le_penalizedLoss_sub (hx t ht) (ha t ht) (subset_closure hu)

/-- **Constrained online convex optimization through projections, with the linearized
surrogates** [Ora, Theorem 12.5]. Under the hypotheses of `regret_le_regret_penalizedLoss`, with
nonnegative weights and subgradients `q t` of the distance to `V` at `z t`, the regret of the plays
`x t` against `u ∈ V` is at most the regret of the plays `z t` for the linear losses
`y t + a t • q t`. -/
theorem regret_le_regret_add_smul
    (hy : ∀ t < n, HasSubgradientWithinAt (ℓ t) (y t) V (x t))
    (hx : ∀ t < n, infDist (z t) V = dist (z t) (x t))
    (ha : ∀ t < n, max (y t (x t - z t)) 0 ≤ a t * ‖x t - z t‖) (ha₀ : ∀ t < n, 0 ≤ a t)
    (hq : ∀ t < n, HasSubgradientWithinAt (infDist · V) (q t) s (z t)) (hus : u ∈ s)
    (hu : u ∈ V) :
    regret ℓ x u n ≤ regret (fun t ↦ y t + a t • q t) z u n := by
  rw [regret_def ℓ, regret_eq_sum_apply_sub]
  refine (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt ℓ y x hy hu).trans
    (sum_le_sum fun t ht ↦ ?_)
  have ht := mem_range.mp ht
  exact apply_sub_le_add_smul_apply_sub (hx t ht) (ha t ht) (ha₀ t ht) (hq t ht) hus
    (subset_closure hu)

end Regret

/-- The fourth surrogate of [Ora, Theorem 12.5] for the projection `p z` of the play `z`, the loss
`y` and the subgradient `q z` of the distance at `z`. -/
noncomputable def constrainSurrogate (p : E → E) (q : E → E →L[ℝ] ℝ) (z : E) (y : E →L[ℝ] ℝ) :
    E →L[ℝ] ℝ :=
  y + surrogateCoeff y (p z) z • q z

lemma constrainSurrogate_def (p : E → E) (q : E → E →L[ℝ] ℝ) (z : E) (y : E →L[ℝ] ℝ) :
    constrainSurrogate p q z y = y + surrogateCoeff y (p z) z • q z := (rfl)

namespace OnlineLearner

variable {C : Type*} (A : OnlineLearner C (E →L[ℝ] ℝ) E) (p : E → E) (q : E → E →L[ℝ] ℝ)

/-- The learner `A` **constrained by the projection `p`** [Ora, Algorithm 12.1]: when `A` plays `z`,
it plays `p z`, and it feeds `A` the fourth surrogate `constrainSurrogate p q z y` of the loss `y`
of its play, for the subgradients `q z` of the distance to the feasible set. When `p` maps into a
set `V`, its plays lie in `V` (`run_constrain_mem`). When moreover the `p z` are nearest points of
`V`, the `q z` are subgradients of the distance to `V` and the surrogates of the admissible losses
are admissible for `A`, a regret bound `B` of `A` against the comparators of `V` is a regret bound
of the constrained learner, with `B` evaluated at the surrogate losses fed to `A`
(`HasRegretBound.constrain`). -/
noncomputable def constrain : OnlineLearner C (E →L[ℝ] ℝ) E :=
  A.reduce p (constrainSurrogate p q)

/-- The plays of the constrained learner are the projections of the plays of the closed-loop run of
`A` fed the surrogate losses. -/
@[simp]
lemma run_constrain (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) :
    (A.constrain p q).run c y t =
      p (A.run c (A.closedLoopFeedback c fun s z ↦ constrainSurrogate p q z (y s)) t) :=
  A.run_reduce p _ c y t

/-- The plays of the constrained learner lie in `V` when the projection maps into `V`. -/
lemma run_constrain_mem (hp : ∀ z, p z ∈ V) (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) :
    (A.constrain p q).run c y t ∈ V := by
  rw [run_constrain]
  exact hp _

variable {A p q} {adm adm' : C → (E →L[ℝ] ℝ) → Prop} {U : Set E}
  {B : ℕ → (ℕ → C) → (ℕ → E →L[ℝ] ℝ) → E → ℝ}

/-- **Regret guarantee of the constrained learner** [Ora, Theorem 12.5]. Let `p z` be a nearest
point of `V` to `z` and `q z` a subgradient of the distance to `V` at `z` within `V`, for every
`z` (for instance a subgradient within `univ`). If `A` has the regret bound `B` for linear losses
against the comparators of `U ⊇ V`, and the surrogate of every admissible loss is admissible for
`A`, then the constrained learner has the regret bound `B` at the surrogate losses against the
comparators of `V`. -/
theorem HasRegretBound.constrain (hA : A.HasRegretBound (fun y x ↦ y x) adm U B) (hVU : V ⊆ U)
    (hp : ∀ z, infDist z V = dist z (p z))
    (hq : ∀ z, HasSubgradientWithinAt (infDist · V) (q z) V z)
    (hadm : ∀ c y z, adm' c y → adm c (constrainSurrogate p q z y)) :
    (A.constrain p q).HasRegretBound (fun y x ↦ y x) adm' V
      (fun n c y u ↦ B n c (A.closedLoopFeedback c fun s z ↦ constrainSurrogate p q z (y s)) u) :=
  hA.reduce hVU hadm fun _ y z _ u hu ↦ by
    have h := apply_sub_le_add_surrogateCoeff_smul_apply_sub (y := y) (hp z) (hq z) hu
      (subset_closure hu)
    simpa only [constrainSurrogate_def, map_sub] using h

/-- **Regret guarantee of the constrained learner for bounded losses** [Ora, Theorem 12.5]. If `A`
has the regret bound `B` for linear losses of dual norm at most `2 L` against the comparators of
`U ⊇ V`, then the constrained learner has the regret bound `B` at the surrogate losses for linear
losses of dual norm at most `L`, against the comparators of `V`, for nearest points `p z` of `V`
and subgradients `q z` of the distance to `V` at `z` within `univ`. -/
theorem HasRegretBound.constrain_of_norm_le {L : ℝ}
    (hA : A.HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ 2 * L) U B) (hVU : V ⊆ U)
    (hp : ∀ z, infDist z V = dist z (p z))
    (hq : ∀ z, HasSubgradientWithinAt (infDist · V) (q z) univ z) :
    (A.constrain p q).HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) V
      (fun n c y u ↦ B n c (A.closedLoopFeedback c fun s z ↦ constrainSurrogate p q z (y s)) u) :=
  hA.constrain hVU hp (fun z ↦ (hq z).mono (subset_univ V)) fun _ y z hy ↦ by
    rw [constrainSurrogate_def]
    exact (norm_add_surrogateCoeff_smul_le ((hq z).norm_le_one_of_infDist Filter.univ_mem)).trans
      (by linarith)

end OnlineLearner

namespace OnlineLearner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {V U : Set F} {C : Type*}
  {A : OnlineLearner C (F →L[ℝ] ℝ) F} {p : F → F} {q : F → F →L[ℝ] ℝ}
  {B : ℕ → (ℕ → C) → (ℕ → F →L[ℝ] ℝ) → F → ℝ}

/-- **Regret guarantee of the constrained learner for bounded losses, in an inner product space**
[Ora, Theorem 12.5, Remark 12.6]. If `A` has the regret bound `B` for linear losses of dual norm
at most `L` against the comparators of `U ⊇ V`, then so does the constrained learner, at the
surrogate losses, against the comparators of `V`, for nearest points `p z` in the closure of
`V` and subgradients `q z` of the distance to `V` at `z` within `univ`. -/
theorem HasRegretBound.constrain_of_norm_le_of_inner {L : ℝ}
    (hA : A.HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) U B) (hVU : V ⊆ U)
    (hpV : ∀ z, p z ∈ closure V) (hp : ∀ z, infDist z V = dist z (p z))
    (hq : ∀ z, HasSubgradientWithinAt (infDist · V) (q z) univ z) :
    (A.constrain p q).HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) V
      (fun n c y u ↦ B n c (A.closedLoopFeedback c fun s z ↦ constrainSurrogate p q z (y s)) u) :=
  hA.constrain hVU hp (fun z ↦ (hq z).mono (subset_univ V)) fun _ y z hy ↦ by
    rw [constrainSurrogate_def]
    exact (norm_add_surrogateCoeff_smul_le_norm (hq z) (hpV z) (hp z)).trans hy

end OnlineLearner

section Clip

/-- The surrogate loss of the clipping of a learner on `ℝ` to `[0, ∞)` [Ora, Example 12.9]: for the
play `z` and the loss `g`, it is `min g 0` when `z < 0` and `g` otherwise. -/
noncomputable def clipSurrogate (z g : ℝ) : ℝ :=
  if z < 0 then min g 0 else g

lemma clipSurrogate_of_neg {z : ℝ} (hz : z < 0) (g : ℝ) : clipSurrogate z g = min g 0 := by
  simp [clipSurrogate, hz]

lemma clipSurrogate_of_nonneg {z : ℝ} (hz : 0 ≤ z) (g : ℝ) : clipSurrogate z g = g := by
  simp [clipSurrogate, hz.not_gt]

/-- The clipping surrogate is not larger than the loss. -/
lemma abs_clipSurrogate_le (z g : ℝ) : |clipSurrogate z g| ≤ |g| := by
  unfold clipSurrogate
  split_ifs
  · rcases le_total g 0 with hg | hg
    · rw [min_eq_left hg]
    · rw [min_eq_right hg, abs_zero]
      exact abs_nonneg g
  · exact le_rfl

/-- **The clipping surrogate inequality** [Ora, Example 12.9]: for `u ≥ 0`, the loss of the
clipped play `max z 0` relative to `u` is at most the surrogate loss of `z` relative to `u`. -/
theorem mul_max_sub_le_clipSurrogate_mul_sub {z u : ℝ} (g : ℝ) (hu : 0 ≤ u) :
    g * (max z 0 - u) ≤ clipSurrogate z g * (z - u) := by
  rcases lt_or_ge z 0 with hz | hz
  · rw [clipSurrogate_of_neg hz, max_eq_right hz.le]
    rcases le_total g 0 with hg | hg
    · rw [min_eq_left hg]
      nlinarith
    · rw [min_eq_right hg]
      nlinarith
  · rw [clipSurrogate_of_nonneg hz, max_eq_left hz]

namespace OnlineLearner

variable {C : Type*} (A : OnlineLearner C ℝ ℝ)

/-- The learner `A` on `ℝ` **clipped to `[0, ∞)`** [Ora, Example 12.9]: when `A` plays `z`, it plays
`max z 0`, and it feeds `A` the surrogate loss `clipSurrogate z g` of the loss `g` of its play. -/
noncomputable def clipNonneg : OnlineLearner C ℝ ℝ :=
  A.reduce (max · 0) clipSurrogate

/-- The plays of the clipped learner are the positive parts of the plays of the closed-loop run of
`A` fed the surrogate losses. -/
@[simp]
lemma run_clipNonneg (c : ℕ → C) (g : ℕ → ℝ) (t : ℕ) :
    A.clipNonneg.run c g t =
      max (A.run c (A.closedLoopFeedback c fun s z ↦ clipSurrogate z (g s)) t) 0 :=
  A.run_reduce _ _ c g t

/-- The plays of the clipped learner are nonnegative. -/
lemma run_clipNonneg_nonneg (c : ℕ → C) (g : ℕ → ℝ) (t : ℕ) : 0 ≤ A.clipNonneg.run c g t := by
  rw [run_clipNonneg]
  exact le_max_right _ _

variable {A} {adm adm' : C → ℝ → Prop} {U : Set ℝ} {B : ℕ → (ℕ → C) → (ℕ → ℝ) → ℝ → ℝ}

/-- **Regret guarantee of the clipped learner** [Ora, Example 12.9]. If `A` has the regret bound
`B` for the linear losses `x ↦ g * x` on `ℝ` against the comparators of `U ⊇ [0, ∞)`, and the
surrogate of every admissible loss is admissible for `A`, then the clipped learner has the regret
bound `B` at the surrogate losses against the nonnegative comparators. Since
`|clipSurrogate z g| ≤ |g|` (`abs_clipSurrogate_le`), admissibility by a bound on `|g|` is
inherited. -/
theorem HasRegretBound.clipNonneg (hA : A.HasRegretBound (fun g x ↦ g * x) adm U B)
    (hU : Set.Ici 0 ⊆ U) (hadm : ∀ c g z, adm' c g → adm c (clipSurrogate z g)) :
    A.clipNonneg.HasRegretBound (fun g x ↦ g * x) adm' (Set.Ici 0)
      (fun n c g u ↦ B n c (A.closedLoopFeedback c fun s z ↦ clipSurrogate z (g s)) u) :=
  hA.reduce hU hadm fun _ g z _ u hu ↦ by
    have h := mul_max_sub_le_clipSurrogate_mul_sub (z := z) g (Set.mem_Ici.mp hu)
    rw [mul_sub, mul_sub] at h
    exact h

end OnlineLearner

end Clip

end LMLExplore.OnlineLearning
