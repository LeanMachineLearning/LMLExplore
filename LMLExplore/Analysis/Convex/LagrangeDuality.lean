/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.EReal.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Order.Filter.Extr

/-!
# Lagrange duality for finitely many convex constraints

Consider the convex program of minimizing `F x` over the points `x` of a convex set `C` that
satisfy finitely many convex constraints `h i x ≤ 0`, `i : ι`. Its Lagrangian is
`F x + ∑ i, π i * h i x` for multipliers `π : ι → ℝ≥0`, and its dual function is the infimum of the
Lagrangian over all of `C`, with the constraints dropped. Weak duality, that the dual function is
below the value of the program, holds for every problem. Under **Slater's condition**, that some
`x₀ ∈ C` satisfies every constraint strictly, there is no duality gap: the value of the program is
the maximum over `π` of the dual function, and the minimizers of the program are the points that
minimize the Lagrangian of an optimal multiplier with complementary slackness [Lue69, §8.3,
Theorem 1; §8.6, Theorem 1].

The existence of multipliers only needs `F` and `h` to be jointly *convex-like* on `C` in the sense
of Fan [Fan53]: for `x, y ∈ C` and weights `a, b`, some `z ∈ C` has `F z` and every `h i z` below
the corresponding convex combinations of the values at `x` and `y`
(`LMLExplore.JointlyConvexLikeOn`). It is stated in that form in
`LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`, which needs no linear structure on the
domain and so applies to convex sets of probability measures, which carry no real scalar
multiplication. Strong duality and the saddle point characterization are stated in the same
convex-like form, and specialized to convex functions on a convex set. The sufficiency of the
saddle point condition holds with no hypothesis.

Values of the dual function are taken in `EReal`, except in
`LMLExplore.exists_iInf_eq_iInf_add_of_slater`, which assumes the value of the program finite: the
real infimum of a Lagrangian unbounded below is the junk value `0`, for which weak duality fails.

This is the duality behind the dual formula of the minimal Kullback–Leibler divergence to a set
of laws defined by finitely many moment constraints, `KL_inf`, as the maximal expected logarithm
of a bet `1 + ∑ i, π i * g i`.

## Main definitions

* `LMLExplore.JointlyConvexLikeOn C F h`: `F` and the `h i` are jointly convex-like on `C`;
  `ConvexOn.jointlyConvexLikeOn` derives it from convexity.

## Main statements

* `LMLExplore.iSup_iInf_add_le_iInf`: weak duality in `EReal`, with no hypothesis.
* `IsMinOn.of_add_sum_mul`: a minimizer of a Lagrangian with complementary
  slackness minimizes the program, with no hypothesis.
* `LMLExplore.exists_ne_zero_forall_le_of_convexLike`: Fritz John multipliers for convex-like data,
  with no constraint qualification.
* `LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`: under Slater's condition, every lower
  bound of the objective on the feasible set is a lower bound of the Lagrangian on all of `C` for
  some multiplier, for convex-like data on any type;
  `LMLExplore.exists_forall_le_add_sum_mul_of_slater` for convex functions.
* `LMLExplore.exists_iInf_eq_iInf_add_of_convexLike`: strong duality in `EReal` with an attained
  dual optimum, for convex-like data; `LMLExplore.exists_iInf_eq_iInf_add_of_slater` with real
  values, for convex functions with a finite primal value.
* `LMLExplore.iInf_eq_iSup_iInf_add_of_convexLike`: strong duality in `EReal`, where the primal
  value may be `⊥`, for convex-like data; `LMLExplore.iInf_eq_iSup_iInf_add_of_slater` for convex
  functions.
* `LMLExplore.isMinOn_iff_exists_isMinOn_add_sum_mul_of_convexLike`: the saddle point
  characterization of the minimizers, by a multiplier for which they minimize the Lagrangian with
  complementary slackness, for convex-like data;
  `IsMinOn.exists_mul_eq_zero_and_isMinOn_add_sum_mul_of_slater` gives the multiplier for convex
  functions.

## Implementation notes

The multiplier is produced by separating the point `(m, 0)`, for a lower bound `m` of `F` on the
feasible set, from the open convex set of the `v : Option ι → ℝ` lying strictly above
`(F x, h · x)` for some `x ∈ C`, with Mathlib's `geometric_hahn_banach_open_point`; Slater's
condition makes the coefficient of the objective in the separating functional nonzero.

## References

* [Lue69] D. G. Luenberger, *Optimization by Vector Space Methods*, Wiley, 1969, Chapter 8.
* [Fan53] K. Fan, *Minimax theorems*, Proc. Natl. Acad. Sci. USA 39 (1953), 42–47.
* [BV04] S. Boyd, L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, §5.3.2
  and §5.5.2.
-/

public section

open Filter Set Topology
open scoped NNReal

variable {X ι : Type*} {C : Set X} {F : X → ℝ} {h : ι → X → ℝ}

namespace LMLExplore

/-- `F` and the family `h` are *jointly convex-like* on `C`, in the sense of Fan [Fan53]: for
`x, y ∈ C` and weights `a, b ≥ 0` with `a + b = 1`, some `z ∈ C` has `F z` and every `h i z` below
the corresponding convex combinations of the values at `x` and `y`. Convex functions on a convex
set are jointly convex-like (`ConvexOn.jointlyConvexLikeOn`). The definition needs no linear
structure on `X`, so it also applies to functionals of probability measures, taking `z` to be a
mixture. -/
def JointlyConvexLikeOn (C : Set X) (F : X → ℝ) (h : ι → X → ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    ∃ z ∈ C, F z ≤ a * F x + b * F y ∧ ∀ i, h i z ≤ a * h i x + b * h i y

/-- The defining property of `LMLExplore.JointlyConvexLikeOn`. -/
theorem jointlyConvexLikeOn_iff : JointlyConvexLikeOn C F h ↔
    ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ z ∈ C, F z ≤ a * F x + b * F y ∧ ∀ i, h i z ≤ a * h i x + b * h i y :=
  Iff.rfl

/-- The Lagrangian of a nonnegative multiplier is below the objective on the feasible set. -/
private lemma add_sum_mul_le [Fintype ι] (π : ι → ℝ≥0) {x : X} (hx : ∀ i, h i x ≤ 0) :
    F x + ∑ i, (π i : ℝ) * h i x ≤ F x :=
  add_le_of_nonpos_right <| Finset.sum_mul_nonpos (fun i _ ↦ (π i).property) fun i _ ↦ hx i

/-- **Weak duality** in `EReal`: for every problem, the supremum over the multipliers of the
infimum of the Lagrangian over `C` is below the infimum of the objective on the feasible set. -/
theorem iSup_iInf_add_le_iInf [Fintype ι] :
    ⨆ π : ι → ℝ≥0, ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) ≤
      ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) :=
  iSup_le fun π ↦ le_iInf₂ fun x hx ↦
    (iInf₂_le x hx.1).trans (EReal.coe_le_coe_iff.2 (add_sum_mul_le π hx.2))

/-- **Sufficiency of the saddle point condition** [Lue69, §8.4]. If `x` minimizes over `C` the
Lagrangian `F y + ∑ i, π i * h i y` of some multiplier `π : ι → ℝ≥0`, with complementary slackness
`π i * h i x = 0` for every `i`, then `x` minimizes `F` over `{y ∈ C | ∀ i, h i y ≤ 0}`. No
convexity or constraint qualification is needed. -/
theorem _root_.IsMinOn.of_add_sum_mul [Fintype ι] {π : ι → ℝ≥0} {x : X}
    (hmin : IsMinOn (fun y ↦ F y + ∑ i, (π i : ℝ) * h i y) C x)
    (hslack : ∀ i, (π i : ℝ) * h i x = 0) : IsMinOn F {y ∈ C | ∀ i, h i y ≤ 0} x := by
  refine isMinOn_iff.2 fun y ⟨hy, hyh⟩ ↦ ?_
  have hle := isMinOn_iff.1 hmin y hy
  simp only [hslack, Finset.sum_const_zero, add_zero] at hle
  exact hle.trans (add_sum_mul_le π hyh)

/-- The objective (`none`) and the constraints (`some i`) of the program, as one family. -/
private def objConstr (F : X → ℝ) (h : ι → X → ℝ) (j : Option ι) (x : X) : ℝ :=
  j.elim (F x) fun i ↦ h i x

/-- The points lying strictly above the joint values of the objective and the constraints at some
point of `C`. -/
private def strictEpigraph (C : Set X) (F : X → ℝ) (h : ι → X → ℝ) : Set (Option ι → ℝ) :=
  {v | ∃ x ∈ C, ∀ j, objConstr F h j x < v j}

private lemma isOpen_strictEpigraph [Finite ι] : IsOpen (strictEpigraph C F h) := by
  have : strictEpigraph C F h = ⋃ x ∈ C, ⋂ j, {v : Option ι → ℝ | objConstr F h j x < v j} := by
    ext v
    simp [strictEpigraph]
  rw [this]
  exact isOpen_biUnion fun x _ ↦ isOpen_iInter_of_finite fun j ↦
    isOpen_lt continuous_const (continuous_apply j)

private lemma convex_strictEpigraph (hconv : JointlyConvexLikeOn C F h) :
    Convex ℝ (strictEpigraph C F h) := by
  rintro v ⟨x, hx, hxv⟩ w ⟨y, hy, hyw⟩ a b ha hb hab
  obtain ⟨z, hz, hFz, hhz⟩ := jointlyConvexLikeOn_iff.1 hconv x hx y hy a b ha hb hab
  refine ⟨z, hz, fun j ↦ ?_⟩
  have hz' : objConstr F h j z ≤ a * objConstr F h j x + b * objConstr F h j y := by
    cases j <;> simp [objConstr, hFz, hhz]
  -- The convex combination of `objConstr F h j x - v j < 0` and `objConstr F h j y - w j < 0`.
  have hlt := convex_Iio (0 : ℝ) (sub_neg.2 (hxv j)) (sub_neg.2 (hyw j)) ha hb hab
  simp only [mem_Iio, smul_eq_mul] at hlt
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

private lemma mem_strictEpigraph_of_le {v w : Option ι → ℝ} (hv : v ∈ strictEpigraph C F h)
    (hvw : v ≤ w) : w ∈ strictEpigraph C F h := by
  obtain ⟨x, hx, hxv⟩ := hv
  exact ⟨x, hx, fun j ↦ (hxv j).trans_le (hvw j)⟩

/-- A functional below `f p` on the upward closed set `strictEpigraph C F h` is at most `f p` at
the joint values of the objective and the constraints at every point of `C`. -/
private lemma apply_le_of_forall_lt {f : StrongDual ℝ (Option ι → ℝ)} {p : Option ι → ℝ}
    (hf : ∀ v ∈ strictEpigraph C F h, f v < f p) {x : X} (hx : x ∈ C) :
    f (fun j ↦ objConstr F h j x) ≤ f p := by
  set v : Option ι → ℝ := fun j ↦ objConstr F h j x
  -- `v + ε • 1` lies in `strictEpigraph C F h` for `ε > 0`, and tends to `v` as `ε → 0`.
  have hlim : Tendsto (fun ε : ℝ ↦ f v + ε * f 1) (𝓝[>] 0) (𝓝 (f v)) := by
    have : Tendsto (fun ε : ℝ ↦ f v + ε * f 1) (𝓝 0) (𝓝 (f v + 0 * f 1)) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦ ?_)
  have := hf (v + ε • 1) ⟨x, hx, fun j ↦ by simpa [v] using hε⟩
  rw [map_add, map_smul, smul_eq_mul] at this
  exact this.le

/-- A functional below `f p` on the nonempty upward closed set `strictEpigraph C F h` is
nonpositive on nonnegative vectors. -/
private lemma apply_nonpos_of_forall_lt {f : StrongDual ℝ (Option ι → ℝ)} {p a : Option ι → ℝ}
    (hf : ∀ v ∈ strictEpigraph C F h, f v < f p) (ha : a ∈ strictEpigraph C F h)
    {w : Option ι → ℝ} (hw : 0 ≤ w) : f w ≤ 0 := by
  by_contra! hfw
  -- Moving from `a` in the direction `w` reaches the level `f p` inside the set.
  have ht : 0 ≤ (f p - f a) / f w := div_nonneg (sub_nonneg.2 (hf a ha).le) hfw.le
  have := hf (a + ((f p - f a) / f w) • w) (mem_strictEpigraph_of_le ha fun k ↦ by
    simpa using mul_nonneg ht (hw k))
  rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfw.ne'] at this
  linarith

/-- **Fritz John multipliers** for convex-like data, with no constraint qualification. Let `F` and
finitely many `h i` be jointly convex-like on a set `C`, as in
`LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`. If `m` is a lower bound of `F` on the
feasible set `{x ∈ C | ∀ i, h i x ≤ 0}`, then some nonzero `c : Option ι → ℝ` with nonnegative
entries, the coefficient `c none` of the objective and the coefficients `c (some i)` of the
constraints, has `c none * m ≤ c none * F x + ∑ i, c (some i) * h i x` for every `x ∈ C`.

Under Slater's condition `c none` is positive, which gives
`LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`. -/
theorem exists_ne_zero_forall_le_of_convexLike [Fintype ι]
    (hconv : JointlyConvexLikeOn C F h)
    {m : ℝ} (hm : ∀ x ∈ C, (∀ i, h i x ≤ 0) → m ≤ F x) :
    ∃ c : Option ι → ℝ, c ≠ 0 ∧ (∀ j, 0 ≤ c j) ∧
      ∀ x ∈ C, c none * m ≤ c none * F x + ∑ i, c (some i) * h i x := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨fun _ ↦ 1, fun h1 ↦ one_ne_zero (congrFun h1 none), fun _ ↦ zero_le_one,
      fun x hx ↦ absurd hx (notMem_empty x)⟩
  -- The point `(m, 0)` lies outside the open convex set `strictEpigraph C F h`, so a continuous
  -- linear functional `f` separates them.
  let p : Option ι → ℝ := fun j ↦ j.elim m fun _ ↦ 0
  have hp : p ∉ strictEpigraph C F h := by
    rintro ⟨x, hx, hxp⟩
    exact (hxp none).not_ge (hm x hx fun i ↦ (hxp (some i)).le)
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (convex_strictEpigraph hconv)
    isOpen_strictEpigraph hp
  have ha₀ : (fun j ↦ objConstr F h j x₀ + 1) ∈ strictEpigraph C F h :=
    ⟨x₀, hx₀, fun j ↦ by simp⟩
  -- The coefficients `c j` of `f` in the standard basis; the multipliers are `-c`.
  let e : Option ι → Option ι → ℝ := fun j k ↦ if j = k then 1 else 0
  let c : Option ι → ℝ := fun j ↦ f (e j)
  have hfc (v : Option ι → ℝ) : f v = c none * v none + ∑ i, c (some i) * v (some i) := by
    rw [← Fintype.sum_option (fun j ↦ c j * v j)]
    simpa [c, e, smul_eq_mul, mul_comm] using
      LinearMap.pi_apply_eq_sum_univ (f : (Option ι → ℝ) →ₗ[ℝ] ℝ) v
  refine ⟨-c, neg_ne_zero.2 fun hc ↦ ?_, fun j ↦ neg_nonneg.2 <|
    apply_nonpos_of_forall_lt hf ha₀ fun k ↦ by by_cases hjk : j = k <;> simp [e, hjk],
    fun x hx ↦ ?_⟩
  · -- `f` is nonzero, since it is strictly below `f p` somewhere.
    have := hf _ ha₀
    simp [hfc, hc] at this
  · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, ← neg_add, neg_le_neg_iff]
    simpa [hfc, objConstr, p] using apply_le_of_forall_lt hf hx

/-- **Lagrange multipliers under Slater's condition** [Lue69, §8.3, Theorem 1], for convex-like
data [Fan53]. Let `F` and finitely many `h i` be jointly convex-like on a set `C`
(`LMLExplore.JointlyConvexLikeOn`): for `x, y ∈ C` and weights `a, b ≥ 0` with `a + b = 1`, some
`z ∈ C` has `F z` and every `h i z` below the corresponding convex combinations of the values at
`x` and `y`. If some `x₀ ∈ C` satisfies `h i x₀ < 0` for every `i` and `m` is a lower bound of
`F` on the feasible set `{x ∈ C | ∀ i, h i x ≤ 0}`, then some multiplier `π : ι → ℝ≥0` makes `m` a
lower bound of the Lagrangian `F x + ∑ i, π i * h i x` on all of `C`.

No vector space structure on `X` is needed: this applies to convex sets of measures. For convex
functions on a convex set, see `LMLExplore.exists_forall_le_add_sum_mul_of_slater`.
-/
theorem exists_forall_le_add_sum_mul_of_convexLike [Fintype ι]
    (hconv : JointlyConvexLikeOn C F h)
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {m : ℝ}
    (hm : ∀ x ∈ C, (∀ i, h i x ≤ 0) → m ≤ F x) :
    ∃ π : ι → ℝ≥0, ∀ x ∈ C, m ≤ F x + ∑ i, (π i : ℝ) * h i x := by
  obtain ⟨x₀, hx₀, hx₀h⟩ := hslater
  obtain ⟨c, hc, hc_nonneg, hcx⟩ := exists_ne_zero_forall_le_of_convexLike hconv hm
  -- By Slater's condition the coefficient of the objective is positive: otherwise the terms
  -- `c (some i) * h i x₀ ≤ 0` would have a nonnegative sum, so every coefficient would vanish.
  have hc_pos : 0 < c none := by
    refine (hc_nonneg none).lt_of_ne' fun h0 ↦ hc ?_
    have hsum : 0 ≤ ∑ i, c (some i) * h i x₀ := by simpa [h0] using hcx x₀ hx₀
    have hzero (i : ι) : c (some i) = 0 :=
      (mul_eq_zero.1 (Finset.mul_eq_zero_of_sum_mul_nonneg (fun _ _ ↦ hc_nonneg _)
        (fun i _ ↦ (hx₀h i).le) hsum (Finset.mem_univ i))).resolve_right (hx₀h i).ne
    ext (_ | i)
    exacts [h0, hzero i]
  -- Normalize the coefficient of the objective to `1`.
  have hc0 : c none ≠ 0 := hc_pos.ne'
  have hL (x : X) (hx : x ∈ C) : m ≤ F x + ∑ i, c (some i) / c none * h i x := by
    have hmul : c none * (F x + ∑ i, c (some i) / c none * h i x) =
        c none * F x + ∑ i, c (some i) * h i x := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
    refine le_of_mul_le_mul_left ?_ hc_pos
    rw [hmul]
    exact hcx x hx
  exact ⟨fun i ↦ ⟨c (some i) / c none, div_nonneg (hc_nonneg _) hc_pos.le⟩, hL⟩

/-- **Strong duality under Slater's condition with an attained dual optimum**, for convex-like
data [Fan53]. Let `F` and finitely many `h i` be jointly convex-like on a set `C`, as in
`LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`. If some `x₀ ∈ C` satisfies `h i x₀ < 0` for
every `i`, then some multiplier `π : ι → ℝ≥0` makes the infimum of `F` over the feasible set
`{x ∈ C | ∀ i, h i x ≤ 0}` equal to the infimum over `C` of the Lagrangian
`F x + ∑ i, π i * h i x`. Values are in `EReal`, so no boundedness is assumed: when `F` is
unbounded below on the feasible set, both sides are `⊥`. -/
theorem exists_iInf_eq_iInf_add_of_convexLike [Fintype ι]
    (hconv : JointlyConvexLikeOn C F h)
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ∃ π : ι → ℝ≥0, ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) =
      ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) := by
  set P := ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal)
  obtain ⟨x₀, hx₀, hx₀h⟩ := hslater
  rcases eq_or_ne P ⊥ with hP | hP
  · exact ⟨0, hP.trans (le_bot_iff.1 (hP ▸ iSup_le_iff.1 iSup_iInf_add_le_iInf 0)).symm⟩
  have hPtop : P ≠ ⊤ :=
    ((iInf₂_le x₀ ⟨hx₀, fun i ↦ (hx₀h i).le⟩).trans_lt (EReal.coe_lt_top _)).ne
  obtain ⟨π, hπ⟩ := exists_forall_le_add_sum_mul_of_convexLike hconv ⟨x₀, hx₀, hx₀h⟩
    (m := P.toReal) fun x hx hxh ↦ by
      rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hPtop hP]
      exact iInf₂_le x ⟨hx, hxh⟩
  refine ⟨π, le_antisymm ?_ (iSup_le_iff.1 iSup_iInf_add_le_iInf π)⟩
  rw [← EReal.coe_toReal hPtop hP]
  exact le_iInf₂ fun x hx ↦ EReal.coe_le_coe_iff.2 (hπ x hx)

/-- **Strong Lagrange duality under Slater's condition** [Lue69, §8.6, Theorem 1], for convex-like
data [Fan53]. Let `F` and finitely many `h i` be jointly convex-like on a set `C`, as in
`LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`. If some `x₀ ∈ C` satisfies `h i x₀ < 0` for
every `i`, then the infimum of `F` over `{x ∈ C | ∀ i, h i x ≤ 0}` is the supremum over multipliers
`π : ι → ℝ≥0` of the infimum over `C` of the Lagrangian `F x + ∑ i, π i * h i x`, in `EReal`. The
supremum is attained (`LMLExplore.exists_iInf_eq_iInf_add_of_convexLike`). -/
theorem iInf_eq_iSup_iInf_add_of_convexLike [Fintype ι]
    (hconv : JointlyConvexLikeOn C F h)
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) =
      ⨆ π : ι → ℝ≥0, ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) := by
  obtain ⟨π, hπ⟩ := exists_iInf_eq_iInf_add_of_convexLike hconv hslater
  exact le_antisymm (hπ.le.trans (le_iSup_of_le π le_rfl)) iSup_iInf_add_le_iInf

/-- **Saddle point characterization of the minimizers** [Lue69, §8.3, Theorem 1; §8.4], for
convex-like data [Fan53]. Let `F` and finitely many `h i` be jointly convex-like on a set `C`, as
in `LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`, with some `x₀ ∈ C` satisfying
`h i x₀ < 0` for every `i`. A feasible point `x` minimizes `F` over `{y ∈ C | ∀ i, h i y ≤ 0}`
exactly when some multiplier `π : ι → ℝ≥0` makes `x` a minimizer over `C` of the Lagrangian
`F y + ∑ i, π i * h i y`, with complementary slackness `π i * h i x = 0` for every `i`. -/
theorem isMinOn_iff_exists_isMinOn_add_sum_mul_of_convexLike [Fintype ι]
    (hconv : JointlyConvexLikeOn C F h)
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {x : X} (hx : x ∈ C) (hxh : ∀ i, h i x ≤ 0) :
    IsMinOn F {y ∈ C | ∀ i, h i y ≤ 0} x ↔
      ∃ π : ι → ℝ≥0, IsMinOn (fun y ↦ F y + ∑ i, (π i : ℝ) * h i y) C x ∧
        ∀ i, (π i : ℝ) * h i x = 0 := by
  constructor
  · intro hmin
    obtain ⟨π, hπ⟩ := exists_forall_le_add_sum_mul_of_convexLike hconv hslater (m := F x)
      fun y hy hyh ↦ isMinOn_iff.1 hmin y ⟨hy, hyh⟩
    -- At `x` the sum of the nonpositive terms `π i * h i x` is nonnegative, hence each is zero.
    have hslack (i : ι) : (π i : ℝ) * h i x = 0 :=
      Finset.mul_eq_zero_of_sum_mul_nonneg (fun i _ ↦ (π i).property) (fun i _ ↦ hxh i)
        ((le_add_iff_nonneg_right _).1 (hπ x hx)) (Finset.mem_univ i)
    exact ⟨π, isMinOn_iff.2 fun y hy ↦ by simpa [hslack] using hπ y hy, hslack⟩
  · rintro ⟨π, hmin, hslack⟩
    exact hmin.of_add_sum_mul hslack

section ConvexOn

variable [AddCommMonoid X] [SMul ℝ X]

/-- Convex functions on a convex set are jointly convex-like there, witnessed by `a • x + b • y`. -/
theorem _root_.ConvexOn.jointlyConvexLikeOn (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i)) :
    JointlyConvexLikeOn C F h :=
  jointlyConvexLikeOn_iff.2 fun x hx y hy a b ha hb hab ↦ ⟨a • x + b • y, hF.1 hx hy ha hb hab,
    by simpa using hF.2 hx hy ha hb hab, fun i ↦ by simpa using (hh i).2 hx hy ha hb hab⟩

variable [Fintype ι]

/-- **Lagrange multipliers under Slater's condition** [Lue69, §8.3, Theorem 1]. If `F` and the
finitely many constraints `h i` are convex on `C`, some point of `C` satisfies every constraint
strictly, and `p` is below `F` on the feasible set `{x ∈ C | ∀ i, h i x ≤ 0}`, then some multiplier
`π : ι → ℝ≥0` makes `p` a lower bound of the Lagrangian `F x + ∑ i, π i * h i x` on all of `C`.
For convex-like data, see `LMLExplore.exists_forall_le_add_sum_mul_of_convexLike`. -/
theorem exists_forall_le_add_sum_mul_of_slater (hF : ConvexOn ℝ C F)
    (hh : ∀ i, ConvexOn ℝ C (h i)) (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {p : ℝ}
    (hp : ∀ x ∈ C, (∀ i, h i x ≤ 0) → p ≤ F x) :
    ∃ π : ι → ℝ≥0, ∀ x ∈ C, p ≤ F x + ∑ i, (π i : ℝ) * h i x :=
  exists_forall_le_add_sum_mul_of_convexLike (hF.jointlyConvexLikeOn hh) hslater hp

/-- **Strong duality under Slater's condition**, with an attained dual optimum. If `F` and the
finitely many constraints `h i` are convex on `C`, some point of `C` satisfies every constraint
strictly, and `F` is bounded below on the feasible set, then the infimum of `F` on the feasible
set is the infimum over `C` of the Lagrangian `F x + ∑ i, π i * h i x` for some multiplier `π`. -/
theorem exists_iInf_eq_iInf_add_of_slater (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i))
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) (hbdd : BddBelow (F '' {x ∈ C | ∀ i, h i x ≤ 0})) :
    ∃ π : ι → ℝ≥0, ⨅ x : {x ∈ C | ∀ i, h i x ≤ 0}, F x =
      ⨅ x : C, (F x + ∑ i, (π i : ℝ) * h i x) := by
  obtain ⟨x₀, hx₀, hx₀h⟩ := hslater
  have hbdd' : BddBelow (range fun x : {x ∈ C | ∀ i, h i x ≤ 0} ↦ F x) := by
    rwa [← image_eq_range]
  obtain ⟨π, hπ⟩ := exists_forall_le_add_sum_mul_of_slater hF hh ⟨x₀, hx₀, hx₀h⟩
    fun x hx hxh ↦ ciInf_le hbdd' (⟨x, hx, hxh⟩ : {x ∈ C | ∀ i, h i x ≤ 0})
  have : Nonempty C := ⟨⟨x₀, hx₀⟩⟩
  have : Nonempty {x ∈ C | ∀ i, h i x ≤ 0} := ⟨⟨x₀, hx₀, fun i ↦ (hx₀h i).le⟩⟩
  refine ⟨π, le_antisymm (le_ciInf fun x ↦ hπ x x.property) ?_⟩
  apply le_ciInf
  intro x
  refine le_trans (ciInf_le ⟨⨅ x : {x ∈ C | ∀ i, h i x ≤ 0}, F x, ?_⟩ (⟨x, x.property.1⟩ : C))
    (add_sum_mul_le π x.property.2)
  rintro _ ⟨y, rfl⟩
  exact hπ y y.property

/-- **Strong duality under Slater's condition** in `EReal` [Lue69, §8.6, Theorem 1]. If `F` and
the finitely many constraints `h i` are convex on `C` and some point of `C` satisfies every
constraint strictly, the infimum of `F` on the feasible set, possibly `⊥`, is the supremum over the
multipliers `π : ι → ℝ≥0` of the infimum over `C` of the Lagrangian `F x + ∑ i, π i * h i x`. For
convex-like data, see `LMLExplore.iInf_eq_iSup_iInf_add_of_convexLike`. -/
theorem iInf_eq_iSup_iInf_add_of_slater (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i))
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) =
      ⨆ π : ι → ℝ≥0, ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) :=
  iInf_eq_iSup_iInf_add_of_convexLike (hF.jointlyConvexLikeOn hh) hslater

/-- **Complementary slackness under Slater's condition** [Lue69, §8.3, Theorem 1]. If `F` and the
finitely many constraints `h i` are convex on `C`, some point of `C` satisfies every constraint
strictly, and a feasible `x` minimizes `F` on the feasible set, then for some multiplier
`π : ι → ℝ≥0`, every `π i * h i x` vanishes and `x` minimizes the Lagrangian
`F y + ∑ i, π i * h i y` on all of `C`. For convex-like data, and the converse, see
`LMLExplore.isMinOn_iff_exists_isMinOn_add_sum_mul_of_convexLike`. -/
theorem _root_.IsMinOn.exists_mul_eq_zero_and_isMinOn_add_sum_mul_of_slater {x : X}
    (hmin : IsMinOn F {y ∈ C | ∀ i, h i y ≤ 0} x) (hx : x ∈ {y ∈ C | ∀ i, h i y ≤ 0})
    (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i)) (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ∃ π : ι → ℝ≥0, (∀ i, (π i : ℝ) * h i x = 0) ∧
      IsMinOn (fun y ↦ F y + ∑ i, (π i : ℝ) * h i y) C x := by
  obtain ⟨π, hπ, hslack⟩ := (isMinOn_iff_exists_isMinOn_add_sum_mul_of_convexLike
    (hF.jointlyConvexLikeOn hh) hslater hx.1 hx.2).1 hmin
  exact ⟨π, hslack, hπ⟩

end ConvexOn

end LMLExplore
