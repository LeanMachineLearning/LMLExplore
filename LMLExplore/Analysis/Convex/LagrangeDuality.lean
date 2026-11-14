/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.EReal.Basic

/-!
# Lagrange duality for finitely many convex constraints

Consider the convex program of minimizing `F x` over the points `x` of a convex set `C` that
satisfy finitely many convex constraints `h i x ≤ 0`, `i : ι`. Its Lagrangian is
`F x + ∑ i, π i * h i x` for multipliers `π : ι → ℝ≥0`, and its dual function is the infimum of the
Lagrangian over all of `C`, with the constraints dropped. Under **Slater's condition**, that some
`x₀ ∈ C` satisfies every constraint strictly, there is no duality gap: the value of the program is
the maximum over `π` of the dual function, and the minimizers of the program are the points that
minimize the Lagrangian of an optimal multiplier with complementary slackness [Lue69, §8.3,
Theorem 1; §8.6, Theorem 1].

The existence of multipliers only needs `F` and `h` to be jointly *convex-like* on `C` in the sense
of Fan [Fan53]: for `x, y ∈ C` and weights `a, b`, some `z ∈ C` has `F z` and every `h i z` below
the corresponding convex combinations of the values at `x` and `y`. It is stated in that form in
`LMLExplore.exists_forall_le_add_sum_of_convexLike`, which needs no linear structure on the domain
and so applies to convex sets of probability measures, which carry no real scalar multiplication.
Weak duality holds with no hypothesis; strong duality and the saddle point characterization are
stated for convex functions on a convex set.

Values of the dual function are taken in `EReal`: the real infimum of a Lagrangian unbounded below
is the junk value `0`, for which weak duality fails.

## Main statements

* `LMLExplore.exists_forall_le_add_sum_of_convexLike`: under Slater's condition, every lower bound
  of the objective on the feasible set is a lower bound of the Lagrangian on all of `C` for some
  multiplier, for convex-like data on any type.
* `ConvexOn.exists_forall_le_add_sum_of_slater`: the same for convex functions on a convex set.
* `LMLExplore.iInf_add_sum_le_iInf`: weak duality, for every multiplier and with no hypothesis.
* `ConvexOn.exists_iInf_eq_iInf_add_of_slater`: strong duality with an optimal multiplier.
* `ConvexOn.iInf_eq_iSup_iInf_add_of_slater`: strong duality, the value of the program is the
  supremum of the dual function.
* `ConvexOn.isMinOn_iff_exists_isMinOn_add_sum_of_slater`: the saddle point characterization of the
  minimizers, by a multiplier for which they minimize the Lagrangian with complementary slackness.

## Implementation notes

The multiplier is produced by separating the point `(m, 0)`, for a lower bound `m` of `F` on the
feasible set, from the open convex set of the `v : Option ι → ℝ` lying strictly above
`(F x, h · x)` for some `x ∈ C`, with Mathlib's `geometric_hahn_banach_open_point`; Slater's
condition makes the coefficient of the objective in the separating functional nonzero.

## References

* [Lue69] D. G. Luenberger, *Optimization by Vector Space Methods*, Wiley, 1969, Chapter 8.
* [Fan53] K. Fan, *Minimax theorems*, Proc. Natl. Acad. Sci. USA 39 (1953), 42–47.
-/

public section

open Filter Set Topology
open scoped NNReal

variable {X ι : Type*} {C : Set X} {F : X → ℝ} {h : ι → X → ℝ}

namespace LMLExplore

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

/-- A convex combination of two strict inequalities is strict. -/
private lemma combo_lt_combo {a b s t u w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hs : s < u) (ht : t < w) : a * s + b * t < a * u + b * w := by
  rcases ha.eq_or_lt with rfl | ha
  · obtain rfl : b = 1 := by linarith
    linarith
  · nlinarith [mul_lt_mul_of_pos_left hs ha, mul_le_mul_of_nonneg_left ht.le hb]

private lemma convex_strictEpigraph
    (hconv : ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ z ∈ C, F z ≤ a * F x + b * F y ∧ ∀ i, h i z ≤ a * h i x + b * h i y) :
    Convex ℝ (strictEpigraph C F h) := by
  rintro v ⟨x, hx, hxv⟩ w ⟨y, hy, hyw⟩ a b ha hb hab
  obtain ⟨z, hz, hFz, hhz⟩ := hconv x hx y hy a b ha hb hab
  refine ⟨z, hz, fun j ↦ ?_⟩
  have hz' : objConstr F h j z ≤ a * objConstr F h j x + b * objConstr F h j y := by
    cases j <;> simp [objConstr, hFz, hhz]
  simpa using hz'.trans_lt (combo_lt_combo ha hb hab (hxv j) (hyw j))

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

/-- **Fritz John multipliers** for convex-like data: if `m` is a lower bound of `F` on the feasible
set and `C` is nonempty, some nonzero nonpositive `c : Option ι → ℝ` has
`c none * F x + ∑ i, c (some i) * h i x ≤ c none * m` on `C`. -/
private lemma exists_fritzJohn [Fintype ι]
    (hconv : ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ z ∈ C, F z ≤ a * F x + b * F y ∧ ∀ i, h i z ≤ a * h i x + b * h i y)
    {x₀ : X} (hx₀ : x₀ ∈ C) {m : ℝ} (hm : ∀ x ∈ C, (∀ i, h i x ≤ 0) → m ≤ F x) :
    ∃ c : Option ι → ℝ, c ≠ 0 ∧ (∀ j, c j ≤ 0) ∧
      ∀ x ∈ C, c none * F x + ∑ i, c (some i) * h i x ≤ c none * m := by
  classical
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
  -- The coefficients `c j` of `f` in the standard basis.
  let e : Option ι → Option ι → ℝ := fun j k ↦ if j = k then 1 else 0
  let c : Option ι → ℝ := fun j ↦ f (e j)
  have hfc (v : Option ι → ℝ) : f v = c none * v none + ∑ i, c (some i) * v (some i) := by
    rw [← Fintype.sum_option (fun j ↦ c j * v j)]
    simpa [c, e, smul_eq_mul, mul_comm] using
      LinearMap.pi_apply_eq_sum_univ (f : (Option ι → ℝ) →ₗ[ℝ] ℝ) v
  refine ⟨c, fun hc ↦ ?_, fun j ↦ apply_nonpos_of_forall_lt hf ha₀ fun k ↦ by
    by_cases hjk : j = k <;> simp [e, hjk], fun x hx ↦ ?_⟩
  · -- `f` is nonzero, since it is strictly below `f p` somewhere.
    have := hf _ ha₀
    simp [hfc, hc] at this
  · simpa [hfc, objConstr, p] using apply_le_of_forall_lt hf hx

/-- **Lagrange multipliers under Slater's condition** [Lue69, §8.3, Theorem 1], for convex-like
data [Fan53]. Let `F` and finitely many `h i` be jointly convex-like on a set `C`: for `x, y ∈ C`
and weights `a, b ≥ 0` with `a + b = 1`, some `z ∈ C` has `F z` and every `h i z` below the
corresponding convex combinations of the values at `x` and `y`. If some `x₀ ∈ C` satisfies
`h i x₀ < 0` for every `i` and `m` is a lower bound of `F` on the feasible set
`{x ∈ C | ∀ i, h i x ≤ 0}`, then some multiplier `π : ι → ℝ≥0` makes `m` a lower bound of the
Lagrangian `F x + ∑ i, π i * h i x` on all of `C`.

No vector space structure on `X` is needed: this applies to convex sets of measures. For convex
functions on a convex set, see `ConvexOn.exists_forall_le_add_sum_of_slater`.
-/
theorem exists_forall_le_add_sum_of_convexLike [Fintype ι]
    (hconv : ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ z ∈ C, F z ≤ a * F x + b * F y ∧ ∀ i, h i z ≤ a * h i x + b * h i y)
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {m : ℝ}
    (hm : ∀ x ∈ C, (∀ i, h i x ≤ 0) → m ≤ F x) :
    ∃ π : ι → ℝ≥0, ∀ x ∈ C, m ≤ F x + ∑ i, (π i : ℝ) * h i x := by
  obtain ⟨x₀, hx₀, hx₀h⟩ := hslater
  obtain ⟨c, hc, hc_nonpos, hcx⟩ := exists_fritzJohn hconv hx₀ hm
  -- By Slater's condition the coefficient of the objective is negative: otherwise the terms
  -- `c (some i) * h i x₀ ≥ 0` would have a nonpositive sum, so every coefficient would vanish.
  have hc_neg : c none < 0 := by
    refine (hc_nonpos none).lt_of_ne fun h0 ↦ hc ?_
    have hsum := hcx x₀ hx₀
    rw [h0, zero_mul, zero_mul, zero_add] at hsum
    have hterm (i : ι) : 0 ≤ c (some i) * h i x₀ :=
      mul_nonneg_of_nonpos_of_nonpos (hc_nonpos _) (hx₀h i).le
    have hzero (i : ι) : c (some i) = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hterm i).1
        (le_antisymm hsum (Finset.sum_nonneg fun i _ ↦ hterm i)) i (Finset.mem_univ _)
      exact (mul_eq_zero.1 this).resolve_right (hx₀h i).ne
    ext (_ | i)
    exacts [h0, hzero i]
  -- Normalize the coefficient of the objective to `1`.
  have hc0 : c none ≠ 0 := hc_neg.ne
  have hL (x : X) (hx : x ∈ C) : m ≤ F x + ∑ i, c (some i) / c none * h i x := by
    have hmul : c none * (F x + ∑ i, c (some i) / c none * h i x) =
        c none * F x + ∑ i, c (some i) * h i x := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      field_simp
    rw [← mul_le_mul_left_of_neg hc_neg, hmul]
    exact hcx x hx
  exact ⟨fun i ↦ ⟨c (some i) / c none, div_nonneg_of_nonpos (hc_nonpos _) hc_neg.le⟩, hL⟩

/-- **Weak duality.** For every multiplier `π : ι → ℝ≥0`, the infimum over `C` of the Lagrangian
`F x + ∑ i, π i * h i x` is at most the infimum of `F` over the feasible set
`{x ∈ C | ∀ i, h i x ≤ 0}`, with values in `EReal`. -/
theorem iInf_add_sum_le_iInf [Fintype ι] (π : ι → ℝ≥0) :
    ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) ≤
      ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) := by
  refine le_iInf₂ fun x ⟨hx, hxh⟩ ↦ (iInf₂_le x hx).trans (EReal.coe_le_coe_iff.2 ?_)
  have : ∑ i, (π i : ℝ) * h i x ≤ 0 :=
    Finset.sum_nonpos fun i _ ↦ mul_nonpos_of_nonneg_of_nonpos (π i).2 (hxh i)
  linarith

end LMLExplore

namespace ConvexOn

open LMLExplore

variable [Fintype ι] {V : Type*} [AddCommMonoid V] [SMul ℝ V] {C : Set V} {F : V → ℝ}
  {h : ι → V → ℝ}

/-- **Lagrange multipliers under Slater's condition** [Lue69, §8.3, Theorem 1]. Let `F` and
finitely many `h i` be convex on a convex set `C`. If some `x₀ ∈ C` satisfies
`h i x₀ < 0` for every `i` and `m` is a lower bound of `F` on the feasible set
`{x ∈ C | ∀ i, h i x ≤ 0}`, then some multiplier `π : ι → ℝ≥0` makes `m` a lower bound of the
Lagrangian `F x + ∑ i, π i * h i x` on all of `C`. -/
theorem exists_forall_le_add_sum_of_slater (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i))
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {m : ℝ}
    (hm : ∀ x ∈ C, (∀ i, h i x ≤ 0) → m ≤ F x) :
    ∃ π : ι → ℝ≥0, ∀ x ∈ C, m ≤ F x + ∑ i, (π i : ℝ) * h i x :=
  exists_forall_le_add_sum_of_convexLike (fun x hx y hy a b ha hb hab ↦
    ⟨a • x + b • y, hF.1 hx hy ha hb hab, by simpa using hF.2 hx hy ha hb hab,
      fun i ↦ by simpa using (hh i).2 hx hy ha hb hab⟩) hslater hm

/-- **Strong Lagrange duality under Slater's condition** [Lue69, §8.6, Theorem 1]. For `F` and
finitely many `h i` convex on a convex set `C`, if some `x₀ ∈ C` satisfies `h i x₀ < 0` for every
`i`, then some multiplier `π : ι → ℝ≥0` has dual value equal to the value of the program: the
infimum over `C` of the Lagrangian `F x + ∑ i, π i * h i x` is the infimum of `F` over
`{x ∈ C | ∀ i, h i x ≤ 0}`. Values are in `EReal`, so no boundedness is assumed: when `F` is
unbounded below on the feasible set, both sides are `⊥`. -/
theorem exists_iInf_eq_iInf_add_of_slater (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i))
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ∃ π : ι → ℝ≥0, ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) =
      ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) := by
  set P := ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal)
  obtain ⟨x₀, hx₀, hx₀h⟩ := hslater
  rcases eq_or_ne P ⊥ with hP | hP
  · exact ⟨0, hP.trans (le_bot_iff.1 (hP ▸ iInf_add_sum_le_iInf 0)).symm⟩
  have hPtop : P ≠ ⊤ :=
    ((iInf₂_le x₀ ⟨hx₀, fun i ↦ (hx₀h i).le⟩).trans_lt (EReal.coe_lt_top _)).ne
  obtain ⟨π, hπ⟩ := hF.exists_forall_le_add_sum_of_slater hh ⟨x₀, hx₀, hx₀h⟩ (m := P.toReal)
    fun x hx hxh ↦ by
      rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hPtop hP]
      exact iInf₂_le x ⟨hx, hxh⟩
  refine ⟨π, le_antisymm ?_ (iInf_add_sum_le_iInf π)⟩
  rw [← EReal.coe_toReal hPtop hP]
  exact le_iInf₂ fun x hx ↦ EReal.coe_le_coe_iff.2 (hπ x hx)

/-- **Strong Lagrange duality under Slater's condition** [Lue69, §8.6, Theorem 1]. For `F` and
finitely many `h i` convex on a convex set `C`, if some `x₀ ∈ C` satisfies `h i x₀ < 0` for every
`i`, then the infimum of `F` over `{x ∈ C | ∀ i, h i x ≤ 0}` is the supremum over multipliers
`π : ι → ℝ≥0` of the infimum over `C` of the Lagrangian `F x + ∑ i, π i * h i x`, in `EReal`. The
supremum is attained (`ConvexOn.exists_iInf_eq_iInf_add_of_slater`). -/
theorem iInf_eq_iSup_iInf_add_of_slater (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i))
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) =
      ⨆ π : ι → ℝ≥0, ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) := by
  obtain ⟨π, hπ⟩ := hF.exists_iInf_eq_iInf_add_of_slater hh hslater
  exact le_antisymm (hπ.le.trans (le_iSup_of_le π le_rfl)) (iSup_le iInf_add_sum_le_iInf)

/-- **Saddle point characterization of the minimizers** [Lue69, §8.3, Theorem 1; §8.4].
For `F` and finitely many `h i` convex on a convex set `C`, with some `x₀ ∈ C` satisfying
`h i x₀ < 0` for every `i`, a feasible point `x` minimizes `F` over `{y ∈ C | ∀ i, h i y ≤ 0}`
exactly when some multiplier `π : ι → ℝ≥0` makes `x` a minimizer over `C` of the Lagrangian
`F y + ∑ i, π i * h i y`, with complementary slackness `π i * h i x = 0` for every `i`. -/
theorem isMinOn_iff_exists_isMinOn_add_sum_of_slater (hF : ConvexOn ℝ C F)
    (hh : ∀ i, ConvexOn ℝ C (h i)) (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {x : V} (hx : x ∈ C)
    (hxh : ∀ i, h i x ≤ 0) :
    IsMinOn F {y ∈ C | ∀ i, h i y ≤ 0} x ↔
      ∃ π : ι → ℝ≥0, IsMinOn (fun y ↦ F y + ∑ i, (π i : ℝ) * h i y) C x ∧
        ∀ i, (π i : ℝ) * h i x = 0 := by
  have hterm (π : ι → ℝ≥0) (y : V) (hyh : ∀ i, h i y ≤ 0) (i : ι) : (π i : ℝ) * h i y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (π i).2 (hyh i)
  constructor
  · intro hmin
    obtain ⟨π, hπ⟩ := hF.exists_forall_le_add_sum_of_slater hh hslater (m := F x)
      fun y hy hyh ↦ isMinOn_iff.1 hmin y ⟨hy, hyh⟩
    -- At `x` the sum of the nonpositive terms `π i * h i x` is nonnegative, hence each is zero.
    have hsum : ∑ i, (π i : ℝ) * h i x = 0 :=
      le_antisymm (Finset.sum_nonpos fun i _ ↦ hterm π x hxh i) (by linarith [hπ x hx])
    have hslack (i : ι) : (π i : ℝ) * h i x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hterm π x hxh i).1 hsum i (Finset.mem_univ _)
    exact ⟨π, isMinOn_iff.2 fun y hy ↦ by simpa [hsum] using hπ y hy, hslack⟩
  · rintro ⟨π, hmin, hslack⟩
    refine isMinOn_iff.2 fun y ⟨hy, hyh⟩ ↦ ?_
    have hle := isMinOn_iff.1 hmin y hy
    simp only [hslack, Finset.sum_const_zero, add_zero] at hle
    linarith [Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) ↦ hterm π y hyh i]

end ConvexOn
