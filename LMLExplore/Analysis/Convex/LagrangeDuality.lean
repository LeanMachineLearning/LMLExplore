/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.EReal.Basic
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Order.Filter.Extr
public import LMLExplore.LinearAlgebra.Pi

/-!
# Lagrange duality for finitely many convex constraints

Let `C` be a convex set in a real vector space, `F : V → ℝ` convex on `C`, and finitely many
constraints `h i : V → ℝ`, `i : ι`, convex on `C`. The convex program
`minimize F x subject to x ∈ C and h i x ≤ 0 for every i` has the Lagrangian
`F x + ∑ i, π i * h i x` for multipliers `π : ι → ℝ≥0`; its infimum over `C` is the dual function
at `π`. Weak duality, that the dual function is below the primal value, holds for every problem.
Under Slater's condition, a point `x₀ ∈ C` with `h i x₀ < 0` for every `i`, strong duality
holds and the dual optimum is attained: some multiplier `π` has dual value equal to the primal
value.

No topology on `V` is used: the proof separates, in the finite-dimensional space `ℝ × (ι → ℝ)`,
the open convex set of the values `(t, u)` with `F x < t` and `h i x < u i` for some `x ∈ C`
from the point `(p, 0)`, where `p` is a lower bound of `F` on the feasible set, by Mathlib's
`geometric_hahn_banach_open_point`. The coefficients of the separating functional are
nonpositive because the set is upward closed, and Slater's condition makes the coefficient of
the first coordinate negative; dividing by it gives the multipliers.

This is the duality behind the dual formula of the minimal Kullback–Leibler divergence to a set
of laws defined by finitely many moment constraints, `KL_inf`, as the maximal expected logarithm
of a bet `1 + ∑ i, π i * g i`.

## Main statements

* `LMLExplore.exists_forall_le_add_sum_mul_of_slater`: under Slater's condition, every lower bound
  `p` of `F` on the feasible set is a lower bound of the Lagrangian on `C` for some multiplier.
* `LMLExplore.exists_iInf_eq_iInf_add_of_slater`: strong duality with an attained dual optimum,
  when the primal value is finite.
* `LMLExplore.iSup_iInf_add_le_iInf`: weak duality in `EReal`, with no hypothesis.
* `LMLExplore.iInf_eq_iSup_iInf_add_of_slater`: strong duality in `EReal`, where the primal value
  may be `⊥`.
* `IsMinOn.exists_mul_eq_zero_and_isMinOn_add_sum_mul_of_slater`: a minimizer of the program
  minimizes the Lagrangian of some multiplier over `C`, with complementary slackness
  `π i * h i x = 0`.

## References

* [S. Boyd, L. Vandenberghe, *Convex Optimization*, 2004][BV04], §5.3.2 (the proof of strong
  duality under Slater's condition, which the proof here follows) and §5.5.2 (complementary
  slackness).
* [D. G. Luenberger, *Optimization by Vector Space Methods*, 1969][Lue69], Chapter 8.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace LMLExplore

variable {V ι : Type*} {C : Set V} {F : V → ℝ} {h : ι → V → ℝ}

/-- The Lagrangian of a nonnegative multiplier is below the objective on the feasible set. -/
private lemma add_sum_mul_le [Fintype ι] (π : ι → ℝ≥0) {x : V} (hx : ∀ i, h i x ≤ 0) :
    F x + ∑ i, (π i : ℝ) * h i x ≤ F x :=
  add_le_of_nonpos_right <| Finset.sum_nonpos fun i _ ↦
    mul_nonpos_of_nonneg_of_nonpos (π i).2 (hx i)

/-- **Weak duality** in `EReal`: for every problem, the supremum over the multipliers of the
infimum of the Lagrangian over `C` is below the infimum of the objective on the feasible set. -/
theorem iSup_iInf_add_le_iInf [Fintype ι] :
    ⨆ π : ι → ℝ≥0, ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) ≤
      ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) :=
  iSup_le fun π ↦ le_iInf₂ fun x hx ↦
    (iInf₂_le x hx.1).trans (EReal.coe_le_coe_iff.2 (add_sum_mul_le π hx.2))

/-- The values `(t, u)` strictly above `(F x, fun i ↦ h i x)` for some `x ∈ C` form an open set. -/
private lemma isOpen_setOf_exists_lt [Finite ι] :
    IsOpen {z : ℝ × (ι → ℝ) | ∃ x ∈ C, F x < z.1 ∧ ∀ i, h i x < z.2 i} := by
  refine isOpen_iff_forall_mem_open.2 fun z ⟨x, hx, hzx⟩ ↦
    ⟨{z | F x < z.1 ∧ ∀ i, h i x < z.2 i}, fun z hz ↦ ⟨x, hx, hz⟩, ?_, hzx⟩
  simp only [ofPred_and, ofPred_forall]
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const
      ((continuous_apply i).comp continuous_snd))

variable [AddCommGroup V] [Module ℝ V]

/-- The values `(t, u)` strictly above `(F x, fun i ↦ h i x)` for some `x ∈ C` form a convex set
when `F` and the `h i` are convex on `C`. -/
private lemma convex_setOf_exists_lt (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i)) :
    Convex ℝ {z : ℝ × (ι → ℝ) | ∃ x ∈ C, F x < z.1 ∧ ∀ i, h i x < z.2 i} := by
  refine convex_iff_openSegment_subset.2 ?_
  rintro z ⟨x, hx, hFx, hhx⟩ z' ⟨x', hx', hFx', hhx'⟩ _ ⟨a, b, ha, hb, hab, rfl⟩
  have key {G : V → ℝ} (hG : ConvexOn ℝ C G) {t t' : ℝ} (ht : G x < t) (ht' : G x' < t') :
      G (a • x + b • x') < a * t + b * t' := by
    simpa using (hG.openSegment_subset_strict_epigraph (x, t) (x', t') ⟨hx, ht⟩
      ⟨hx', ht'.le⟩ ⟨a, b, ha, hb, hab, rfl⟩).2
  exact ⟨a • x + b • x', hF.1 hx hx' ha.le hb.le hab, by simpa using key hF hFx hFx',
    fun i ↦ by simpa using key (hh i) (hhx i) (hhx' i)⟩

/-- Under Slater's condition, a lower bound `p` of `F` on the feasible set gives a continuous
linear functional on `ℝ × (ι → ℝ)`, negative on the first coordinate vector and nonpositive on
the others, that is at most its value at `(p, 0)` at every `(F x, fun i ↦ h i x)` with `x ∈ C`. -/
private lemma exists_strongDual_le_of_slater [Finite ι] [DecidableEq ι] (hF : ConvexOn ℝ C F)
    (hh : ∀ i, ConvexOn ℝ C (h i)) (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {p : ℝ}
    (hp : ∀ x ∈ C, (∀ i, h i x ≤ 0) → p ≤ F x) :
    ∃ f : StrongDual ℝ (ℝ × (ι → ℝ)), f (1, 0) < 0 ∧ (∀ i, f (0, Pi.single i 1) ≤ 0) ∧
      ∀ x ∈ C, f (F x, fun i ↦ h i x) ≤ f (p, 0) := by
  have := Fintype.ofFinite ι
  obtain ⟨x₀, hx₀, hx₀h⟩ := hslater
  set A : Set (ℝ × (ι → ℝ)) := {z | ∃ x ∈ C, F x < z.1 ∧ ∀ i, h i x < z.2 i}
  -- The point `(p, 0)` is not in `A`, since `p` is below `F` on the feasible set.
  have hpA : ((p, 0) : ℝ × (ι → ℝ)) ∉ A := by
    rintro ⟨x, hx, hFx, hhx⟩
    exact (hp x hx fun i ↦ (hhx i).le).not_gt hFx
  obtain ⟨f, hf⟩ :=
    geometric_hahn_banach_open_point (convex_setOf_exists_lt hF hh) isOpen_setOf_exists_lt hpA
  -- The functional is nonpositive on the nonnegative vectors, since `A` is upward closed.
  have hz₀ : ((F x₀ + 1, 0) : ℝ × (ι → ℝ)) ∈ A := ⟨x₀, hx₀, by simp, by simpa using hx₀h⟩
  have hf_nonpos (w : ℝ × (ι → ℝ)) (hw₁ : 0 ≤ w.1) (hw₂ : ∀ i, 0 ≤ w.2 i) : f w ≤ 0 := by
    by_contra! hw
    set s := |f (p, 0) - f (F x₀ + 1, 0)| / f w
    have hs : 0 ≤ s := by positivity
    have hmem : ((F x₀ + 1, 0) : ℝ × (ι → ℝ)) + s • w ∈ A :=
      ⟨x₀, hx₀, by
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linarith [mul_nonneg hs hw₁],
        fun i ↦ (hx₀h i).trans_le (by simpa using mul_nonneg hs (hw₂ i))⟩
    have hlt := hf _ hmem
    rw [map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hw.ne'] at hlt
    linarith [le_abs_self (f (p, 0) - f (F x₀ + 1, 0))]
  refine ⟨f, ?_, fun i ↦ hf_nonpos _ le_rfl fun j ↦
    (Pi.single_nonneg.2 zero_le_one : (0 : ι → ℝ) ≤ Pi.single i 1) j, fun x hx ↦ ?_⟩
  -- Slater's condition makes the coefficient of the first coordinate negative.
  · refine (hf_nonpos (1, 0) zero_le_one fun _ ↦ le_rfl).lt_of_ne fun hc0 ↦ ?_
    have h0 := hf _ hz₀
    have hdec := (f : ℝ × (ι → ℝ) →ₗ[ℝ] ℝ).prod_pi_apply_eq_sum_univ
    simp only [ContinuousLinearMap.coe_coe] at hdec
    rw [hdec (F x₀ + 1), hdec p, hc0] at h0
    simp at h0
  -- At `(F x, fun i ↦ h i x)`, by continuity from the points of `A` just above.
  have hcont : Continuous fun ε : ℝ ↦ f (F x + ε, fun i ↦ h i x + ε) :=
    f.continuous.comp (by fun_prop)
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [add_zero] at hlim
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) ↦
    (hf _ ⟨x, hx, by linarith, fun i ↦ by simpa using hε⟩).le)

variable [Fintype ι]

/-- **Lagrange multipliers under Slater's condition.** If `F` and the finitely many constraints
`h i` are convex on `C`, some point of `C` satisfies every constraint strictly, and `p` is below
`F` on the feasible set `{x ∈ C | ∀ i, h i x ≤ 0}`, then some multiplier `π : ι → ℝ≥0` makes `p`
a lower bound of the Lagrangian `F x + ∑ i, π i * h i x` on all of `C`. -/
theorem exists_forall_le_add_sum_mul_of_slater (hF : ConvexOn ℝ C F)
    (hh : ∀ i, ConvexOn ℝ C (h i)) (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) {p : ℝ}
    (hp : ∀ x ∈ C, (∀ i, h i x ≤ 0) → p ≤ F x) :
    ∃ π : ι → ℝ≥0, ∀ x ∈ C, p ≤ F x + ∑ i, (π i : ℝ) * h i x := by
  classical
  obtain ⟨f, hc, hd, hf⟩ := exists_strongDual_le_of_slater hF hh hslater hp
  -- Dividing the coefficients of `f` by the negative first one gives the multipliers.
  refine ⟨fun i ↦ ⟨f (0, Pi.single i 1) / f (1, 0), div_nonneg_of_nonpos (hd i) hc.le⟩,
    fun x hx ↦ (mul_le_mul_left_of_neg hc).1 ?_⟩
  have hle := hf x hx
  have hdec := (f : ℝ × (ι → ℝ) →ₗ[ℝ] ℝ).prod_pi_apply_eq_sum_univ
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at hdec
  rw [hdec (F x), hdec p] at hle
  have hc' : f (1, 0) ≠ 0 := hc.ne
  calc f (1, 0) * (F x + ∑ i, (f (0, Pi.single i 1) / f (1, 0)) * h i x)
      = f (1, 0) * F x + ∑ i, f (0, Pi.single i 1) * h i x := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦ by field_simp
    _ ≤ f (1, 0) * p := by simpa [mul_comm] using hle

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
  refine ⟨π, le_antisymm (le_ciInf fun x ↦ hπ x x.2) ?_⟩
  apply le_ciInf
  intro x
  refine le_trans (ciInf_le ⟨⨅ x : {x ∈ C | ∀ i, h i x ≤ 0}, F x, ?_⟩ (⟨x, x.2.1⟩ : C))
    (add_sum_mul_le π x.2.2)
  rintro _ ⟨y, rfl⟩
  exact hπ y y.2

/-- **Strong duality under Slater's condition** in `EReal`. If `F` and the finitely many
constraints `h i` are convex on `C` and some point of `C` satisfies every constraint strictly,
the infimum of `F` on the feasible set, possibly `⊥`, is the supremum over the multipliers
`π : ι → ℝ≥0` of the infimum over `C` of the Lagrangian `F x + ∑ i, π i * h i x`. -/
theorem iInf_eq_iSup_iInf_add_of_slater (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i))
    (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) =
      ⨆ π : ι → ℝ≥0, ⨅ x ∈ C, ((F x + ∑ i, (π i : ℝ) * h i x : ℝ) : EReal) := by
  refine le_antisymm ?_ iSup_iInf_add_le_iInf
  set P := ⨅ x ∈ {x ∈ C | ∀ i, h i x ≤ 0}, (F x : EReal) with hP
  obtain hbot | hbot := eq_or_ne P ⊥
  · rw [hbot]
    exact bot_le
  obtain ⟨x₀, hx₀, hx₀h⟩ := hslater
  have htop : P ≠ ⊤ :=
    ((iInf₂_le x₀ ⟨hx₀, fun i ↦ (hx₀h i).le⟩).trans_lt (EReal.coe_lt_top (F x₀))).ne
  obtain ⟨π, hπ⟩ := exists_forall_le_add_sum_mul_of_slater hF hh ⟨x₀, hx₀, hx₀h⟩
    (p := P.toReal) fun x hx hxh ↦ by
      rw [← EReal.coe_le_coe_iff, EReal.coe_toReal htop hbot]
      exact iInf₂_le x ⟨hx, hxh⟩
  refine le_iSup_of_le π (le_iInf₂ fun x hx ↦ ?_)
  rw [← EReal.coe_toReal htop hbot]
  exact EReal.coe_le_coe_iff.2 (hπ x hx)

end LMLExplore

/-- **Complementary slackness under Slater's condition.** If `F` and the finitely many
constraints `h i` are convex on `C`, some point of `C` satisfies every constraint strictly, and a
feasible `x` minimizes `F` on the feasible set, then for some multiplier `π : ι → ℝ≥0`, every
`π i * h i x` vanishes and `x` minimizes the Lagrangian `F y + ∑ i, π i * h i y` on all of `C`. -/
theorem IsMinOn.exists_mul_eq_zero_and_isMinOn_add_sum_mul_of_slater {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [Fintype ι] {C : Set V} {F : V → ℝ} {h : ι → V → ℝ} {x : V}
    (hmin : IsMinOn F {y ∈ C | ∀ i, h i y ≤ 0} x) (hx : x ∈ {y ∈ C | ∀ i, h i y ≤ 0})
    (hF : ConvexOn ℝ C F) (hh : ∀ i, ConvexOn ℝ C (h i)) (hslater : ∃ x₀ ∈ C, ∀ i, h i x₀ < 0) :
    ∃ π : ι → ℝ≥0, (∀ i, (π i : ℝ) * h i x = 0) ∧
      IsMinOn (fun y ↦ F y + ∑ i, (π i : ℝ) * h i y) C x := by
  obtain ⟨π, hπ⟩ := LMLExplore.exists_forall_le_add_sum_mul_of_slater hF hh hslater
    fun y hy hyh ↦ isMinOn_iff.1 hmin y ⟨hy, hyh⟩
  have hnonpos (i : ι) : (π i : ℝ) * h i x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (π i).2 (hx.2 i)
  have hsum : ∑ i, (π i : ℝ) * h i x = 0 :=
    le_antisymm (Finset.sum_nonpos fun i _ ↦ hnonpos i) (by linarith [hπ x hx.1])
  refine ⟨π, fun i ↦ (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hnonpos i).1 hsum i
    (Finset.mem_univ i), isMinOn_iff.2 fun y hy ↦ ?_⟩
  rw [hsum, add_zero]
  exact hπ y hy
