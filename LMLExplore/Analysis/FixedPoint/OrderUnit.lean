/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Order units, Blackwell's conditions and topical maps

Let `E` be an ordered real vector space. An element `e : E` is an *order unit* if every `x : E`
lies in an order interval `[-c • e, c • e]` with `c ≥ 0`. It defines the order-unit seminorm
`‖x‖_e = inf {c ≥ 0 | -c • e ≤ x ≤ c • e}` (a norm when the order is Archimedean) and the
oscillation `osc_e x = inf {b - a | a ≤ b, a • e ≤ x ≤ b • e}`, which is invariant under adding
multiples of `e`.

*Blackwell's sufficient conditions* [Bla65] say that a monotone map `T : E → E` with
`T (x + c • e) ≤ T x + (γ * c) • e` for all `x` and `c ≥ 0` is `γ`-Lipschitz for `‖·‖_e`. This is
how the Bellman operators of dynamic programming are shown to be contractions: they are monotone,
and adding a constant `c` to a value function adds at most `γ * c` to its image.

A map is *topical* [GG04] if it is monotone and commutes with adding multiples of `e`. Topical maps
(undiscounted Bellman operators, max-plus maps) are nonexpansive for both `‖·‖_e` and `osc_e`.

On `ι → ℝ` with `ι` finite and the pointwise order, `1` is an order unit whose order-unit norm is
the sup norm, so Blackwell's conditions give a `LipschitzWith` statement to which Mathlib's
`ContractingWith` applies. A positive weight `w` is an order unit whose order-unit norm is the
weighted sup norm `⨆ i, |x i| / w i`, and the oscillation for `1` is `max x - min x`.

## Main definitions

* `LMLExplore.IsOrderUnit e`: every element lies in `[-c • e, c • e]` for some `c ≥ 0`.
* `LMLExplore.orderUnitNorm e x`: the order-unit seminorm `‖x‖_e`.
* `LMLExplore.orderUnitOsc e x`: the oscillation `osc_e x`.
* `LMLExplore.IsTopical e T`: `T` is monotone and `T (x + c • e) = T x + c • e`.

## Main statements

* `LMLExplore.orderUnitNorm_smul`, `LMLExplore.orderUnitNorm_add_le`: the order-unit norm of an
  order unit is a seminorm.
* `LMLExplore.orderUnitOsc_add_smul`, `LMLExplore.orderUnitOsc_le_two_mul_orderUnitNorm`: the
  oscillation is invariant under adding multiples of `e` and bounded by twice the norm.
* `LMLExplore.orderUnitNorm_sub_le_of_monotone_of_add_smul_le`: Blackwell's sufficient conditions.
* `LMLExplore.IsTopical.orderUnitNorm_sub_le`, `LMLExplore.IsTopical.orderUnitOsc_sub_le`:
  topical maps are nonexpansive for the order-unit norm and for the oscillation.
* `LMLExplore.orderUnitNorm_one_eq_norm`: on `ι → ℝ`, the order-unit norm of `1` is the sup norm.
* `LMLExplore.lipschitzWith_of_monotone_of_add_smul_le`: Blackwell's conditions in a normed group
  whose norm is the order-unit norm, and `LMLExplore.lipschitzWith_of_monotone_of_add_const_le`
  their case `ι → ℝ`.
* `LMLExplore.orderUnitNorm_eq_iSup_abs_div`: the order-unit norm of a positive weight is the
  weighted sup norm, and `LMLExplore.iSup_abs_sub_div_le_of_monotone_of_add_smul_le` is
  Blackwell's bound for it.
* `LMLExplore.orderUnitOsc_one_eq_sup'_sub_inf'`: on `ι → ℝ`, the oscillation of `1` is
  `max x - min x`.
* `LMLExplore.isTopical_one_iff`: topical maps for `1` commute with adding constant functions.
* `LMLExplore.isTopical_one_sup'_add`: max-plus maps are topical.

## References

* [D. Blackwell, *Discounted dynamic programming*, 1965][Bla65]
* [S. Gaubert and J. Gunawardena, *The Perron–Frobenius theorem for homogeneous, monotone
  functions*, 2004][GG04], §1
-/

public section

open Set

/-- Multiples of the unit `1 : ι → R` are the constant functions. -/
lemma Pi.smul_one_eq_const {ι R : Type*} [MulOneClass R] (c : R) :
    c • (1 : ι → R) = fun _ ↦ c :=
  funext fun _ ↦ by simp

namespace LMLExplore

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [Module ℝ E] {e x y : E} {c : ℝ}

/-! ### Order units, the order-unit norm and the oscillation -/

/-- An *order unit* of an ordered real vector space: every element lies in an order interval
`[-c • e, c • e]` with `c ≥ 0`. -/
def IsOrderUnit (e : E) : Prop := ∀ x : E, ∃ c : ℝ, 0 ≤ c ∧ x ∈ Icc (-(c • e)) (c • e)

lemma isOrderUnit_def : IsOrderUnit e ↔ ∀ x : E, ∃ c : ℝ, 0 ≤ c ∧ x ∈ Icc (-(c • e)) (c • e) :=
  (Iff.rfl)

/-- The order-unit norm `‖x‖_e = inf {c ≥ 0 | -c • e ≤ x ≤ c • e}`. When `e` is an order unit it
is a seminorm (`orderUnitNorm_smul`, `orderUnitNorm_add_le`); it is a norm exactly when the order
is moreover almost Archimedean (`-ε • e ≤ x ≤ ε • e` for every `ε > 0` forces `x = 0`), for
instance when it is Archimedean. If `x` lies in no interval `[-c • e, c • e]` (which can only
happen when `e` is not an order unit), it takes the junk value `sInf ∅ = 0`. On `ι → ℝ` with `ι`
finite and a positive weight `e`, it is the weighted sup norm (`orderUnitNorm_eq_iSup_abs_div`). -/
noncomputable def orderUnitNorm (e x : E) : ℝ := sInf {c : ℝ | 0 ≤ c ∧ x ∈ Icc (-(c • e)) (c • e)}

lemma orderUnitNorm_def (e x : E) :
    orderUnitNorm e x = sInf {c : ℝ | 0 ≤ c ∧ x ∈ Icc (-(c • e)) (c • e)} := (rfl)

/-- The oscillation `osc_e x = inf {b - a | a ≤ b, a • e ≤ x ≤ b • e}`, written with `d = b - a`.
It is meaningful when `e` is an order unit; if `x` lies in no interval `[a • e, (a + d) • e]`
(which can only happen when `e` is not an order unit), it takes the junk value `sInf ∅ = 0`. On
`ι → ℝ` with `ι` finite and nonempty, `osc_1 x = max x - min x`
(`orderUnitOsc_one_eq_sup'_sub_inf'`). -/
noncomputable def orderUnitOsc (e x : E) : ℝ :=
  sInf {d : ℝ | 0 ≤ d ∧ ∃ a : ℝ, x ∈ Icc (a • e) ((a + d) • e)}

lemma orderUnitOsc_def (e x : E) :
    orderUnitOsc e x = sInf {d : ℝ | 0 ≤ d ∧ ∃ a : ℝ, x ∈ Icc (a • e) ((a + d) • e)} := (rfl)

lemma orderUnitNorm_nonneg (e x : E) : 0 ≤ orderUnitNorm e x :=
  Real.sInf_nonneg fun _ hc ↦ hc.1

lemma orderUnitOsc_nonneg (e x : E) : 0 ≤ orderUnitOsc e x :=
  Real.sInf_nonneg fun _ hd ↦ hd.1

/-- Every bound `c ≥ 0` with `-c • e ≤ x ≤ c • e` bounds the order-unit norm of `x`. -/
lemma orderUnitNorm_le (hc : 0 ≤ c) (hx : x ∈ Icc (-(c • e)) (c • e)) : orderUnitNorm e x ≤ c :=
  csInf_le ⟨0, fun _ hc ↦ hc.1⟩ ⟨hc, hx⟩

/-- A lower bound of every `c ≥ 0` with `-c • e ≤ x ≤ c • e` is at most the order-unit norm. -/
lemma le_orderUnitNorm {r : ℝ} (he : IsOrderUnit e)
    (h : ∀ c, 0 ≤ c → x ∈ Icc (-(c • e)) (c • e) → r ≤ c) : r ≤ orderUnitNorm e x :=
  le_csInf (he x) fun c hc ↦ h c hc.1 hc.2

/-- Every `d ≥ 0` with `a • e ≤ x ≤ (a + d) • e` for some `a` bounds the oscillation of `x`. -/
lemma orderUnitOsc_le {a d : ℝ} (hd : 0 ≤ d) (hx : x ∈ Icc (a • e) ((a + d) • e)) :
    orderUnitOsc e x ≤ d :=
  csInf_le ⟨0, fun _ hd ↦ hd.1⟩ ⟨hd, a, hx⟩

/-- For an order unit `e`, every element lies in an interval `[a • e, (a + d) • e]` with `d ≥ 0`. -/
lemma IsOrderUnit.exists_mem_Icc_smul (he : IsOrderUnit e) (x : E) :
    ∃ d : ℝ, 0 ≤ d ∧ ∃ a : ℝ, x ∈ Icc (a • e) ((a + d) • e) := by
  obtain ⟨c, hc, hx⟩ := he x
  exact ⟨2 * c, by positivity, -c, by rwa [neg_smul, show -c + 2 * c = c by ring]⟩

/-- A lower bound of every `d ≥ 0` with `a • e ≤ x ≤ (a + d) • e` for some `a` is at most the
oscillation. -/
lemma le_orderUnitOsc {r : ℝ} (he : IsOrderUnit e)
    (h : ∀ d, 0 ≤ d → ∀ a : ℝ, x ∈ Icc (a • e) ((a + d) • e) → r ≤ d) : r ≤ orderUnitOsc e x :=
  le_csInf (he.exists_mem_Icc_smul x) fun d ⟨hd, a, hx⟩ ↦ h d hd a hx

@[simp]
lemma orderUnitNorm_zero (e : E) : orderUnitNorm e 0 = 0 :=
  (orderUnitNorm_le le_rfl (by simp)).antisymm (orderUnitNorm_nonneg e 0)

@[simp]
lemma orderUnitOsc_zero (e : E) : orderUnitOsc e 0 = 0 :=
  (orderUnitOsc_le (a := 0) le_rfl (by simp)).antisymm (orderUnitOsc_nonneg e 0)

/-- The oscillation is at most twice the order-unit norm. -/
lemma orderUnitOsc_le_two_mul_orderUnitNorm (he : IsOrderUnit e) (x : E) :
    orderUnitOsc e x ≤ 2 * orderUnitNorm e x := by
  rw [← div_le_iff₀' two_pos]
  refine le_orderUnitNorm he fun c hc hx ↦ ?_
  rw [div_le_iff₀' two_pos]
  exact orderUnitOsc_le (a := -c) (by positivity) (by rwa [neg_smul, show -c + 2 * c = c by ring])

/-! ### Topical maps -/

/-- A map `T` is *topical* for `e` [GG04] if it is monotone and commutes with adding multiples of
`e`. Undiscounted Bellman operators and max-plus maps (`isTopical_one_sup'_add`) are topical. -/
structure IsTopical (e : E) (T : E → E) : Prop where
  monotone : Monotone T
  map_add_smul (x : E) (c : ℝ) : T (x + c • e) = T x + c • e

namespace IsTopical

variable {T T' : E → E}

lemma id (e : E) : IsTopical e id := ⟨monotone_id, fun _ _ ↦ rfl⟩

lemma comp (hT : IsTopical e T) (hT' : IsTopical e T') : IsTopical e (T ∘ T') :=
  ⟨hT.monotone.comp hT'.monotone, fun x c ↦ by simp [hT'.map_add_smul, hT.map_add_smul]⟩

lemma iterate (hT : IsTopical e T) (n : ℕ) : IsTopical e T^[n] := by
  induction n with
  | zero => exact IsTopical.id e
  | succ n ih => rw [Function.iterate_succ]; exact ih.comp hT

end IsTopical

/-! ### Algebraic properties of the order-unit norm and the oscillation -/

/-- Scaling by `r > 0` maps the interval `[-(r⁻¹ * c) • e, (r⁻¹ * c) • e]` onto
`[-c • e, c • e]`. -/
lemma smul_mem_Icc_neg_smul_iff_of_pos [PosSMulMono ℝ E] {r : ℝ} (hr : 0 < r) :
    r • x ∈ Icc (-(c • e)) (c • e) ↔ x ∈ Icc (-((r⁻¹ * c) • e)) ((r⁻¹ * c) • e) := by
  have h : c • e = r • (r⁻¹ * c) • e := by rw [smul_smul, mul_inv_cancel_left₀ hr.ne']
  rw [h, ← smul_neg, mem_Icc, mem_Icc, smul_le_smul_iff_of_pos_left hr,
    smul_le_smul_iff_of_pos_left hr]

variable [IsOrderedAddMonoid E]

@[simp]
lemma orderUnitNorm_neg (e x : E) : orderUnitNorm e (-x) = orderUnitNorm e x := by
  simp_rw [orderUnitNorm_def, mem_Icc, neg_le_neg_iff, neg_le, and_comm (a := x ≤ _)]

lemma orderUnitNorm_sub_rev (e x y : E) : orderUnitNorm e (x - y) = orderUnitNorm e (y - x) := by
  rw [← orderUnitNorm_neg, neg_sub]

/-- The order-unit norm is absolutely homogeneous. -/
lemma orderUnitNorm_smul [PosSMulMono ℝ E] (r : ℝ) (x : E) :
    orderUnitNorm e (r • x) = |r| * orderUnitNorm e x := by
  wlog hr : 0 ≤ r generalizing r
  · rw [← orderUnitNorm_neg, ← neg_smul, this (-r) (by linarith), abs_neg]
  obtain rfl | hr := hr.eq_or_lt
  · simp
  rw [abs_of_pos hr, orderUnitNorm_def, orderUnitNorm_def, ← smul_eq_mul,
    ← Real.sInf_smul_of_nonneg hr.le]
  congr 1
  ext c
  simp [mem_smul_set_iff_inv_smul_mem₀ hr.ne', smul_mem_Icc_neg_smul_iff_of_pos hr,
    mul_nonneg_iff_of_pos_left (inv_pos.2 hr)]

/-- The triangle inequality for the order-unit norm of an order unit. -/
lemma orderUnitNorm_add_le (he : IsOrderUnit e) (x y : E) :
    orderUnitNorm e (x + y) ≤ orderUnitNorm e x + orderUnitNorm e y := by
  have h c (hc : 0 ≤ c) (hx : x ∈ Icc (-(c • e)) (c • e)) c' (hc' : 0 ≤ c')
      (hy : y ∈ Icc (-(c' • e)) (c' • e)) : orderUnitNorm e (x + y) ≤ c + c' := by
    refine orderUnitNorm_le (add_nonneg hc hc') ⟨?_, ?_⟩
    · rw [add_smul, neg_add]
      exact add_le_add hx.1 hy.1
    · rw [add_smul]
      exact add_le_add hx.2 hy.2
  rw [← sub_le_iff_le_add]
  refine le_orderUnitNorm he fun c hc hx ↦ ?_
  rw [sub_le_iff_le_add', ← sub_le_iff_le_add]
  exact le_orderUnitNorm he fun c' hc' hy ↦
    sub_le_iff_le_add.2 ((h c hc hx c' hc' hy).trans_eq (add_comm c c'))

/-- The order-unit norm is monotone on nonnegative elements. -/
lemma orderUnitNorm_le_orderUnitNorm_of_nonneg (he : IsOrderUnit e) (hx : 0 ≤ x) (hxy : x ≤ y) :
    orderUnitNorm e x ≤ orderUnitNorm e y :=
  le_orderUnitNorm he fun _ hc hy ↦ orderUnitNorm_le hc
    ⟨(neg_nonpos.2 (hx.trans (hxy.trans hy.2))).trans hx, hxy.trans hy.2⟩

/-- The oscillation is invariant under adding multiples of `e`. -/
@[simp]
lemma orderUnitOsc_add_smul (e x : E) (c : ℝ) : orderUnitOsc e (x + c • e) = orderUnitOsc e x := by
  simp only [orderUnitOsc_def]
  congr 1
  ext d
  refine and_congr_right fun _ ↦ ⟨fun ⟨a, h₁, h₂⟩ ↦ ⟨a - c, ?_, ?_⟩,
    fun ⟨a, h₁, h₂⟩ ↦ ⟨a + c, ?_, ?_⟩⟩
  · rw [sub_smul, sub_le_iff_le_add]
    exact h₁
  · rw [sub_add_eq_add_sub, sub_smul, le_sub_iff_add_le]
    exact h₂
  · rw [add_smul]
    exact add_le_add_left h₁ _
  · rw [add_right_comm, add_smul]
    exact add_le_add_left h₂ _

/-- The oscillation is invariant under negation. -/
@[simp]
lemma orderUnitOsc_neg (e x : E) : orderUnitOsc e (-x) = orderUnitOsc e x := by
  simp only [orderUnitOsc_def]
  congr 1
  ext d
  refine and_congr_right fun _ ↦ ⟨fun ⟨a, h₁, h₂⟩ ↦ ⟨-(a + d), ?_, ?_⟩,
    fun ⟨a, h₁, h₂⟩ ↦ ⟨-(a + d), ?_, ?_⟩⟩
  · rw [neg_smul]
    exact neg_le.1 h₂
  · rw [show -(a + d) + d = -a by ring, neg_smul]
    exact le_neg.1 h₁
  · rw [neg_smul]
    exact neg_le_neg h₂
  · rw [show -(a + d) + d = -a by ring, neg_smul]
    exact neg_le_neg h₁

/-! ### Blackwell's sufficient conditions -/

/-- **Blackwell's sufficient conditions** [Bla65]: a monotone map `T` with
`T (x + c • e) ≤ T x + (γ * c) • e` for all `x` and `c ≥ 0` is `γ`-Lipschitz for the order-unit
norm of an order unit `e`. -/
theorem orderUnitNorm_sub_le_of_monotone_of_add_smul_le {T : E → E} {γ : ℝ} (hγ : 0 ≤ γ)
    (he : IsOrderUnit e) (hT : Monotone T)
    (h : ∀ x (c : ℝ), 0 ≤ c → T (x + c • e) ≤ T x + (γ * c) • e) (x y : E) :
    orderUnitNorm e (T x - T y) ≤ γ * orderUnitNorm e (x - y) := by
  obtain ⟨c₀, hc₀⟩ := he (x - y)
  rw [orderUnitNorm_def e (x - y), ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hγ]
  refine csInf_le_csInf ⟨0, fun _ hc ↦ hc.1⟩ ⟨γ • c₀, smul_mem_smul_set hc₀⟩ ?_
  rintro _ ⟨c, ⟨hc, hxy₁, hxy₂⟩, rfl⟩
  -- `y - c • e ≤ x ≤ y + c • e`, so monotonicity and the hypothesis bound `T x - T y`.
  have hx : T x ≤ T y + (γ * c) • e := (hT (sub_le_iff_le_add'.1 hxy₂)).trans (h y c hc)
  have hy : T y ≤ T x + (γ * c) • e := (hT (neg_le_sub_iff_le_add.1 hxy₁)).trans (h x c hc)
  exact ⟨by simpa using mul_nonneg hγ hc, by simpa using neg_le_sub_iff_le_add.2 hy,
    by simpa using sub_le_iff_le_add'.2 hx⟩

/-- If the norm of a normed group `F` is the order-unit norm of `u`, then `u` is an order unit. -/
lemma isOrderUnit_of_forall_orderUnitNorm_eq_norm {F : Type*} [NormedAddCommGroup F]
    [PartialOrder F] [Module ℝ F] {u : F} (hnorm : ∀ x, orderUnitNorm u x = ‖x‖) :
    IsOrderUnit u := by
  intro x
  by_contra hx
  have hS : {c : ℝ | 0 ≤ c ∧ x ∈ Icc (-(c • u)) (c • u)} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun c hc ↦ hx ⟨c, hc⟩
  have hx0 : x = 0 := by rw [← norm_eq_zero, ← hnorm, orderUnitNorm_def, hS, Real.sInf_empty]
  exact hx ⟨0, le_rfl, by simp [hx0]⟩

/-- **Blackwell's sufficient conditions** in a normed group whose norm is the order-unit norm of
`u`: a monotone map `T` with `T (x + c • u) ≤ T x + (γ * c) • u` for all `x` and `c ≥ 0` is
`γ`-Lipschitz. For `γ < 1` it is a contraction (`ContractingWith`). -/
theorem lipschitzWith_of_monotone_of_add_smul_le {F : Type*} [NormedAddCommGroup F]
    [PartialOrder F] [IsOrderedAddMonoid F] [Module ℝ F] {u : F}
    (hnorm : ∀ x, orderUnitNorm u x = ‖x‖) {T : F → F} {γ : NNReal} (hT : Monotone T)
    (h : ∀ x (c : ℝ), 0 ≤ c → T (x + c • u) ≤ T x + ((γ : ℝ) * c) • u) : LipschitzWith γ T :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    simpa only [dist_eq_norm, ← hnorm] using orderUnitNorm_sub_le_of_monotone_of_add_smul_le
      γ.coe_nonneg (isOrderUnit_of_forall_orderUnitNorm_eq_norm hnorm) hT h x y

/-! ### Nonexpansiveness of topical maps -/

namespace IsTopical

variable {T : E → E}

/-- A topical map is nonexpansive for the order-unit norm. -/
theorem orderUnitNorm_sub_le (hT : IsTopical e T) (he : IsOrderUnit e) (x y : E) :
    orderUnitNorm e (T x - T y) ≤ orderUnitNorm e (x - y) := by
  simpa using orderUnitNorm_sub_le_of_monotone_of_add_smul_le zero_le_one he hT.monotone
    (fun x c _ ↦ by rw [one_mul, hT.map_add_smul]) x y

/-- A topical map is nonexpansive for the oscillation. -/
theorem orderUnitOsc_sub_le (hT : IsTopical e T) (he : IsOrderUnit e) (x y : E) :
    orderUnitOsc e (T x - T y) ≤ orderUnitOsc e (x - y) := by
  refine csInf_le_csInf ⟨0, fun _ hd ↦ hd.1⟩ (he.exists_mem_Icc_smul _) ?_
  rintro d ⟨hd, a, h₁, h₂⟩
  -- `y + a • e ≤ x ≤ y + (a + d) • e` is preserved by `T`.
  refine ⟨hd, a, ?_, ?_⟩
  · rw [le_sub_iff_add_le', ← hT.map_add_smul]
    exact hT.monotone (le_sub_iff_add_le'.1 h₁)
  · rw [sub_le_iff_le_add', ← hT.map_add_smul]
    exact hT.monotone (sub_le_iff_le_add'.1 h₂)

end IsTopical

/-! ### Functions on a finite type -/

section Pi

variable {ι : Type*} {w : ι → ℝ}

/-- For a positive weight `w`, `x` lies in `[-c • w, c • w]` iff `|x i| / w i ≤ c` for all `i`. -/
lemma mem_Icc_neg_smul_smul_iff_forall_abs_div_le (hw : ∀ i, 0 < w i) {x : ι → ℝ} :
    x ∈ Icc (-(c • w)) (c • w) ↔ ∀ i, |x i| / w i ≤ c := by
  simp only [mem_Icc, Pi.le_def, ← forall_and, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  exact forall_congr' fun i ↦ by rw [div_le_iff₀ (hw i), abs_le]

/-- The weighted sup norm of a nonnegative weight is nonnegative. -/
lemma iSup_abs_div_nonneg (hw : ∀ i, 0 ≤ w i) (x : ι → ℝ) : 0 ≤ ⨆ i, |x i| / w i :=
  Real.iSup_nonneg fun i ↦ div_nonneg (abs_nonneg _) (hw i)

/-- A positive weight `w` is an order unit of `ι → ℝ`. -/
lemma isOrderUnit_of_pos [Finite ι] (hw : ∀ i, 0 < w i) : IsOrderUnit w := fun x ↦
  ⟨⨆ j, |x j| / w j, iSup_abs_div_nonneg (fun i ↦ (hw i).le) x,
    (mem_Icc_neg_smul_smul_iff_forall_abs_div_le hw).2 (le_ciSup (finite_range _).bddAbove)⟩

lemma isOrderUnit_one [Finite ι] : IsOrderUnit (1 : ι → ℝ) := isOrderUnit_of_pos fun _ ↦ one_pos

/-- The order-unit norm of a positive weight `w` is the weighted sup norm `⨆ i, |x i| / w i`. -/
theorem orderUnitNorm_eq_iSup_abs_div [Finite ι] (hw : ∀ i, 0 < w i) (x : ι → ℝ) :
    orderUnitNorm w x = ⨆ i, |x i| / w i := by
  have hS : {c : ℝ | 0 ≤ c ∧ x ∈ Icc (-(c • w)) (c • w)} = Ici (⨆ i, |x i| / w i) := by
    ext c
    simp only [mem_ofPred_eq, mem_Ici, mem_Icc_neg_smul_smul_iff_forall_abs_div_le hw]
    refine ⟨fun ⟨hc, h⟩ ↦ Real.iSup_le h hc, fun h ↦ ⟨?_, fun i ↦ ?_⟩⟩
    · exact (iSup_abs_div_nonneg (fun i ↦ (hw i).le) x).trans h
    · exact (le_ciSup (finite_range _).bddAbove i).trans h
  rw [orderUnitNorm_def, hS, csInf_Ici]

/-- On `ι → ℝ` with `ι` finite, the order-unit norm of `1` is the sup norm. -/
@[simp]
theorem orderUnitNorm_one_eq_norm [Fintype ι] (x : ι → ℝ) : orderUnitNorm 1 x = ‖x‖ := by
  rw [orderUnitNorm_eq_iSup_abs_div (w := 1) fun _ ↦ one_pos]
  simp only [Pi.one_apply, div_one]
  refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (norm_nonneg x)) ?_
  · simpa [← Real.norm_eq_abs] using norm_le_pi_norm x i
  · refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg fun i ↦ abs_nonneg _)).2 fun i ↦ ?_
    simpa [Real.norm_eq_abs] using le_ciSup (finite_range fun i ↦ |x i|).bddAbove i

/-- **Blackwell's sufficient conditions** for the weighted sup norm of a positive weight `w`: a
monotone map `T` with `T (x + c • w) ≤ T x + (γ * c) • w` for all `x` and `c ≥ 0` satisfies
`⨆ i, |T x i - T y i| / w i ≤ γ * ⨆ i, |x i - y i| / w i`. -/
theorem iSup_abs_sub_div_le_of_monotone_of_add_smul_le [Finite ι] (hw : ∀ i, 0 < w i)
    {T : (ι → ℝ) → ι → ℝ} {γ : ℝ} (hγ : 0 ≤ γ) (hT : Monotone T)
    (h : ∀ x (c : ℝ), 0 ≤ c → T (x + c • w) ≤ T x + (γ * c) • w) (x y : ι → ℝ) :
    ⨆ i, |T x i - T y i| / w i ≤ γ * ⨆ i, |x i - y i| / w i := by
  simpa [orderUnitNorm_eq_iSup_abs_div hw] using
    orderUnitNorm_sub_le_of_monotone_of_add_smul_le hγ (isOrderUnit_of_pos hw) hT h x y

/-- **Blackwell's sufficient conditions** on `ι → ℝ` with the sup norm: a monotone map `T` with
`T (x + c) ≤ T x + γ * c` for all `x` and constants `c ≥ 0` is `γ`-Lipschitz. For `γ < 1` it is a
contraction (`ContractingWith`). -/
theorem lipschitzWith_of_monotone_of_add_const_le [Fintype ι] {T : (ι → ℝ) → ι → ℝ} {γ : NNReal}
    (hT : Monotone T) (h : ∀ x (c : ℝ), 0 ≤ c → T (x + fun _ ↦ c) ≤ T x + fun _ ↦ γ * c) :
    LipschitzWith γ T :=
  lipschitzWith_of_monotone_of_add_smul_le (u := (1 : ι → ℝ)) orderUnitNorm_one_eq_norm hT
    fun x c hc ↦ by rw [Pi.smul_one_eq_const, Pi.smul_one_eq_const]; exact h x c hc

/-- On `ι → ℝ` with `ι` finite and nonempty, the oscillation of `1` is `max x - min x`. -/
theorem orderUnitOsc_one_eq_sup'_sub_inf' [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    orderUnitOsc 1 x = Finset.univ.sup' Finset.univ_nonempty x -
      Finset.univ.inf' Finset.univ_nonempty x := by
  set M := Finset.univ.sup' Finset.univ_nonempty x
  set m := Finset.univ.inf' Finset.univ_nonempty x
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hm i : m ≤ x i := Finset.inf'_le _ (Finset.mem_univ i)
  have hM i : x i ≤ M := Finset.le_sup' _ (Finset.mem_univ i)
  rw [orderUnitOsc_def]
  refine IsLeast.csInf_eq ⟨⟨sub_nonneg.2 ((hm i₀).trans (hM i₀)), m, fun i ↦ ?_, fun i ↦ ?_⟩, ?_⟩
  · simpa using hm i
  · simpa using hM i
  · rintro d ⟨-, a, h₁, h₂⟩
    have ham : a ≤ m := Finset.le_inf' _ _ fun i _ ↦ by simpa using h₁ i
    have hMa : M ≤ a + d := Finset.sup'_le _ _ fun i _ ↦ by simpa using h₂ i
    linarith

/-- A map on `ι → ℝ` is topical for `1` iff it is monotone and commutes with adding constant
functions. -/
theorem isTopical_one_iff {T : (ι → ℝ) → ι → ℝ} :
    IsTopical (1 : ι → ℝ) T ↔ Monotone T ∧ ∀ x (c : ℝ), T (x + fun _ ↦ c) = T x + fun _ ↦ c := by
  simp only [← Pi.smul_one_eq_const]
  exact ⟨fun h ↦ ⟨h.monotone, h.map_add_smul⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- Max-plus maps `x ↦ (max_j (A i j + x j))_i` are topical for `1`. -/
theorem isTopical_one_sup'_add [Fintype ι] [Nonempty ι] (A : ι → ι → ℝ) :
    IsTopical (1 : ι → ℝ) fun x i ↦ Finset.univ.sup' Finset.univ_nonempty fun j ↦ A i j + x j := by
  refine ⟨fun x y hxy i ↦ Finset.sup'_mono_fun fun j _ ↦ add_le_add le_rfl (hxy j),
    fun x c ↦ funext fun i ↦ ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, ← add_assoc]
  exact (Finset.sup'_add ..).symm

end Pi

end LMLExplore
