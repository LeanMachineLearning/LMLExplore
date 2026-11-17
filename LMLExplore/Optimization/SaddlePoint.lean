/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.SaddlePoint

/-!
# The duality gap and approximate saddle points

For a payoff `f : E → F → ℝ` and sets `X ⊆ E`, `Y ⊆ F`, consider the problem
`min_{x ∈ X} max_{y ∈ Y} f x y`, in which a minimizing player chooses `x` and a maximizing player
chooses `y`. This file measures how far a pair `(a, b)` is from a saddle point of `f` on `X × Y`
(Mathlib's `IsSaddlePointOn`) [Ora, Chapter 15]:

* The **duality gap** `dualityGap X Y f a b = ⨆ y ∈ Y, f a y - ⨅ x ∈ X, f x b`
  [Ora, Definition 15.8]. The supremum and the infimum need not be attained nor finite, so the gap
  takes values in `EReal`. A real bound on the gap is a bound on every difference
  `f a y - f x b` (`dualityGap_le_coe_iff`), which is how the gap is bounded in practice: no
  supremum or infimum needs to be computed. The gap is nonnegative at a pair of `X × Y`
  (`dualityGap_nonneg`), it bounds the suboptimality of `a` for the minimizing player and of `b`
  for the maximizing player (`iSup₂_sub_iInf₂_iSup₂_le_dualityGap`,
  `iSup₂_iInf₂_sub_iInf₂_le_dualityGap`), and it vanishes exactly at the saddle points
  (`isSaddlePointOn_iff_dualityGap_nonpos`, `isSaddlePointOn_iff_dualityGap_eq_zero`).
* An **`ε`-saddle point** `IsApproxSaddlePointOn X Y f ε a b`: no player gains more than `ε` by
  deviating, `f a y ≤ f a b + ε` and `f a b ≤ f x b + ε` for every `x ∈ X` and `y ∈ Y`
  [Ora, Definition 15.9]. An `ε`-saddle point has gap at most `2 ε`
  (`IsApproxSaddlePointOn.dualityGap_le`), and a pair of `X × Y` with gap at most `ε` is an
  `ε`-saddle point (`isApproxSaddlePointOn_of_dualityGap_le`) (see [Ora, Lemma 15.10]). The
  `0`-saddle points of `X × Y` are the saddle points (`isApproxSaddlePointOn_zero_iff`).

The duality gap measures the quality of approximate solutions produced by algorithms, such as the
averages of the plays of two online learners against each other, without knowing the value of the
problem.

## Main definitions

* `LMLExplore.dualityGap X Y f a b`: the duality gap of `(a, b)`.
* `LMLExplore.IsApproxSaddlePointOn X Y f ε a b`: `(a, b)` is an `ε`-saddle point of `f` on
  `X × Y`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Set

namespace LMLExplore

variable {E F : Type*} {X : Set E} {Y : Set F} {f : E → F → ℝ} {a x : E} {b y : F}

section DualityGap

/-- The **duality gap** of the pair `(a, b)` for the problem `min_{x ∈ X} max_{y ∈ Y} f x y`
[Ora, Definition 15.8]: the supremum over `y ∈ Y` of `f a y` minus the infimum over `x ∈ X` of
`f x b`. It is valued in `EReal`, since the supremum and the infimum need not be finite; it is `⊥`
when `X` or `Y` is empty. -/
noncomputable def dualityGap (X : Set E) (Y : Set F) (f : E → F → ℝ) (a : E) (b : F) : EReal :=
  (⨆ y ∈ Y, (f a y : EReal)) - ⨅ x ∈ X, (f x b : EReal)

lemma dualityGap_def (X : Set E) (Y : Set F) (f : E → F → ℝ) (a : E) (b : F) :
    dualityGap X Y f a b = (⨆ y ∈ Y, (f a y : EReal)) - ⨅ x ∈ X, (f x b : EReal) := (rfl)

/-- Each difference `f a y - f x b` for `x ∈ X` and `y ∈ Y` is at most the duality gap of
`(a, b)`. -/
lemma coe_sub_le_dualityGap (hx : x ∈ X) (hy : y ∈ Y) :
    ((f a y - f x b : ℝ) : EReal) ≤ dualityGap X Y f a b := by
  rw [EReal.coe_sub, dualityGap_def]
  exact EReal.sub_le_sub (le_iSup₂ (f := fun y _ ↦ (f a y : EReal)) y hy)
    (iInf₂_le (f := fun x _ ↦ (f x b : EReal)) x hx)

/-- **A real bound on the duality gap** is a bound on every difference `f a y - f x b` for
`x ∈ X` and `y ∈ Y`. The gap can thus be bounded without computing any supremum or infimum, and
without assuming that they are attained. -/
theorem dualityGap_le_coe_iff {B : ℝ} :
    dualityGap X Y f a b ≤ B ↔ ∀ x ∈ X, ∀ y ∈ Y, f a y - f x b ≤ B := by
  refine ⟨fun h x hx y hy ↦ EReal.coe_le_coe_iff.1 ((coe_sub_le_dualityGap hx hy).trans h),
    fun h ↦ ?_⟩
  rw [dualityGap_def, EReal.sub_le_iff_le_add (.inr (EReal.coe_ne_top B))
    (.inr (EReal.coe_ne_bot B))]
  refine iSup₂_le fun y hy ↦ ?_
  rw [add_comm, ← EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot B)) (.inl (EReal.coe_ne_top B))]
  refine le_iInf₂ fun x hx ↦ ?_
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith [h x hx y hy]

/-- The duality gap of a pair of `X × Y` is nonnegative. -/
lemma dualityGap_nonneg (ha : a ∈ X) (hb : b ∈ Y) : 0 ≤ dualityGap X Y f a b := by
  simpa using coe_sub_le_dualityGap (f := f) (a := a) (b := b) ha hb

/-- The duality gap of `(a, b)` bounds the **suboptimality of `a`** for the minimizing player:
for `b ∈ Y`, the worst-case payoff of `a` exceeds the minimax value by at most the gap. -/
lemma iSup₂_sub_iInf₂_iSup₂_le_dualityGap (hb : b ∈ Y) :
    (⨆ y ∈ Y, (f a y : EReal)) - ⨅ x ∈ X, ⨆ y ∈ Y, (f x y : EReal) ≤ dualityGap X Y f a b :=
  EReal.sub_le_sub le_rfl <| iInf₂_mono fun x _ ↦ le_iSup₂ (f := fun y _ ↦ (f x y : EReal)) b hb

/-- The duality gap of `(a, b)` bounds the **suboptimality of `b`** for the maximizing player:
for `a ∈ X`, the worst-case payoff of `b` falls short of the maximin value by at most the gap. -/
lemma iSup₂_iInf₂_sub_iInf₂_le_dualityGap (ha : a ∈ X) :
    (⨆ y ∈ Y, ⨅ x ∈ X, (f x y : EReal)) - ⨅ x ∈ X, (f x b : EReal) ≤ dualityGap X Y f a b :=
  EReal.sub_le_sub (iSup₂_mono fun y _ ↦ iInf₂_le (f := fun x _ ↦ (f x y : EReal)) a ha) le_rfl

/-- **The saddle points are the pairs of nonpositive duality gap.** No membership is needed: a
saddle point in the sense of Mathlib's `IsSaddlePointOn` need not lie in `X × Y`. -/
theorem isSaddlePointOn_iff_dualityGap_nonpos :
    IsSaddlePointOn X Y f a b ↔ dualityGap X Y f a b ≤ 0 := by
  rw [← EReal.coe_zero, dualityGap_le_coe_iff]
  exact forall₂_congr fun x _ ↦ forall₂_congr fun y _ ↦ sub_nonpos.symm

/-- **Zero duality gap characterizes the saddle points** of `X × Y`. -/
theorem isSaddlePointOn_iff_dualityGap_eq_zero (ha : a ∈ X) (hb : b ∈ Y) :
    IsSaddlePointOn X Y f a b ↔ dualityGap X Y f a b = 0 := by
  rw [isSaddlePointOn_iff_dualityGap_nonpos]
  exact ⟨fun h ↦ h.antisymm (dualityGap_nonneg ha hb), le_of_eq⟩

end DualityGap

section ApproxSaddlePoint

variable {ε ε' : ℝ}

/-- The pair `(a, b)` is an **`ε`-saddle point** of `f` on `X × Y` [Ora, Definition 15.9]: the
maximizing player gains at most `ε` by deviating from `b` to any `y ∈ Y`, and the minimizing
player gains at most `ε` by deviating from `a` to any `x ∈ X`. As for Mathlib's
`IsSaddlePointOn`, the pair need not lie in `X × Y`. -/
def IsApproxSaddlePointOn (X : Set E) (Y : Set F) (f : E → F → ℝ) (ε : ℝ) (a : E) (b : F) :
    Prop :=
  (∀ y ∈ Y, f a y ≤ f a b + ε) ∧ ∀ x ∈ X, f a b ≤ f x b + ε

lemma isApproxSaddlePointOn_iff :
    IsApproxSaddlePointOn X Y f ε a b ↔
      (∀ y ∈ Y, f a y ≤ f a b + ε) ∧ ∀ x ∈ X, f a b ≤ f x b + ε := Iff.rfl

namespace IsApproxSaddlePointOn

/-- An `ε`-saddle point is an `ε'`-saddle point for every `ε' ≥ ε`. -/
lemma mono (h : IsApproxSaddlePointOn X Y f ε a b) (hε : ε ≤ ε') :
    IsApproxSaddlePointOn X Y f ε' a b :=
  ⟨fun y hy ↦ (h.1 y hy).trans (by linarith), fun x hx ↦ (h.2 x hx).trans (by linarith)⟩

/-- **An `ε`-saddle point has duality gap at most `2 ε`** (see [Ora, Lemma 15.10]). -/
theorem dualityGap_le (h : IsApproxSaddlePointOn X Y f ε a b) :
    dualityGap X Y f a b ≤ (2 * ε : ℝ) :=
  dualityGap_le_coe_iff.2 fun x hx y hy ↦ by linarith [h.1 y hy, h.2 x hx]

end IsApproxSaddlePointOn

/-- **A pair of `X × Y` with duality gap at most `ε` is an `ε`-saddle point** [Ora, Lemma 15.10]. -/
theorem isApproxSaddlePointOn_of_dualityGap_le (ha : a ∈ X) (hb : b ∈ Y)
    (h : dualityGap X Y f a b ≤ ε) : IsApproxSaddlePointOn X Y f ε a b := by
  rw [dualityGap_le_coe_iff] at h
  exact ⟨fun y hy ↦ by linarith [h a ha y hy], fun x hx ↦ by linarith [h x hx b hb]⟩

/-- The `0`-saddle points of `f` in `X × Y` are its saddle points. -/
theorem isApproxSaddlePointOn_zero_iff (ha : a ∈ X) (hb : b ∈ Y) :
    IsApproxSaddlePointOn X Y f 0 a b ↔ IsSaddlePointOn X Y f a b := by
  refine ⟨fun h x hx y hy ↦ ?_, fun h ↦ ?_⟩
  · linarith [h.1 y hy, h.2 x hx]
  · exact isApproxSaddlePointOn_of_dualityGap_le ha hb <| by
      exact_mod_cast (isSaddlePointOn_iff_dualityGap_nonpos.1 h)

end ApproxSaddlePoint

end LMLExplore
