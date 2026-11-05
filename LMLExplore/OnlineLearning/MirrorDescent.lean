/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.OnlineLearning.FTRL
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv

/-!
# Mirror descent

Online linear optimization on a set `K` of a real normed space `E`, with losses
`y t : E →L[ℝ] ℝ` in the dual of `E`, as in `LMLExplore.OnlineLearning.FTRL`. **Mirror descent**
with potential `F` and learning rate `η` starts at a minimizer `a 0` of `F` over `K` [LS, (28.1)]
and, after the loss `y t` of round `t`, plays a minimizer over `K` of
`b ↦ η y t b + D_F(b, a t)` [LS, (28.2)], where `D_F(b, a) = F b - F a - F'(b - a)` is the
Bregman divergence of `F` for a derivative `F'` of `F` at `a`. Where FTRL regularizes the
cumulative loss, mirror descent only uses the last loss and the last play.

The step can be computed in two stages [LS, (28.7)–(28.9)]: an unconstrained step to a point `b`
where `F` has derivative `F' - η y`, followed by the Bregman projection of `b` onto `K`. The
mirror map `∇F` is not required to be invertible here: the statements take the point `b` and its
derivative as data, which is what the analysis of mirror descent with bandit feedback uses.

As for FTRL, the statements need only the derivatives of `F` at the points involved and the
convexity of `F`, not the full structure of a Legendre function, and they hold for every sequence
of losses, in particular for losses chosen adaptively from the past plays.

## Main definitions

* `IsMirrorDescentStep K F η y a F' x`: `x` is a step of mirror descent on `K` from `a`, with
  potential `F`, derivative `F'` of `F` at `a`, learning rate `η` and loss `y`.

## Main statements

* `isMirrorDescentStep_iff_isMinOn_bregDiv`: the second stage of the two-step form [LS, (28.8)].
  If `G = F' - η y`, the steps from `a` are the Bregman projections onto `K` of any point `b`
  with derivative `G`.
* `isMinOn_mul_apply_add_bregDiv_of_hasFDerivWithinAt`: the first stage [LS, (28.7), (28.9)].
  For `F` convex on `D`, a point `b ∈ D` where `F` has derivative `F' - η y` minimizes the
  objective of the step over `D`.
* `exists_isMirrorDescentStep`: on a nonempty compact set, with a potential continuous on it,
  mirror descent steps exist.
* `IsMirrorDescentStep.mul_apply_sub_le`: the one-step inequality
  `η y (x - u) ≤ D_F(u, a) - D_F(u, x) - D_F(x, a)`.
* `sum_apply_sub_le_mirrorDescent`: the regret against `u` is at most
  `(D_F(u, a 0) - D_F(u, a n)) / η + ∑ t < n, y t (a t - a (t + 1))
    - (∑ t < n, D_F(a (t + 1), a t)) / η`, for any initial play.
* `mirrorDescent_regret_le`: [LS, Theorem 28.4], first bound.
* `mirrorDescent_regret_le_bregDiv_add_sum_bregDiv`: [LS, (28.11)], the bound
  `(D_F(u, a 0) + ∑ t < n, D_F(a t, b (t + 1))) / η` through the unconstrained steps `b (t + 1)`,
  for any initial play.
* `mirrorDescent_regret_le_sub_add_sum_bregDiv`: [LS, Theorem 28.4], second bound.
* `mirrorDescent_regret_le_of_strongConvexOn`: [LS, Corollary 28.8] for mirror descent.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K D : Set E} {F : E → ℝ} {η : ℝ}
  {n : ℕ} {u : E}

/-- `x` is a **mirror descent step** [LS, (28.2)] on `K` from `a`, with potential `F`, linear map
`F'`, learning rate `η` and loss `y`: `x ∈ K` minimizes over `K` the objective
`b ↦ η y b + D_F(b, a)`, where `D_F(b, a) = F b - F a - F' (b - a)` is the Bregman divergence.
`F'` is intended to be a derivative of `F` at `a`, but the predicate does not require it: the
theorems below assume `HasFDerivWithinAt` separately. -/
structure IsMirrorDescentStep (K : Set E) (F : E → ℝ) (η : ℝ) (y : E →L[ℝ] ℝ) (a : E)
    (F' : E →L[ℝ] ℝ) (x : E) : Prop where
  /-- The step lies in `K`. -/
  mem : x ∈ K
  /-- The step minimizes the mirror descent objective over `K`. -/
  isMinOn : IsMinOn (fun b ↦ η * y b + bregDiv F b a F') K x

section TwoStep

variable {y F' G : E →L[ℝ] ℝ}

/-- If `G = F' - η y`, the objective of a mirror descent step from `a` with derivative `F'` is the
Bregman divergence from any point `b` with derivative `G`, up to an additive constant:
`η y c + D_F(c, a) = η y b + D_F(b, a) + D_F(c, b)`. -/
lemma mul_apply_add_bregDiv_eq (hG : G = F' - η • y) (a b c : E) :
    η * y c + bregDiv F c a F' = η * y b + bregDiv F b a F' + bregDiv F c b G := by
  subst hG
  simp only [bregDiv, map_sub, sub_apply, smul_apply, smul_eq_mul]
  ring

/-- **Mirror descent steps are Bregman projections** [LS, (28.8)]. If `G = F' - η y`, then for
every point `b`, the mirror descent steps on `K` from `a` with derivative `F'` are the minimizers
over `K` of the Bregman divergence `c ↦ D_F(c, b)` for the derivative `G`. In the two-step form
of mirror descent, `b` is the unconstrained step of
`isMinOn_mul_apply_add_bregDiv_of_hasFDerivWithinAt`. -/
theorem isMirrorDescentStep_iff_isMinOn_bregDiv (hG : G = F' - η • y) (a b x : E) :
    IsMirrorDescentStep K F η y a F' x ↔ x ∈ K ∧ IsMinOn (fun c ↦ bregDiv F c b G) K x := by
  have h_iff (c : E) : η * y x + bregDiv F x a F' ≤ η * y c + bregDiv F c a F' ↔
      bregDiv F x b G ≤ bregDiv F c b G := by
    rw [mul_apply_add_bregDiv_eq hG a b x, mul_apply_add_bregDiv_eq hG a b c]
    exact add_le_add_iff_left _
  refine ⟨fun h ↦ ⟨h.mem, isMinOn_iff.mpr fun c hc ↦ (h_iff c).mp (isMinOn_iff.mp h.isMinOn c hc)⟩,
    fun h ↦ ⟨h.1, isMinOn_iff.mpr fun c hc ↦ (h_iff c).mpr (isMinOn_iff.mp h.2 c hc)⟩⟩

/-- **The unconstrained step of mirror descent** [LS, (28.7), (28.9)]. Let `F` be convex on `D`
and let `b ∈ D` be a point where `F` has derivative `G = F' - η y` within `D`. Then `b`
minimizes over `D` the objective `c ↦ η y c + D_F(c, a)` of a mirror descent step from `a` with
derivative `F'`. -/
theorem isMinOn_mul_apply_add_bregDiv_of_hasFDerivWithinAt (hG : G = F' - η • y)
    (hF : ConvexOn ℝ D F) {b : E} (hb : b ∈ D) (hGb : HasFDerivWithinAt F G D b) (a : E) :
    IsMinOn (fun c ↦ η * y c + bregDiv F c a F') D b := by
  refine isMinOn_iff.mpr fun c hc ↦ ?_
  rw [mul_apply_add_bregDiv_eq hG a b c]
  exact le_add_of_nonneg_right (hGb.hasSubgradientWithinAt hF hb c hc)

end TwoStep

/-- **Existence of mirror descent steps.** On a nonempty compact set `K`, with a potential `F`
continuous on `K`, every point `a` and linear map `F'` have a mirror descent step from `a` with
derivative `F'`, for every learning rate and loss. -/
theorem exists_isMirrorDescentStep (hK : IsCompact K) (hK_ne : K.Nonempty) (hF : ContinuousOn F K)
    (η : ℝ) (y : E →L[ℝ] ℝ) (a : E) (F' : E →L[ℝ] ℝ) :
    ∃ x, IsMirrorDescentStep K F η y a F' x := by
  have h_cont : ContinuousOn (fun b ↦ η * y b + bregDiv F b a F') K := by
    simp only [bregDiv]
    fun_prop
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hK_ne h_cont
  exact ⟨x, hx, hmin⟩

/-- **One step of mirror descent.** Let `K` be convex, let `x` be a mirror descent step on `K`
from `a` with derivative `F'`, and let `F` have derivative `G` within `K` at `x`. Then for every
`u ∈ K`, `η y (x - u) ≤ D_F(u, a) - D_F(u, x) - D_F(x, a)`, where the divergences from `a` and
from `x` use `F'` and `G`. -/
theorem IsMirrorDescentStep.mul_apply_sub_le {y F' G : E →L[ℝ] ℝ} {a x : E}
    (h : IsMirrorDescentStep K F η y a F' x) (hK : Convex ℝ K) (hG : HasFDerivWithinAt F G K x)
    (hu : u ∈ K) :
    η * y (x - u) ≤ bregDiv F u a F' - bregDiv F u x G - bregDiv F x a F' := by
  -- up to a constant, the objective is `c ↦ (η y - F') c + F c`, minimized over `K` at `x`
  have h_min : IsMinOn (fun c ↦ (η • y - F') c + F c) K x := isMinOn_iff.mpr fun c hc ↦ by
    have := isMinOn_iff.mp h.isMinOn c hc
    simp only [bregDiv, map_sub, sub_apply, smul_apply,
      smul_eq_mul] at this ⊢
    linarith
  have h_breg := bregDiv_le_sub_of_isMinOn (hK.segment_subset h.mem hu) h_min hG
  simp only [bregDiv, map_sub, sub_apply, smul_apply,
    smul_eq_mul] at h_breg ⊢
  linarith

/-- **Regret of mirror descent from any initial play.** Let `K` be convex and `η > 0`. Let each
`a (t + 1)`, for `t < n`, be a mirror descent step on `K` from `a t` with derivative `F' t`, for
the loss `y t`, where `F` has derivative `F' (t + 1)` within `K` at `a (t + 1)`. Then for every
`u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n, y t (a t - u) ≤ (D_F(u, a 0) - D_F(u, a n)) / η + ∑ t < n, y t (a t - a (t + 1))
  - (∑ t < n, D_F(a (t + 1), a t)) / η`.
This is the telescoped inequality behind [LS, (28.10)], before any use of the convexity of `F`. -/
theorem sum_apply_sub_le_mirrorDescent (hK : Convex ℝ K) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ)
    (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha : ∀ t < n, IsMirrorDescentStep K F η (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t < n, HasFDerivWithinAt F (F' (t + 1)) K (a (t + 1))) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (bregDiv F u (a 0) (F' 0) - bregDiv F u (a n) (F' n)) / η +
        ∑ t ∈ range n, y t (a t - a (t + 1)) -
          (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
  -- split `a t - u` at `a (t + 1)` and bound the second part by the one-step inequality
  have h_step (t : ℕ) (ht : t ∈ range n) : y t (a t - u) ≤ y t (a t - a (t + 1)) +
      (bregDiv F u (a t) (F' t) - bregDiv F u (a (t + 1)) (F' (t + 1)) -
        bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
    have ht' := mem_range.mp ht
    have h_one := (ha t ht').mul_apply_sub_le hK (hF' t ht') hu
    have h_split : y t (a t - u) = y t (a t - a (t + 1)) + y t (a (t + 1) - u) := by
      rw [← map_add, sub_add_sub_cancel]
    rw [h_split, add_le_add_iff_left, le_div_iff₀ hη, mul_comm]
    exact h_one
  -- the divergences to `u` telescope
  have h_tele := sum_range_sub' (fun t ↦ bregDiv F u (a t) (F' t)) n
  refine (sum_le_sum h_step).trans_eq ?_
  rw [sum_add_distrib, ← sum_div, sum_sub_distrib, h_tele, sub_div]
  ring

/-- Plays of mirror descent started in `K` stay in `K`. -/
private lemma mem_of_isMirrorDescentStep {y : ℕ → E →L[ℝ] ℝ} {a : ℕ → E} {F' : ℕ → E →L[ℝ] ℝ}
    (ha0 : a 0 ∈ K) (ha : ∀ t < n, IsMirrorDescentStep K F η (y t) (a t) (F' t) (a (t + 1))) :
    ∀ t ≤ n, a t ∈ K
  | 0, _ => ha0
  | t + 1, ht => (ha t ht).mem

/-- **Regret of mirror descent** [LS, Theorem 28.4], first bound. Let `F` be convex on `K` and
`η > 0`. Let `a 0 ∈ K` minimize `F` over `K` and let each `a (t + 1)`, for `t < n`, be a mirror
descent step on `K` from `a t` with derivative `F' t`, for the loss `y t`, where `F` has
derivative `F' t` within `K` at `a t` for `t ≤ n`. Then for every `u ∈ K`, with `D_F` the
Bregman divergence,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η + ∑ t < n, y t (a t - a (t + 1))
  - (∑ t < n, D_F(a (t + 1), a t)) / η`.
[LS] assumes `F` Legendre; the proof only uses its convexity on `K` and the derivatives at the
plays. -/
theorem mirrorDescent_regret_le (hF : ConvexOn ℝ K F) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ)
    (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0 : IsMinOn F K (a 0)) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F η (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ (F u - F (a 0)) / η +
      ∑ t ∈ range n, y t (a t - a (t + 1)) -
        (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
  have h := sum_apply_sub_le_mirrorDescent hF.1 hη y a F' ha (fun t ht ↦ hF' (t + 1) ht) hu
  -- `D_F(u, a 0) ≤ F u - F (a 0)` as `a 0` minimizes `F`, and `D_F(u, a n) ≥ 0` by convexity
  have h_init : bregDiv F u (a 0) (F' 0) ≤ F u - F (a 0) :=
    bregDiv_le_sub_of_isMinOn_self (hF.1.segment_subset ha0K hu) ha0 (hF' 0 (Nat.zero_le n))
  have h_last : 0 ≤ bregDiv F u (a n) (F' n) :=
    (hF' n le_rfl).hasSubgradientWithinAt hF (mem_of_isMirrorDescentStep ha0K ha n le_rfl) u hu
  have h_div : (bregDiv F u (a 0) (F' 0) - bregDiv F u (a n) (F' n)) / η ≤ (F u - F (a 0)) / η :=
    div_le_div_of_nonneg_right (by linarith) hη.le
  linarith

/-- **Regret of mirror descent through the unconstrained steps** [LS, (28.11)]. Let `F` be convex
on a set `D` containing the convex set `K`, and let `η > 0`. Let `a 0 ∈ K` and let each
`a (t + 1)`, for `t < n`, be a mirror descent step on `K` from `a t` with derivative `F' t`, for
the loss `y t`, where `F` has derivative `F' t` within `K` at `a t` for `t ≤ n`. Let `b (t + 1) ∈ D`
be a point where `F` has derivative `G t = F' t - η y t` within `D`, the unconstrained step of
[LS, (28.9)]. Then for every `u ∈ K`, with `D_F` the Bregman divergence,
`∑ t < n, y t (a t - u) ≤ (D_F(u, a 0) + ∑ t < n, D_F(a t, b (t + 1))) / η`. -/
theorem mirrorDescent_regret_le_bregDiv_add_sum_bregDiv (hF : ConvexOn ℝ D F) (hKD : K ⊆ D)
    (hK : Convex ℝ K) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha0K : a 0 ∈ K) (ha : ∀ t < n, IsMirrorDescentStep K F η (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (b : ℕ → E) (G : ℕ → E →L[ℝ] ℝ)
    (hG : ∀ t < n, G t = F' t - η • y t) (hb : ∀ t < n, b (t + 1) ∈ D)
    (hGb : ∀ t < n, HasFDerivWithinAt F (G t) D (b (t + 1))) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (bregDiv F u (a 0) (F' 0) + ∑ t ∈ range n, bregDiv F (a t) (b (t + 1)) (G t)) / η := by
  have h := sum_apply_sub_le_mirrorDescent hK hη y a F' ha (fun t ht ↦ hF' (t + 1) ht) hu
  have h_mem := mem_of_isMirrorDescentStep ha0K ha
  have h_last : 0 ≤ bregDiv F u (a n) (F' n) :=
    (hF' n le_rfl).hasSubgradientWithinAt (hF.subset hKD hK) (h_mem n le_rfl) u hu
  -- `η y t (a t - a (t + 1)) = D_F(a (t + 1), a t) + D_F(a t, b) - D_F(a (t + 1), b)`
  have h_stab (t : ℕ) (ht : t ∈ range n) : η * y t (a t - a (t + 1)) ≤
      bregDiv F (a (t + 1)) (a t) (F' t) + bregDiv F (a t) (b (t + 1)) (G t) := by
    have ht' := mem_range.mp ht
    have h_three := bregDiv_three_point (f := F) (z := a (t + 1)) (x := a t) (y := b (t + 1))
      (J_x := F' t) (J_y := G t)
    have h_nonneg : 0 ≤ bregDiv F (a (t + 1)) (b (t + 1)) (G t) :=
      (hGb t ht').hasSubgradientWithinAt hF (hb t ht') _ (hKD (h_mem (t + 1) ht'))
    rw [hG t ht'] at h_three h_nonneg ⊢
    simp only [map_sub, sub_apply, smul_apply,
      smul_eq_mul] at h_three ⊢
    linarith
  have h_sum : ∑ t ∈ range n, y t (a t - a (t + 1)) ≤
      (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t) +
        ∑ t ∈ range n, bregDiv F (a t) (b (t + 1)) (G t)) / η := by
    rw [le_div_iff₀ hη, sum_mul, ← sum_add_distrib]
    exact sum_le_sum fun t ht ↦ by rw [mul_comm]; exact h_stab t ht
  have h_div : (bregDiv F u (a 0) (F' 0) - bregDiv F u (a n) (F' n)) / η ≤
      bregDiv F u (a 0) (F' 0) / η := div_le_div_of_nonneg_right (by linarith) hη.le
  rw [add_div] at h_sum ⊢
  linarith

/-- **Regret of mirror descent** [LS, Theorem 28.4], second bound. Under the assumptions of
`mirrorDescent_regret_le_bregDiv_add_sum_bregDiv`, if moreover `a 0` minimizes `F` over `K`,
then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0) + ∑ t < n, D_F(a t, b (t + 1))) / η`. -/
theorem mirrorDescent_regret_le_sub_add_sum_bregDiv (hF : ConvexOn ℝ D F) (hKD : K ⊆ D)
    (hK : Convex ℝ K) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha0 : IsMinOn F K (a 0)) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F η (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (b : ℕ → E) (G : ℕ → E →L[ℝ] ℝ)
    (hG : ∀ t < n, G t = F' t - η • y t) (hb : ∀ t < n, b (t + 1) ∈ D)
    (hGb : ∀ t < n, HasFDerivWithinAt F (G t) D (b (t + 1))) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (F u - F (a 0) + ∑ t ∈ range n, bregDiv F (a t) (b (t + 1)) (G t)) / η := by
  refine (mirrorDescent_regret_le_bregDiv_add_sum_bregDiv hF hKD hK hη y a F' ha0K ha hF' b G hG
    hb hGb hu).trans (div_le_div_of_nonneg_right ?_ hη.le)
  -- `D_F(u, a 0) ≤ F u - F (a 0)` as `a 0` minimizes `F`
  have := bregDiv_le_sub_of_isMinOn_self (hK.segment_subset ha0K hu) ha0 (hF' 0 (Nat.zero_le n))
  linarith

/-- **Regret of mirror descent with a strongly convex potential** [LS, Corollary 28.8]. Under the
assumptions of `mirrorDescent_regret_le`, if the potential `F` is `m`-strongly convex on `K` for
the norm of `E`, with `m > 0`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ (F u - F (a 0)) / η + η / (2 m) ∑ t < n, ‖y t‖ ^ 2`,
where `‖y t‖` is the operator norm of the loss, the dual norm of the norm of `E`. [LS] states it
with the diameter of `K` for `F` in place of `F u - F (a 0)`. -/
theorem mirrorDescent_regret_le_of_strongConvexOn {m : ℝ} (hF : StrongConvexOn K m F)
    (hm : 0 < m) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha0 : IsMinOn F K (a 0)) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F η (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      (F u - F (a 0)) / η + η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 := by
  have h := mirrorDescent_regret_le (strongConvexOn_zero.mp (hF.mono hm.le)) hη y a F' ha0 ha0K
    ha hF' hu
  have h_stab := sum_apply_sub_sub_bregDiv_le_of_strongConvexOn hF hm hη y a
    (mem_of_isMirrorDescentStep ha0K ha) F' fun t ht ↦ hF' t ht.le
  linarith

end LMLExplore.OnlineLearning
