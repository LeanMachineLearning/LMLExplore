/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LMLExplore.OnlineLearning.FTRL.Basic
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Subgradient.Deriv

/-!
# Mirror descent

Online linear optimization on a set `K` of a real normed space `E`, with losses
`y t : E →L[ℝ] ℝ` in the dual of `E`, as in `LMLExplore.OnlineLearning.FTRL.Basic`.
**Mirror descent** with potential `F` and learning rate `η` starts at a minimizer `a 0` of `F`
over `K` [LS, (28.1)] and, after the loss `y t` of round `t`, plays a minimizer over `K` of
`b ↦ η y t b + D_F(b, a t)` [LS, (28.2)], where `D_F(b, a) = F b - F a - F'(b - a)` is the
Bregman divergence of `F` for a derivative `F'` of `F` at `a`. Where FTRL regularizes the
cumulative loss, mirror descent only uses the last loss and the last play. The learning rate may
change over the rounds: with nonincreasing learning rates `η t`, the step of round `t` uses `η t`,
and the regret bound holds for every horizon, without tuning the rate to it. Every regret bound
of this file is derived from one inequality for any sequence of positive learning rates, which
sums the Bregman divergences to the comparator by parts: the bounds for a constant rate are its
case of a constant sequence.

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
* `apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt`: for `F` convex on `D`, the stability term
  `y (a - b) - D_F(b, a) / η` at every `b ∈ D` is at most its value at the unconstrained step `x`,
  and `apply_sub_sub_bregDiv_div_le_bregDiv_div`: that value is `D_F(a, x) / η`.
* `IsMirrorDescentStep.mul_apply_sub_le`: the one-step inequality
  `η y (x - u) ≤ D_F(u, a) - D_F(u, x) - D_F(x, a)`, and its form
  `IsMirrorDescentStep.apply_sub_le` for `η > 0`, which splits `y (a - u)` at `x`.
* `mem_of_isMirrorDescentStep`: plays of mirror descent started in `K` stay in `K`.
* `sum_apply_sub_le_mirrorDescent`: for any learning rates `η t > 0` and any initial play, with
  `d t = D_F(u, a t)`, the regret against `u` is at most
  `d 0 / η 0 + ∑ t < n - 1, (1 / η (t + 1) - 1 / η t) * d (t + 1) - d n / η (n - 1)
    + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
  Every regret bound below is derived from it.
* `mirrorDescent_regret_le_of_antitone`: with nonincreasing learning rates `η t` and divergences
  `D_F(u, a t) ≤ D`, the regret is at most
  `D / η (n - 1) + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
* `mirrorDescent_regret_le_of_strongConvexOn_of_antitone`: [Ora, Theorem 6.11], its form
  `D / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2` for an `m`-strongly convex potential.
* `mirrorDescent_regret_le_add_sum_bregDiv_of_antitone`: its form
  `B / η (n - 1) + ∑ t < n, D_F(a t, b (t + 1)) / η t`, for divergences `D_F(u, a t) ≤ B`, through
  the unconstrained steps `b (t + 1)` [LS, (28.11)].
* `mirrorDescent_regret_le_bregDiv_div`: for a constant learning rate `η` and any initial play,
  the bound `D_F(u, a 0) / η + ∑ t < n, y t (a t - a (t + 1)) - (∑ t < n, D_F(a (t + 1), a t)) / η`.
* `mirrorDescent_regret_le`: [LS, Theorem 28.4], first bound.
* `mirrorDescent_regret_le_bregDiv_add_sum_bregDiv`: [LS, (28.11)], the bound
  `(D_F(u, a 0) + ∑ t < n, D_F(a t, b (t + 1))) / η` through the unconstrained steps `b (t + 1)`,
  for any initial play.
* `mirrorDescent_regret_le_sub_add_sum_bregDiv`: [LS, Theorem 28.4], second bound.
* `mirrorDescent_regret_le_of_strongConvexOn`: [LS, Corollary 28.8] for mirror descent.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
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

/-- **The stability term is largest at the unconstrained step.** Let `F` be convex on `D`, let
`η > 0`, and let `x ∈ D` be a point where `F` has derivative `J - η y` within `D`. Then for every
`b ∈ D`, `y (a - b) - D_F(b, a) / η ≤ y (a - x) - D_F(x, a) / η`, where the Bregman divergences
from `a` use the linear map `J`. The point `a` need not lie in `D`. -/
theorem apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt (hF : ConvexOn ℝ D F) (hη : 0 < η)
    (y J : E →L[ℝ] ℝ) (a : E) {b x : E} (hb : b ∈ D) (hx : x ∈ D)
    (hJx : HasFDerivWithinAt F (J - η • y) D x) :
    y (a - b) - bregDiv F b a J / η ≤ y (a - x) - bregDiv F x a J / η := by
  -- `x` minimizes the objective `c ↦ η y c + D_F(c, a)` of a mirror descent step over `D`
  have h_min := isMinOn_iff.mp
    (isMinOn_mul_apply_add_bregDiv_of_hasFDerivWithinAt rfl hF hx hJx a) b hb
  have h_eq (c : E) :
      y (a - c) - bregDiv F c a J / η = y a - (η * y c + bregDiv F c a J) / η := by
    rw [map_sub]
    field_simp
    ring
  rw [h_eq, h_eq]
  exact sub_le_sub_left (div_le_div_of_nonneg_right h_min hη.le) _

/-- **The stability term through the unconstrained step** [LS, (28.11)]. Under the assumptions of
`apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt`, for every `b ∈ D`,
`y (a - b) - D_F(b, a) / η ≤ D_F(a, x) / η`, where the divergence from `a` uses `J` and the
divergence from `x` uses its derivative `J - η y`. -/
theorem apply_sub_sub_bregDiv_div_le_bregDiv_div (hF : ConvexOn ℝ D F) (hη : 0 < η)
    (y J : E →L[ℝ] ℝ) (a : E) {b x : E} (hb : b ∈ D) (hx : x ∈ D)
    (hJx : HasFDerivWithinAt F (J - η • y) D x) :
    y (a - b) - bregDiv F b a J / η ≤ bregDiv F a x (J - η • y) / η := by
  refine (apply_sub_sub_bregDiv_div_le_of_hasFDerivWithinAt hF hη y J a hb hx hJx).trans_eq ?_
  -- `D_F(x, a) + D_F(a, x) = η y (a - x)` for the derivatives `J` at `a` and `J - η y` at `x`
  have h := bregDiv_add_swap (f := F) (x := a) (y := x) (J_x := J) (J_y := J - η • y)
  simp only [sub_sub_cancel, smul_apply, smul_eq_mul] at h
  rw [eq_div_iff hη.ne', sub_mul, div_mul_cancel₀ _ hη.ne']
  linarith

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

/-- **One step of mirror descent, split at the step.** Under the assumptions of
`IsMirrorDescentStep.mul_apply_sub_le`, if `η > 0`, then for every `u ∈ K`,
`y (a - u) ≤ y (a - x) + (D_F(u, a) - D_F(u, x) - D_F(x, a)) / η`. -/
theorem IsMirrorDescentStep.apply_sub_le {y F' G : E →L[ℝ] ℝ} {a x : E}
    (h : IsMirrorDescentStep K F η y a F' x) (hK : Convex ℝ K) (hη : 0 < η)
    (hG : HasFDerivWithinAt F G K x) (hu : u ∈ K) :
    y (a - u) ≤ y (a - x) + (bregDiv F u a F' - bregDiv F u x G - bregDiv F x a F') / η := by
  have h_split : y (a - u) = y (a - x) + y (x - u) := by rw [← map_add, sub_add_sub_cancel]
  rw [h_split, add_le_add_iff_left, le_div_iff₀ hη, mul_comm]
  exact h.mul_apply_sub_le hK hG hu

/-- **Regret of mirror descent from any initial play.** Let `K` be convex and let the learning
rates satisfy `η t > 0` for `t < n`. Let each `a (t + 1)`, for `t < n`, be a mirror descent step on
`K` from `a t` with derivative `F' t` and learning rate `η t`, for the loss `y t`, where `F` has
derivative `F' (t + 1)` within `K` at `a (t + 1)`. Then for every `u ∈ K`, with `D_F` the Bregman
divergence and `d t = D_F(u, a t)` for the derivative `F' t`,
`∑ t < n, y t (a t - u) ≤ d 0 / η 0 + ∑ t < n - 1, (1 / η (t + 1) - 1 / η t) * d (t + 1)
  - d n / η (n - 1) + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
This is the telescoped inequality behind [LS, (28.10)] and [Ora, Theorem 6.11], before any use of
the convexity of `F`: the terms `(d t - d (t + 1)) / η t` of the rounds are summed by parts. For a
constant learning rate the middle sum vanishes, and with nonincreasing rates its coefficients are
nonnegative. -/
theorem sum_apply_sub_le_mirrorDescent (hK : Convex ℝ K) {η : ℕ → ℝ} (hη : ∀ t < n, 0 < η t)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha : ∀ t < n, IsMirrorDescentStep K F (η t) (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t < n, HasFDerivWithinAt F (F' (t + 1)) K (a (t + 1))) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      bregDiv F u (a 0) (F' 0) / η 0 +
        ∑ t ∈ range (n - 1), ((η (t + 1))⁻¹ - (η t)⁻¹) * bregDiv F u (a (t + 1)) (F' (t + 1)) -
          bregDiv F u (a n) (F' n) / η (n - 1) +
        ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) := by
  set d : ℕ → ℝ := fun t ↦ bregDiv F u (a t) (F' t)
  -- split `a t - u` at `a (t + 1)` and bound the second part by the one-step inequality
  have h_step (t : ℕ) (ht : t ∈ range n) : y t (a t - u) ≤
      (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) +
        (d t - d (t + 1)) / η t := by
    have ht' := mem_range.mp ht
    have h_one := (ha t ht').apply_sub_le hK (hη t ht') (hF' t ht') hu
    rw [sub_div, sub_div] at h_one
    rw [sub_div]
    linarith
  -- summation by parts of the divergences to `u`
  have h_parts (m : ℕ) : ∑ t ∈ range m, (d t - d (t + 1)) / η t =
      d 0 / η 0 + ∑ t ∈ range (m - 1), ((η (t + 1))⁻¹ - (η t)⁻¹) * d (t + 1) -
        d m / η (m - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rcases m with _ | m
      · simp [sub_div]
      · rw [sum_range_succ, ih, Nat.add_sub_cancel, Nat.add_sub_cancel, sum_range_succ]
        simp only [div_eq_mul_inv]
        ring
  refine (sum_le_sum h_step).trans_eq ?_
  rw [sum_add_distrib, h_parts n, add_comm]

/-- **Plays of mirror descent stay in `K`.** If `a 0 ∈ K` and each `a (t + 1)`, for `t < n`, is a
mirror descent step on `K` from `a t`, then `a t ∈ K` for every `t ≤ n`. -/
theorem mem_of_isMirrorDescentStep {η : ℕ → ℝ} {y : ℕ → E →L[ℝ] ℝ} {a : ℕ → E}
    {F' : ℕ → E →L[ℝ] ℝ} (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F (η t) (y t) (a t) (F' t) (a (t + 1))) :
    ∀ t ≤ n, a t ∈ K
  | 0, _ => ha0
  | t + 1, ht => (ha t ht).mem

/-- **Regret of mirror descent with a constant learning rate, from any initial play.** Let `F` be
convex on `K` and `η > 0`. Let `a 0 ∈ K` and let each `a (t + 1)`, for `t < n`, be a mirror
descent step on `K` from `a t` with derivative `F' t`, for the loss `y t`, where `F` has
derivative `F' t` within `K` at `a t` for `t ≤ n`. Then for every `u ∈ K`, with `D_F` the Bregman
divergence,
`∑ t < n, y t (a t - u) ≤ D_F(u, a 0) / η + ∑ t < n, y t (a t - a (t + 1))
  - (∑ t < n, D_F(a (t + 1), a t)) / η`.
This is the case of a constant sequence of `sum_apply_sub_le_mirrorDescent`. -/
theorem mirrorDescent_regret_le_bregDiv_div (hF : ConvexOn ℝ K F) (hη : 0 < η)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F η (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ bregDiv F u (a 0) (F' 0) / η +
      ∑ t ∈ range n, y t (a t - a (t + 1)) -
        (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η := by
  have h := sum_apply_sub_le_mirrorDescent (η := fun _ ↦ η) hF.1 (fun _ _ ↦ hη) y a F' ha
    (fun t ht ↦ hF' (t + 1) ht) hu
  simp only [sub_self, zero_mul, sum_const_zero, add_zero, sum_sub_distrib, ← sum_div] at h
  -- the last divergence `D_F(u, a n)` is nonnegative by convexity
  have h_last : 0 ≤ bregDiv F u (a n) (F' n) / η :=
    div_nonneg ((hF' n le_rfl).hasSubgradientWithinAt hF
      (mem_of_isMirrorDescentStep ha0K ha n le_rfl) u hu) hη.le
  linarith

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
  have h := mirrorDescent_regret_le_bregDiv_div hF hη y a F' ha0K ha hF' hu
  -- `D_F(u, a 0) ≤ F u - F (a 0)` as `a 0` minimizes `F`
  have h_init : bregDiv F u (a 0) (F' 0) / η ≤ (F u - F (a 0)) / η :=
    div_le_div_of_nonneg_right (bregDiv_le_sub_of_isMinOn_self (hF.1.segment_subset ha0K hu) ha0
      (hF' 0 (Nat.zero_le n))) hη.le
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
  have h := mirrorDescent_regret_le_bregDiv_div (hF.subset hKD hK) hη y a F' ha0K ha hF' hu
  have h_mem := mem_of_isMirrorDescentStep ha0K ha
  -- the stability term of round `t` is at most `D_F(a t, b (t + 1)) / η`
  have h_stab : ∑ t ∈ range n, y t (a t - a (t + 1)) -
      (∑ t ∈ range n, bregDiv F (a (t + 1)) (a t) (F' t)) / η ≤
        (∑ t ∈ range n, bregDiv F (a t) (b (t + 1)) (G t)) / η := by
    rw [sum_div, sum_div, ← sum_sub_distrib]
    refine sum_le_sum fun t ht ↦ ?_
    have ht' := mem_range.mp ht
    have hGb' := hGb t ht'
    rw [hG t ht'] at hGb' ⊢
    exact apply_sub_sub_bregDiv_div_le_bregDiv_div hF hη (y t) (F' t) (a t)
      (hKD (h_mem (t + 1) ht')) (hb t ht') hGb'
  rw [add_div]
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

section Antitone

variable {η : ℕ → ℝ}

/-- **Regret of mirror descent with nonincreasing learning rates**, before the use of strong
convexity [Ora, Theorem 6.11]. Let `F` be convex on `K` and let the learning rates `η t > 0` be
nonincreasing. Let `a 0 ∈ K` and let each `a (t + 1)`, for `t < n`, be a mirror descent step on
`K` from `a t` with derivative `F' t` and learning rate `η t`, for the loss `y t`, where `F` has
derivative `F' t` within `K` at `a t` for `t ≤ n`. If `D ≥ 0` bounds the Bregman divergences
`D_F(u, a t)` for `t < n`, then
`∑ t < n, y t (a t - u)
  ≤ D / η (n - 1) + ∑ t < n, (y t (a t - a (t + 1)) - D_F(a (t + 1), a t) / η t)`.
The play `a 0` need not minimize `F`. -/
theorem mirrorDescent_regret_le_of_antitone (hF : ConvexOn ℝ K F) (hη : ∀ t, 0 < η t)
    (hη_anti : Antitone η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha0K : a 0 ∈ K) (ha : ∀ t < n, IsMirrorDescentStep K F (η t) (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) {D : ℝ} (hD : 0 ≤ D)
    (hDu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ D) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ D / η (n - 1) +
      ∑ t ∈ range n, (y t (a t - a (t + 1)) - bregDiv F (a (t + 1)) (a t) (F' t) / η t) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa using div_nonneg hD (hη _).le
  have h := sum_apply_sub_le_mirrorDescent hF.1 (fun t _ ↦ hη t) y a F' ha
    (fun t ht ↦ hF' (t + 1) ht) hu
  -- the last divergence `D_F(u, a n)` is nonnegative by convexity
  have h_last : 0 ≤ bregDiv F u (a n) (F' n) / η (n - 1) :=
    div_nonneg ((hF' n le_rfl).hasSubgradientWithinAt hF
      (mem_of_isMirrorDescentStep ha0K ha n le_rfl) u hu) (hη _).le
  -- with nonincreasing rates, the coefficients `1 / η (t + 1) - 1 / η t` are nonnegative, and the
  -- divergences they weigh are at most `D`
  have h_sum : ∑ t ∈ range (n - 1), ((η (t + 1))⁻¹ - (η t)⁻¹) * bregDiv F u (a (t + 1)) (F' (t + 1))
      ≤ D * ((η (n - 1))⁻¹ - (η 0)⁻¹) := by
    rw [← sum_range_sub (fun t ↦ (η t)⁻¹), mul_sum]
    refine sum_le_sum fun t ht ↦ ?_
    rw [mul_comm D]
    exact mul_le_mul_of_nonneg_left (hDu (t + 1) (by have := mem_range.mp ht; omega))
      (sub_nonneg.mpr (inv_anti₀ (hη (t + 1)) (hη_anti t.le_succ)))
  have h_init : bregDiv F u (a 0) (F' 0) / η 0 ≤ D / η 0 :=
    div_le_div_of_nonneg_right (hDu 0 hn) (hη 0).le
  have h_eq : D / η 0 + D * ((η (n - 1))⁻¹ - (η 0)⁻¹) = D / η (n - 1) := by ring
  linarith

/-- **Regret of mirror descent with nonincreasing learning rates and a strongly convex potential**
[Ora, Theorem 6.11]. Under the assumptions of `mirrorDescent_regret_le_of_antitone`, if the
potential `F` is `m`-strongly convex on `K` for the norm of `E`, with `m > 0`, then for every
`u ∈ K`,
`∑ t < n, y t (a t - u) ≤ D / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2`,
where `‖y t‖` is the operator norm of the loss, the dual norm of the norm of `E`. -/
theorem mirrorDescent_regret_le_of_strongConvexOn_of_antitone {m : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F (η t) (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) {D : ℝ} (hD : 0 ≤ D)
    (hDu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ D) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ D / η (n - 1) + ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2 := by
  refine (mirrorDescent_regret_le_of_antitone (strongConvexOn_zero.mp (hF.mono hm.le)) hη hη_anti
    y a F' ha0K ha hF' hD hDu hu).trans (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  have ht := mem_range.mp ht
  have h_mem := mem_of_isMirrorDescentStep ha0K ha
  exact apply_sub_sub_div_le_of_mul_norm_sq_le hm (hη t) (y t)
    (hF.mul_norm_sub_sq_le_bregDiv (h_mem t ht.le) (h_mem (t + 1) ht) (hF' t ht.le))

/-- **Regret of mirror descent with nonincreasing learning rates through the unconstrained steps**
[LS, (28.11); Ora, Theorem 6.11]. Let `F` be convex on a set `D` containing the convex set `K`,
and let the learning rates `η t > 0` be nonincreasing. Let `a 0 ∈ K` and let each `a (t + 1)`, for
`t < n`, be a mirror descent step on `K` from `a t` with derivative `F' t` and learning rate `η t`,
for the loss `y t`, where `F` has derivative `F' t` within `K` at `a t` for `t ≤ n`. Let
`b (t + 1) ∈ D` be a point where `F` has derivative `G t = F' t - η t y t` within `D`, the
unconstrained step of round `t`. If `B ≥ 0` bounds the Bregman divergences `D_F(u, a t)` for
`t < n`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ B / η (n - 1) + ∑ t < n, D_F(a t, b (t + 1)) / η t`. -/
theorem mirrorDescent_regret_le_add_sum_bregDiv_of_antitone (hF : ConvexOn ℝ D F) (hKD : K ⊆ D)
    (hK : Convex ℝ K) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) (y : ℕ → E →L[ℝ] ℝ)
    (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F (η t) (y t) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) {B : ℝ} (hB : 0 ≤ B)
    (hBu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ B) (b : ℕ → E) (G : ℕ → E →L[ℝ] ℝ)
    (hG : ∀ t < n, G t = F' t - η t • y t) (hb : ∀ t < n, b (t + 1) ∈ D)
    (hGb : ∀ t < n, HasFDerivWithinAt F (G t) D (b (t + 1))) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      B / η (n - 1) + ∑ t ∈ range n, bregDiv F (a t) (b (t + 1)) (G t) / η t := by
  refine (mirrorDescent_regret_le_of_antitone (hF.subset hKD hK) hη hη_anti y a F' ha0K ha hF' hB
    hBu hu).trans (add_le_add le_rfl (sum_le_sum fun t ht ↦ ?_))
  have ht := mem_range.mp ht
  have hGb' := hGb t ht
  rw [hG t ht] at hGb' ⊢
  exact apply_sub_sub_bregDiv_div_le_bregDiv_div hF (hη t) (y t) (F' t) (a t)
    (hKD (mem_of_isMirrorDescentStep ha0K ha (t + 1) ht)) (hb t ht) hGb'

end Antitone

end LMLExplore.OnlineLearning
