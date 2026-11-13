/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.FTRL.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# FTRL on the unit ball with a logarithmic potential

On the open unit ball of a real inner product space `E`, the potential
`F a = -log (1 - ‖a‖) - ‖a‖` is the one [LS, Section 28.4] uses for follow the regularized leader
in adversarial linear bandits on the unit ball. It is differentiable on the ball with derivative
`⟪a, ·⟫ / (1 - ‖a‖)` at `a`, it vanishes at `0` and is nonnegative, and it blows up at the
boundary, which keeps the plays of FTRL away from the unit sphere.

The quantity that enters the regret is the Bregman divergence of `F`. It dominates a local
squared norm at its base point:
`D_F(b, a) ≥ ‖b - a‖ ^ 2 / (2 (1 - ‖a‖))` for all `a`, `b` in the ball. Consequently the
stability term of round `t` of FTRL is at most `η / 2 * (1 - ‖a t‖) * ‖y t‖ ^ 2`, where `‖y t‖` is
the operator norm of the loss. In the bandit algorithm of [LS, Section 28.4] the factor
`1 - ‖a t‖` cancels the variance of the importance-weighted loss estimates, which is of order
`1 / (1 - ‖a t‖)`. [LS] bounds the stability term through the Hessian of `F` at a point of the
segment `[a t, a (t + 1)]` and the stability of the plays, with an extra factor `2`; the bound at
the base point needs neither.

## Main definitions

* `unitBallPotential`: the potential `a ↦ -log (1 - ‖a‖) - ‖a‖`.

## Main statements

* `hasFDerivAt_unitBallPotential`: on the open unit ball, the potential has derivative
  `(1 - ‖a‖)⁻¹ • innerSL ℝ a` at `a`.
* `unitBallPotential_nonneg`, `unitBallPotential_le_neg_log_one_sub`: the potential is
  nonnegative on the ball and at most `-log (1 - r)` on the closed ball of radius `r < 1`, which
  bounds the diameter of that ball for `F`.
* `norm_sub_sq_div_le_bregDiv_unitBallPotential`: for `a`, `b` in the ball,
  `‖b - a‖ ^ 2 / (2 (1 - ‖a‖)) ≤ D_F(b, a)`.
* `apply_sub_sub_bregDiv_unitBallPotential_div_le`: the stability term
  `y (a - b) - D_F(b, a) / η` is at most `η / 2 * (1 - ‖a‖) * ‖y‖ ^ 2`.
* `sub_div_add_sum_apply_sub_sub_bregDiv_unitBallPotential_le`: the penalty and stability terms
  of the bound `ftrl_regret_le` are at most
  `-log (1 - r) / η + η / 2 * ∑ t < n, (1 - ‖a t‖) * ‖y t‖ ^ 2` when the plays lie in the open
  unit ball and the comparator in the closed ball of radius `r < 1`.
* `ftrl_regret_le_of_unitBallPotential`: the regret of FTRL with this potential on a convex subset
  of the closed ball of radius `r < 1` is at most
  `-log (1 - r) / η + η / 2 * ∑ t < n, (1 - ‖a t‖) * ‖y t‖ ^ 2`, the full-information bound in
  the proof of [LS, Theorem 28.11].
* `exists_ftrl_unitBallPotential`: in finite dimension, FTRL with this potential on the closed
  ball of radius `r ∈ [0, 1)` has plays.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 28.4.
-/

public section

open Finset Metric Real ContinuousLinearMap
open scoped RealInnerProductSpace Bregman

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] {a b u : E} {r η : ℝ} {n : ℕ} {K : Set E}

/-- The potential `F a = -log (1 - ‖a‖) - ‖a‖` of follow the regularized leader on the unit ball
[LS, Section 28.4]. It is meaningful on the open unit ball, where it is differentiable,
nonnegative and tends to infinity at the boundary. -/
noncomputable def unitBallPotential (a : E) : ℝ :=
  -log (1 - ‖a‖) - ‖a‖

lemma unitBallPotential_def (a : E) : unitBallPotential a = -log (1 - ‖a‖) - ‖a‖ := (rfl)

@[simp]
lemma unitBallPotential_zero : unitBallPotential (0 : E) = 0 := by
  simp [unitBallPotential_def]

/-- The potential is nonnegative on the open unit ball. -/
lemma unitBallPotential_nonneg (ha : ‖a‖ < 1) : 0 ≤ unitBallPotential a := by
  have := log_le_sub_one_of_pos (sub_pos.2 ha)
  rw [unitBallPotential_def]
  linarith

/-- On the closed ball of radius `r < 1`, the potential is at most `-log (1 - r)`. Since it
vanishes at `0` and is nonnegative, this bounds the diameter `sup F - inf F` of that ball for
the potential [LS, proof of Theorem 28.11]. -/
lemma unitBallPotential_le_neg_log_one_sub (ha : ‖a‖ ≤ r) (hr : r < 1) :
    unitBallPotential a ≤ -log (1 - r) := by
  have := log_le_log (sub_pos.2 hr) (sub_le_sub_left ha 1)
  rw [unitBallPotential_def]
  linarith [norm_nonneg a]

variable [InnerProductSpace ℝ E]

/-- **Derivative of the potential.** On the open unit ball, the potential `unitBallPotential`
has derivative `⟪a, ·⟫ / (1 - ‖a‖)`, that is `(1 - ‖a‖)⁻¹ • innerSL ℝ a`, at `a`. -/
theorem hasFDerivAt_unitBallPotential (ha : ‖a‖ < 1) :
    HasFDerivAt unitBallPotential ((1 - ‖a‖)⁻¹ • innerSL ℝ a) a := by
  rcases eq_or_ne a 0 with rfl | ha0
  · -- at `0`, the potential is `O(‖h‖ ^ 2)`, by `-log (1 - s) - s ≤ s / (1 - s) - s`
    simp only [norm_zero, sub_zero, inv_one, map_zero, smul_zero]
    refine HasFDerivAt.of_isLittleO ?_
    simp only [unitBallPotential_zero, sub_zero, zero_apply]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : E ↦ ‖h‖ ^ 2) ?_
      (Asymptotics.isLittleO_norm_pow_id one_lt_two)
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [ball_mem_nhds (0 : E) one_half_pos] with h hh
    rw [mem_ball_zero_iff] at hh
    have h1 : 0 < 1 - ‖h‖ := by linarith
    have hlog := log_le_sub_one_of_pos (inv_pos.2 h1)
    rw [log_inv] at hlog
    have h_nonneg := unitBallPotential_nonneg (a := h) (by linarith)
    have h_le : unitBallPotential h ≤ 2 * ‖h‖ ^ 2 := by
      have h_inv : (1 - ‖h‖)⁻¹ - 1 - ‖h‖ = ‖h‖ ^ 2 / (1 - ‖h‖) := by
        field_simp
        ring
      have : ‖h‖ ^ 2 / (1 - ‖h‖) ≤ 2 * ‖h‖ ^ 2 := by
        rw [div_le_iff₀ h1]
        nlinarith [sq_nonneg ‖h‖]
      rw [unitBallPotential_def]
      linarith
    rw [Real.norm_of_nonneg h_nonneg, Real.norm_of_nonneg (by positivity)]
    exact h_le
  · -- away from `0`, the norm is `√(‖·‖ ^ 2)`, differentiable, and the chain rule applies
    have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha0
    have h1 : 0 < 1 - ‖a‖ := sub_pos.2 ha
    have h_norm : HasFDerivAt (fun x : E ↦ √(‖x‖ ^ 2)) ((1 / (2 * √(‖a‖ ^ 2))) •
        (2 • innerSL ℝ a)) a :=
      (hasStrictFDerivAt_norm_sq a).hasFDerivAt.sqrt (by positivity)
    simp only [sqrt_sq (norm_nonneg _)] at h_norm
    have h_log := (h_norm.const_sub 1).log h1.ne'
    convert (h_log.neg.sub h_norm) using 1
    · ext x
      simp [unitBallPotential_def]
    · ext v
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, sub_apply, neg_apply,
        nsmul_eq_mul, Nat.cast_ofNat]
      field_simp
      ring

/-- The potential is continuous on the open unit ball. -/
lemma continuousOn_unitBallPotential : ContinuousOn unitBallPotential (ball (0 : E) 1) := fun _ ha ↦
  (hasFDerivAt_unitBallPotential (mem_ball_zero_iff.1 ha)).continuousAt.continuousWithinAt

/-- The radial profile `φ s = -log (1 - s) - s` of the potential satisfies
`D_φ(r, s) ≥ (r - s) ^ 2 / (2 (1 - s))` on `[0, 1)`: the difference `g` between the two sides,
as a function of `r`, has derivative `r / (1 - r) - r / (1 - s)`, of the sign of `r - s`, and
vanishes at `r = s`. -/
private lemma sq_sub_div_le_bregDiv_radial {r s : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    (r - s) ^ 2 / (2 * (1 - s)) ≤
      (-log (1 - r) - r) - (-log (1 - s) - s) - s / (1 - s) * (r - s) := by
  have h1s : 0 < 1 - s := sub_pos.2 hs1
  set g : ℝ → ℝ := fun x ↦ (-log (1 - x) - x) - (-log (1 - s) - s) - s / (1 - s) * (x - s) -
    (x - s) ^ 2 / (2 * (1 - s)) with hg
  have hg' (x : ℝ) (hx : x < 1) : HasDerivAt g (x / (1 - x) - x / (1 - s)) x := by
    have h1x : 0 < 1 - x := sub_pos.2 hx
    have hlog := ((hasDerivAt_id x).const_sub 1).log h1x.ne'
    have h := ((((hlog.neg.sub (hasDerivAt_id x)).sub_const ((-log (1 - s) - s))).sub
      (((hasDerivAt_id x).sub_const s).const_mul (s / (1 - s)))).sub
      ((((hasDerivAt_id x).sub_const s).pow 2).div_const (2 * (1 - s))))
    convert h using 1
    · funext y
      simp [hg]
    · simp only [id_eq, Nat.cast_ofNat]
      field_simp
      ring
  have hcont (D : Set ℝ) (hD : ∀ x ∈ D, x < 1) : ContinuousOn g D :=
    fun x hx ↦ (hg' x (hD x hx)).continuousAt.continuousWithinAt
  have hgs : g s = 0 := by simp [hg]
  suffices 0 ≤ g r by simp only [hg] at this; linarith
  rw [← hgs]
  rcases le_total s r with hsr | hrs
  · -- on `[s, r]`, `x / (1 - x) ≥ x / (1 - s)`, so `g` is monotone
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x ↦ x / (1 - x) - x / (1 - s))
      (convex_Icc s r)
      (hcont _ fun x hx ↦ hx.2.trans_lt hr1) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      (Set.left_mem_Icc.2 hsr) (Set.right_mem_Icc.2 hsr) hsr
    · rw [interior_Icc] at hx
      exact (hg' x (hx.2.trans hr1)).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := hs0.trans hx.1.le
      have h1x : 0 < 1 - x := by linarith [hx.2]
      have := div_le_div_of_nonneg_left hx0 h1x (by linarith [hx.1] : 1 - x ≤ 1 - s)
      linarith
  · -- on `[r, s]`, `x / (1 - x) ≤ x / (1 - s)`, so `g` is antitone
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x ↦ x / (1 - x) - x / (1 - s))
      (convex_Icc r s)
      (hcont _ fun x hx ↦ hx.2.trans_lt hs1) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      (Set.left_mem_Icc.2 hrs) (Set.right_mem_Icc.2 hrs) hrs
    · rw [interior_Icc] at hx
      exact (hg' x (hx.2.trans hs1)).hasDerivWithinAt
    · rw [interior_Icc] at hx
      have hx0 : 0 ≤ x := hr0.trans hx.1.le
      have := div_le_div_of_nonneg_left hx0 h1s (by linarith [hx.2] : 1 - s ≤ 1 - x)
      linarith

/-- **Local strong convexity of the potential.** For `a`, `b` in the open unit ball, the Bregman
divergence of `unitBallPotential` dominates the squared distance scaled by `1 / (1 - ‖a‖)`:
`‖b - a‖ ^ 2 / (2 (1 - ‖a‖)) ≤ D_F(b, a)`. The Hessian of `F` at `a` dominates
`1 / (1 - ‖a‖)` times the identity [LS, Section 28.4]; this is the corresponding global
lower bound on the divergence. -/
theorem norm_sub_sq_div_le_bregDiv_unitBallPotential (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    ‖b - a‖ ^ 2 / (2 * (1 - ‖a‖)) ≤
      D_[unitBallPotential](b, a, (1 - ‖a‖)⁻¹ • innerSL ℝ a) := by
  -- the divergence is the radial divergence plus `(‖b - a‖ ^ 2 - (‖b‖ - ‖a‖) ^ 2) / (2 (1 - ‖a‖))`
  have h_rad := sq_sub_div_le_bregDiv_radial (norm_nonneg b) hb (norm_nonneg a) ha
  have h1 : 0 < 1 - ‖a‖ := sub_pos.2 ha
  have h_sq : ‖b - a‖ ^ 2 = ‖b‖ ^ 2 - 2 * ⟪b, a⟫ + ‖a‖ ^ 2 := norm_sub_sq_real b a
  have h_id : (1 - ‖a‖)⁻¹ * (⟪a, b⟫ - ‖a‖ ^ 2) + ‖b - a‖ ^ 2 / (2 * (1 - ‖a‖)) =
      ‖a‖ / (1 - ‖a‖) * (‖b‖ - ‖a‖) + (‖b‖ - ‖a‖) ^ 2 / (2 * (1 - ‖a‖)) := by
    rw [h_sq, real_inner_comm a b]
    field_simp
    ring
  simp only [bregDiv, unitBallPotential_def, smul_apply, innerSL_apply_apply,
    inner_sub_right, real_inner_self_eq_norm_sq, smul_eq_mul]
  linarith

/-- **Stability of FTRL with the potential `unitBallPotential`.** For `η > 0`, a loss `y` and
`a`, `b` in the open unit ball, `y (a - b) - D_F(b, a) / η ≤ η / 2 * (1 - ‖a‖) * ‖y‖ ^ 2`, with
`‖y‖` the operator norm of the loss. [LS, Theorem 26.13] gives the bound
`η / 2 * ‖y‖ ^ 2_{(∇² F z)⁻¹}` for a point `z` of `[a, b]`. -/
theorem apply_sub_sub_bregDiv_unitBallPotential_div_le (hη : 0 < η) (y : E →L[ℝ] ℝ)
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    y (a - b) - D_[unitBallPotential](b, a, (1 - ‖a‖)⁻¹ • innerSL ℝ a) / η ≤
      η / 2 * (1 - ‖a‖) * ‖y‖ ^ 2 := by
  -- the stability bound for the modulus `(1 - ‖a‖)⁻¹`
  calc y (a - b) - D_[unitBallPotential](b, a, (1 - ‖a‖)⁻¹ • innerSL ℝ a) / η
      ≤ η / (2 * (1 - ‖a‖)⁻¹) * ‖y‖ ^ 2 :=
        apply_sub_sub_div_le_of_mul_norm_sq_le (inv_pos.2 (sub_pos.2 ha)) hη y
          ((norm_sub_sq_div_le_bregDiv_unitBallPotential ha hb).trans_eq' (by field_simp))
    _ = η / 2 * (1 - ‖a‖) * ‖y‖ ^ 2 := by field_simp

/-- **Penalty and stability terms of FTRL with the potential `unitBallPotential`**, the bound in
the proof of [LS, Theorem 28.11] on the right-hand side of `ftrl_regret_le`. Let `r < 1`, `η > 0`,
let `a t` be in the open unit ball for `t ≤ n` and let `‖u‖ ≤ r`. Then
`(F u - F (a 0)) / η + ∑ t < n, y t (a t - a (t + 1)) - (∑ t < n, D_F(a (t + 1), a t)) / η
  ≤ -log (1 - r) / η + η / 2 * ∑ t < n, (1 - ‖a t‖) * ‖y t‖ ^ 2`,
with `F = unitBallPotential`, `D_F` its Bregman divergence and `‖y t‖` the operator norm of the
loss. It bounds the integrand of `ftrl_integral_regret_le` path by path. -/
theorem sub_div_add_sum_apply_sub_sub_bregDiv_unitBallPotential_le (hr : r < 1) (hη : 0 < η)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (ha : ∀ t ≤ n, ‖a t‖ < 1) (hu : ‖u‖ ≤ r) :
    (unitBallPotential u - unitBallPotential (a 0)) / η +
        ∑ t ∈ range n, y t (a t - a (t + 1)) - (∑ t ∈ range n,
          D_[unitBallPotential](a (t + 1), a t, (1 - ‖a t‖)⁻¹ • innerSL ℝ (a t))) / η ≤
      -log (1 - r) / η + η / 2 * ∑ t ∈ range n, (1 - ‖a t‖) * ‖y t‖ ^ 2 := by
  -- the penalty is at most the diameter `-log (1 - r)`
  have h_pen : (unitBallPotential u - unitBallPotential (a 0)) / η ≤ -log (1 - r) / η := by
    refine div_le_div_of_nonneg_right ?_ hη.le
    have := unitBallPotential_nonneg (ha 0 (Nat.zero_le n))
    have := unitBallPotential_le_neg_log_one_sub hu hr
    linarith
  -- each stability term is at most `η / 2 * (1 - ‖a t‖) * ‖y t‖ ^ 2`
  have h_stab : ∑ t ∈ range n, y t (a t - a (t + 1)) - (∑ t ∈ range n,
        D_[unitBallPotential](a (t + 1), a t, (1 - ‖a t‖)⁻¹ • innerSL ℝ (a t))) / η ≤
      η / 2 * ∑ t ∈ range n, (1 - ‖a t‖) * ‖y t‖ ^ 2 := by
    refine (sum_apply_sub_sub_bregDiv_le_of_mul_norm_sq_le (m := fun t ↦ (1 - ‖a t‖)⁻¹) hη y a
      (fun t ↦ (1 - ‖a t‖)⁻¹ • innerSL ℝ (a t)) (fun t ht ↦ inv_pos.2 (sub_pos.2 (ha t ht.le)))
      fun t ht ↦ (norm_sub_sq_div_le_bregDiv_unitBallPotential (ha t ht.le)
        (ha (t + 1) ht)).trans_eq' (by field_simp)).trans_eq ?_
    rw [mul_sum]
    refine sum_congr rfl fun t _ ↦ ?_
    field_simp
  linarith

/-- **Regret of FTRL with the potential `unitBallPotential`**, the full-information bound in the
proof of [LS, Theorem 28.11]. Let `K` be a convex subset of the closed ball of radius `r < 1`, let
`η > 0`, and let each `a t`, for `t ≤ n`, be a play of FTRL on `K` with potential
`unitBallPotential` and learning rate `η` for the losses `y`. Then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ -log (1 - r) / η + η / 2 * ∑ t < n, (1 - ‖a t‖) * ‖y t‖ ^ 2`,
with `‖y t‖` the operator norm of the loss. -/
theorem ftrl_regret_le_of_unitBallPotential (hK : Convex ℝ K) (hKr : K ⊆ closedBall 0 r)
    (hr : r < 1) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (ha : ∀ t ≤ n, IsFTRLPlay K unitBallPotential η y t (a t)) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤
      -log (1 - r) / η + η / 2 * ∑ t ∈ range n, (1 - ‖a t‖) * ‖y t‖ ^ 2 := by
  have h_norm {x : E} (hx : x ∈ K) : ‖x‖ < 1 :=
    (mem_closedBall_zero_iff.1 (hKr hx)).trans_lt hr
  have h := ftrl_regret_le hK hη y a ha (fun t ↦ (1 - ‖a t‖)⁻¹ • innerSL ℝ (a t))
    (fun t ht ↦ (hasFDerivAt_unitBallPotential (h_norm (ha t ht.le).mem)).hasFDerivWithinAt) hu
  exact h.trans (sub_div_add_sum_apply_sub_sub_bregDiv_unitBallPotential_le hr hη y a
    (fun t ht ↦ h_norm (ha t ht).mem) (mem_closedBall_zero_iff.1 (hKr hu)))

/-- **FTRL with the potential `unitBallPotential` is well defined** [LS, proof of
Theorem 28.11]. In a finite-dimensional real inner product space (more generally, a proper
one), for `0 ≤ r < 1` there is a sequence of plays of FTRL on the closed ball of radius `r` with
potential `unitBallPotential`, for every learning rate and every sequence of losses. -/
theorem exists_ftrl_unitBallPotential [ProperSpace E] (hr0 : 0 ≤ r) (hr : r < 1) (η : ℝ)
    (y : ℕ → E →L[ℝ] ℝ) :
    ∃ a : ℕ → E, ∀ t, IsFTRLPlay (closedBall 0 r) unitBallPotential η y t (a t) :=
  exists_ftrl (isCompact_closedBall 0 r) ⟨0, mem_closedBall_self hr0⟩
    (continuousOn_unitBallPotential.mono (closedBall_subset_ball hr)) η y

end LMLExplore.OnlineLearning
