/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.KrichevskyTrofimov
public import LMLExplore.OnlineLearning.MirrorDescent.Learner
public import LMLExplore.OnlineLearning.Reduction.MagnitudeDirection
public import LMLExplore.OnlineLearning.SubgradientDescent

/-!
# Parameter-free learners in several dimensions

The Krichevsky–Trofimov (KT) algorithm `OnlineLearner.krichevskyTrofimovOCO L ε` is a
parameter-free learner for one-dimensional online linear optimization: for losses `g t` with
`|g t| ≤ L`, its regret against every `u ∈ ℝ` is at most
`|u| L √(2 n log (e |u| n / ε + 1)) + ε L` (`OnlineLearner.hasRegretBound_krichevskyTrofimovOCO`).
This file builds from it parameter-free learners for linear losses in several dimensions
[Ora, Sections 13.3–13.4].

* **Coordinatewise** [Ora, Algorithm 13.3, Theorem 13.9]: on `α → ℝ`, the coordinatewise product
  (`OnlineLearner.pi`) of copies of the KT algorithm, one per coordinate, has regret at most
  `L ∑ a, |u a| √(2 n log (e |u a| n / ε + 1)) + k ε L` for losses `y t` of sup norm at most `L`,
  where `k` is the number of coordinates (`OnlineLearner.hasRegretBound_pi_krichevskyTrofimovOCO`),
  hence at most `(∑ a, |u a|) L √(2 n log (e ‖u‖ n / ε + 1)) + k ε L`
  (`OnlineLearner.hasRegretBound_pi_krichevskyTrofimovOCO_norm`). The dependence on the
  comparator is through its `ℓ¹` norm.
* **In any norm** [Ora, Section 13.4]: on a real normed space `E`, the magnitude–direction
  reduction (`OnlineLearner.magnitudeDirection`) of the KT algorithm and of a learner `B` on the
  closed unit ball has regret at most `‖u‖ L √(2 n log (e ‖u‖ n / ε + 1)) + ε L` plus `‖u‖`
  times the regret of `B` against the unit vector `‖u‖⁻¹ • u`, for losses of dual norm at most `L`
  (`OnlineLearner.hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection`). With mirror descent on
  the unit ball as `B`, for an `m`-strongly convex potential whose Bregman divergences on the ball
  are at most `D`, and the learning rates `√(m D) / (L √(t + 1))`, the regret is at most
  `‖u‖ L (√(2 n log (e ‖u‖ n / ε + 1)) + 2 √(D n / m)) + ε L`
  (`OnlineLearner.hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection_mirrorDescent`). In a
  Hilbert space, the potential `‖x‖ ^ 2 / 2`, for which mirror descent is projected online
  subgradient descent, gives `‖u‖ L (√(2 n log (e ‖u‖ n / ε + 1)) + 2 √(2 n)) + ε L`
  (`OnlineLearner.hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection_mirrorDescent_norm_sq`),
  a bound in the norm of `E` and not in the `ℓ¹` norm of coordinates. [Ora, (13.2)] states this
  bound with `√(2 n)` in place of `2 √(2 n)`; the analysis of the direction learner, whose plays
  and comparators lie in a set of diameter `2`, gives the constant stated here.

None of these learners needs a learning rate tuned to the comparator, and the regret against
`u = 0` is at most `k ε L`, respectively `ε L`, at every horizon. The translation of a learner
(`OnlineLearner.HasRegretBound.map_add_left`) [Ora, Proposition 13.10] moves this point of
constant regret, and the sum of the plays of several learners (`OnlineLearner.regret_run_sum_le`)
[Ora, Theorem 13.11] combines their guarantees.

## Main statements

* `OnlineLearner.hasRegretBound_pi_krichevskyTrofimovOCO`,
  `OnlineLearner.hasRegretBound_pi_krichevskyTrofimovOCO_norm`: [Ora, Theorem 13.9], the
  coordinatewise KT algorithm.
* `OnlineLearner.hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection`: the KT algorithm as the
  magnitude learner of the magnitude–direction reduction.
* `OnlineLearner.hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection_mirrorDescent`,
  `OnlineLearner.hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection_mirrorDescent_norm_sq`:
  [Ora, Section 13.4], with mirror descent on the unit ball as the direction learner.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Sections 13.3–13.4.
* [CO18] A. Cutkosky and F. Orabona, *Black-box reductions for parameter-free online learning in
  Banach spaces*, COLT 2018.
-/

public section

open Finset Real Metric

namespace LMLExplore.OnlineLearning

namespace OnlineLearner

variable {C : Type*} {ε L : ℝ}

section Coordinatewise

variable {α : Type*} [Fintype α]

/-- **The coordinatewise Krichevsky–Trofimov algorithm** [Ora, Algorithm 13.3, Theorem 13.9]. For
`ε, L > 0`, the coordinatewise product of copies of the KT algorithm on `α → ℝ` has, for the linear
losses `x ↦ ∑ a, y t a * x a` with `‖y t‖ ≤ L` for the sup norm, the regret bound
`L ∑ a, |u a| √(2 n log (e |u a| n / ε + 1)) + k ε L` against every `u`, where `k` is the number
of coordinates. -/
theorem hasRegretBound_pi_krichevskyTrofimovOCO (hε : 0 < ε) (hL : 0 < L) :
    (pi (G := fun _ : α ↦ ℝ) (X := fun _ ↦ ℝ) fun _ ↦
      krichevskyTrofimovOCO (C := C) L ε).HasRegretBound (fun y x ↦ ∑ a, y a * x a)
      (fun _ y ↦ ‖y‖ ≤ L) Set.univ (fun n _ _ u ↦
        L * ∑ a, |u a| * √(2 * n * log (exp 1 * |u a| * n / ε + 1)) +
          Fintype.card α * ε * L) := by
  refine (HasRegretBound.pi (G := fun _ ↦ ℝ) (X := fun _ ↦ ℝ)
    fun _ ↦ hasRegretBound_krichevskyTrofimovOCO hε hL).mono
    (fun _ y hy a ↦ (Real.norm_eq_abs (y a)).symm.trans_le ((norm_le_pi_norm y a).trans hy))
    (fun _ _ a _ ↦ Set.mem_univ _) fun n _ _ u _ _ ↦ le_of_eq ?_
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_sum]
  congr 1
  · exact sum_congr rfl fun a _ ↦ by ring
  · ring

/-- **The coordinatewise Krichevsky–Trofimov algorithm, with norms** [Ora, Theorem 13.9]. For
`ε, L > 0`, the coordinatewise product of copies of the KT algorithm on `α → ℝ` has, for the linear
losses `x ↦ ∑ a, y t a * x a` with `‖y t‖ ≤ L` for the sup norm, the regret bound
`(∑ a, |u a|) L √(2 n log (e ‖u‖ n / ε + 1)) + k ε L` against every `u`, in terms of the `ℓ¹`
norm and of the sup norm `‖u‖` of `u`, where `k` is the number of coordinates. -/
theorem hasRegretBound_pi_krichevskyTrofimovOCO_norm (hε : 0 < ε) (hL : 0 < L) :
    (pi (G := fun _ : α ↦ ℝ) (X := fun _ ↦ ℝ) fun _ ↦
      krichevskyTrofimovOCO (C := C) L ε).HasRegretBound (fun y x ↦ ∑ a, y a * x a)
      (fun _ y ↦ ‖y‖ ≤ L) Set.univ (fun n _ _ u ↦
        (∑ a, |u a|) * L * √(2 * n * log (exp 1 * ‖u‖ * n / ε + 1)) +
          Fintype.card α * ε * L) := by
  refine (hasRegretBound_pi_krichevskyTrofimovOCO hε hL).mono (fun _ _ ↦ id) subset_rfl
    fun n _ _ u _ _ ↦ (add_le_add_iff_right _).mpr ?_
  rw [mul_sum, sum_mul, sum_mul]
  refine sum_le_sum fun a _ ↦ ?_
  -- each coordinate `|u a|` is at most the sup norm `‖u‖` in the logarithm
  have h_log : log (exp 1 * |u a| * n / ε + 1) ≤ log (exp 1 * ‖u‖ * n / ε + 1) := by
    refine log_le_log (by positivity) ?_
    gcongr
    exact (Real.norm_eq_abs (u a)).symm.trans_le (norm_le_pi_norm u a)
  have h_sqrt := sqrt_le_sqrt (mul_le_mul_of_nonneg_left h_log (by positivity : (0 : ℝ) ≤ 2 * n))
  calc L * (|u a| * √(2 * n * log (exp 1 * |u a| * n / ε + 1)))
  _ ≤ L * (|u a| * √(2 * n * log (exp 1 * ‖u‖ * n / ε + 1))) := by gcongr
  _ = |u a| * L * √(2 * n * log (exp 1 * ‖u‖ * n / ε + 1)) := by ring

end Coordinatewise

section AnyNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Krichevsky–Trofimov algorithm as a magnitude learner** [CO18], [Ora, Section 13.4]. Let
`ε, L > 0`, and let `B` be a learner on the closed unit ball of `E` with the regret bound `RB` for
the linear losses of dual norm at most `L` against the comparators of the unit sphere. Then the
magnitude–direction reduction of the KT algorithm and of `B` has, for the linear losses of dual
norm at most `L`, the regret bound
`‖u‖ L √(2 n log (e ‖u‖ n / ε + 1)) + ε L + ‖u‖ RB n c y (‖u‖⁻¹ • u)` against every `u ∈ E`. -/
theorem hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection (hε : 0 < ε) (hL : 0 < L)
    {B : OnlineLearner C (E →L[ℝ] ℝ) E} {UB : Set E}
    {RB : ℕ → (ℕ → C) → (ℕ → E →L[ℝ] ℝ) → E → ℝ}
    (hB : B.HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) UB RB)
    (hUB : sphere 0 1 ⊆ UB) (hB₁ : ∀ c y t, ‖B.run c y t‖ ≤ 1) :
    ((krichevskyTrofimovOCO L ε).magnitudeDirection B).HasRegretBound (fun y x ↦ y x)
      (fun _ y ↦ ‖y‖ ≤ L) Set.univ (fun n c y u ↦
        ‖u‖ * L * √(2 * n * log (exp 1 * ‖u‖ * n / ε + 1)) + ε * L +
          ‖u‖ * RB n c y (‖u‖⁻¹ • u)) :=
  ((hasRegretBound_krichevskyTrofimovOCO hε hL).magnitudeDirection_of_norm_le hB hUB hB₁).mono
    (fun _ _ ↦ id) (fun _ _ ↦ Set.mem_univ _) fun _ _ _ _ _ _ ↦ by rw [abs_norm]

variable {F : E → ℝ} {F' : E → E →L[ℝ] ℝ} {m D : ℝ} {x₀ : E}

/-- **A parameter-free learner in any norm** [CO18], [Ora, Section 13.4]. Let `ε, L > 0`. Let the
potential `F` be `m`-strongly convex on the closed unit ball of `E` for its norm, with `m > 0`,
with derivative `F' x` within the ball at every point `x` of the ball, and with Bregman divergences
`D_F(u, x)` (for `F' x`) at most `D > 0` on the ball. Let mirror descent steps exist on the ball
from every point of the ball, and let `x₀` lie in the ball. Then the magnitude–direction reduction
of the KT algorithm and of mirror descent on the ball from `x₀`, with the learning rates
`√(m D) / (L √(t + 1))`, has, for the linear losses of dual norm at most `L`, the regret bound
`‖u‖ L (√(2 n log (e ‖u‖ n / ε + 1)) + 2 √(D n / m)) + ε L` against every `u ∈ E`. -/
theorem hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection_mirrorDescent (hε : 0 < ε)
    (hL : 0 < L) (hF : StrongConvexOn (closedBall 0 1) m F) (hm : 0 < m)
    (hF' : ∀ x ∈ closedBall (0 : E) 1, HasFDerivWithinAt F (F' x) (closedBall 0 1) x)
    (hex : ∀ (η : ℝ) (y : E →L[ℝ] ℝ), ∀ a ∈ closedBall (0 : E) 1,
      ∃ x, IsMirrorDescentStep (closedBall 0 1) F η y a (F' a) x)
    (hx₀ : x₀ ∈ closedBall (0 : E) 1) (hD : 0 < D)
    (hDK : ∀ u ∈ closedBall (0 : E) 1, ∀ x ∈ closedBall (0 : E) 1, bregDiv F u x (F' x) ≤ D) :
    ((krichevskyTrofimovOCO L ε).magnitudeDirection (mirrorDescent (C := C) (closedBall 0 1) F F'
      (fun t ↦ √(m * D) / (L * √((t : ℝ) + 1))) x₀)).HasRegretBound (fun y x ↦ y x)
      (fun _ y ↦ ‖y‖ ≤ L) Set.univ (fun n _ _ u ↦
        ‖u‖ * L * (√(2 * n * log (exp 1 * ‖u‖ * n / ε + 1)) + 2 * √(D * n / m)) + ε * L) :=
  (hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection hε hL
    (hasRegretBound_mirrorDescent_of_strongConvexOn_of_norm_le hF hm hF' hex hx₀ hD hL hDK)
    sphere_subset_closedBall fun c y t ↦
      mem_closedBall_zero_iff.mp (run_mirrorDescent_mem hx₀ c y t)).mono
    (fun _ _ ↦ id) subset_rfl fun _ _ _ _ _ _ ↦ le_of_eq (by ring)

/-- **A parameter-free learner in a Hilbert space** [CO18], [Ora, (13.2)]. Let `ε, L > 0`. The
magnitude–direction reduction of the KT algorithm and of mirror descent on the closed unit ball of
a real Hilbert space `E` with the potential `‖x‖ ^ 2 / 2`, from `0`, with the learning rates
`√2 / (L √(t + 1))`, has, for the linear losses of dual norm at most `L`, the regret bound
`‖u‖ L (√(2 n log (e ‖u‖ n / ε + 1)) + 2 √(2 n)) + ε L` against every `u ∈ E`. The direction
learner is projected online subgradient descent on the unit ball, fed the vectors representing the
losses (`isMirrorDescentStep_norm_sq_div_two_iff`), whose steps exist on the ball
(`exists_isMirrorDescentStep_norm_sq_div_two`). [Ora, (13.2)] states the bound with `√(2 n)`
in place of `2 √(2 n)`. -/
theorem hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection_mirrorDescent_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (hε : 0 < ε) (hL : 0 < L) :
    ((krichevskyTrofimovOCO L ε).magnitudeDirection (mirrorDescent (C := C) (closedBall 0 1)
      (fun b : E ↦ ‖b‖ ^ 2 / 2) (innerSL ℝ) (fun t ↦ √2 / (L * √((t : ℝ) + 1))) 0)).HasRegretBound
      (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) Set.univ (fun n _ _ u ↦
        ‖u‖ * L * (√(2 * n * log (exp 1 * ‖u‖ * n / ε + 1)) + 2 * √(2 * n)) + ε * L) := by
  -- the Bregman divergences on the ball are `‖u - x‖ ^ 2 / 2 ≤ 2`
  have hDK (u : E) (hu : u ∈ closedBall (0 : E) 1) (x : E) (hx : x ∈ closedBall (0 : E) 1) :
      bregDiv (fun b : E ↦ ‖b‖ ^ 2 / 2) u x (innerSL ℝ x) ≤ 2 := by
    rw [bregDiv_norm_sq_div_two]
    have h := (norm_sub_le u x).trans (add_le_add (mem_closedBall_zero_iff.mp hu)
      (mem_closedBall_zero_iff.mp hx))
    nlinarith [norm_nonneg (u - x)]
  have h := hasRegretBound_krichevskyTrofimovOCO_magnitudeDirection_mirrorDescent (C := C) hε hL
    (strongConvexOn_norm_sq_div_two (convex_closedBall 0 1)) one_pos
    (fun x _ ↦ (hasFDerivAt_norm_sq_div_two x).hasFDerivWithinAt)
    (fun η y a _ ↦ exists_isMirrorDescentStep_norm_sq_div_two ⟨0, mem_closedBall_self zero_le_one⟩
      isClosed_closedBall.isComplete (convex_closedBall 0 1) η y a)
    (mem_closedBall_self zero_le_one) two_pos hDK
  simp only [one_mul, div_one] at h
  exact h

end AnyNorm

end OnlineLearner

end LMLExplore.OnlineLearning
