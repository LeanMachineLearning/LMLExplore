/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.Learner.Basic
public import LMLExplore.OnlineLearning.MirrorDescent.Basic
import LMLExplore.Analysis.Real.Sqrt

/-!
# The mirror descent learner

Mirror descent is specified in `LMLExplore.OnlineLearning.MirrorDescent.Basic` by the predicate
`IsMirrorDescentStep` on its steps, and its regret bounds take the plays as hypotheses. This file
constructs the algorithm as an online learner (`OnlineLearner`) for online linear optimization on
a set `K` of a real normed space `E`, with losses in the dual `E →L[ℝ] ℝ`.

* `mirrorDescentStep K F η y a F'` is a chosen mirror descent step on `K` from `a`, with potential
  `F`, derivative `F'` of `F` at `a`, learning rate `η` and loss `y`, when one exists, and `a`
  otherwise.
* The learner `OnlineLearner.mirrorDescent K F F' η x₀` starts at `x₀` and takes at round `t` the
  chosen step from its play, with the learning rate `η t`, the last loss and the derivative
  `F' (x t)` of `F` at the play: it is the learner defined by this update rule
  (`OnlineLearner.ofUpdate`). Its plays stay in `K` when `x₀ ∈ K` (`run_mirrorDescent_mem`), and
  each of them is a mirror descent step from the previous one at every round where such a step
  exists (`isMirrorDescentStep_run_mirrorDescent`). Steps exist on nonempty compact sets
  (`exists_isMirrorDescentStep`) and, in finite dimension, for a strongly convex potential on
  nonempty closed sets (`exists_isMirrorDescentStep_of_strongConvexOn`).
* For an `m`-strongly convex potential differentiable within `K`, it has the regret guarantees of
  [Ora, Theorem 6.11] for every sequence of linear losses: `D_F(u, x₀) / η + η / (2 m) ∑ ‖y t‖ ^ 2`
  against every `u ∈ K` for a constant learning rate `η`, with no bound on `K`
  (`hasRegretBound_mirrorDescent_of_strongConvexOn`), and `D / η (n - 1) + ∑ η t / (2 m) ‖y t‖ ^ 2`
  for nonincreasing learning rates on a set of Bregman diameter `D`
  (`hasRegretBound_mirrorDescent_of_strongConvexOn_of_antitone`). With the learning rates
  `η t = √(m D) / (L √(t + 1))`, which do not depend on the horizon, this is
  `2 L √(D n / m)` for losses of dual norm at most `L`
  (`hasRegretBound_mirrorDescent_of_strongConvexOn_of_norm_le`). The bounds hold for every
  sequence of losses, hence against adaptive adversaries.

## Main definitions

* `LMLExplore.OnlineLearning.mirrorDescentStep K F η y a F'`: a chosen mirror descent step.
* `LMLExplore.OnlineLearning.OnlineLearner.mirrorDescent K F F' η x₀`: the mirror descent learner.

## Main statements

* `OnlineLearner.isMirrorDescentStep_run_mirrorDescent`: the plays of the mirror descent learner
  are mirror descent steps.
* `OnlineLearner.hasRegretBound_mirrorDescent_of_strongConvexOn`: the regret guarantee with a
  constant learning rate.
* `OnlineLearner.hasRegretBound_mirrorDescent_of_strongConvexOn_of_antitone`: the anytime regret
  guarantee with nonincreasing learning rates.
* `OnlineLearner.hasRegretBound_mirrorDescent_of_strongConvexOn_of_norm_le`: the anytime regret
  guarantee `2 L √(D n / m)` for losses of dual norm at most `L`.

## References

* [LS] T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ}

section Step

variable {η : ℝ} {y : E →L[ℝ] ℝ} {a : E} {F' : E →L[ℝ] ℝ}

open Classical in
/-- A **chosen mirror descent step** on `K` from `a`, with potential `F`, learning rate `η`, loss
`y` and linear map `F'` (intended to be a derivative of `F` at `a`): a mirror descent step
(`IsMirrorDescentStep K F η y a F'`) when one exists, and the point `a` itself otherwise. -/
noncomputable def mirrorDescentStep (K : Set E) (F : E → ℝ) (η : ℝ) (y : E →L[ℝ] ℝ) (a : E)
    (F' : E →L[ℝ] ℝ) : E :=
  if h : ∃ x, IsMirrorDescentStep K F η y a F' x then h.choose else a

/-- When a mirror descent step exists, the chosen step is one. -/
theorem isMirrorDescentStep_mirrorDescentStep (h : ∃ x, IsMirrorDescentStep K F η y a F' x) :
    IsMirrorDescentStep K F η y a F' (mirrorDescentStep K F η y a F') := by
  simp only [mirrorDescentStep, h, dite_true]
  exact h.choose_spec

/-- When no mirror descent step exists, the chosen step stays at the current point. -/
theorem mirrorDescentStep_of_not_exists (h : ¬ ∃ x, IsMirrorDescentStep K F η y a F' x) :
    mirrorDescentStep K F η y a F' = a := by
  simp [mirrorDescentStep, h]

/-- The chosen mirror descent step from a point of `K` lies in `K`. -/
theorem mirrorDescentStep_mem (ha : a ∈ K) : mirrorDescentStep K F η y a F' ∈ K := by
  by_cases h : ∃ x, IsMirrorDescentStep K F η y a F' x
  · exact (isMirrorDescentStep_mirrorDescentStep h).mem
  · rwa [mirrorDescentStep_of_not_exists h]

end Step

namespace OnlineLearner

variable {C : Type*} {F' : E → E →L[ℝ] ℝ} {η : ℕ → ℝ} {x₀ : E}

/-- The **mirror descent learner** on `K` with potential `F`, derivatives `F'`, learning rates `η`
and first play `x₀`, for online linear optimization [LS, (28.1)–(28.2); Ora, Chapter 6]. At
round `t + 1` it plays the chosen mirror descent step (`mirrorDescentStep`) from its play `x t` of
round `t`, with the learning rate `η t`, the loss `y t` of round `t` and the linear map `F' (x t)`,
intended to be the derivative of `F` at `x t`: a minimizer over `K` of
`b ↦ η t * y t b + D_F(b, x t)` when one exists, and `x t` otherwise. It ignores the contexts. -/
noncomputable def mirrorDescent (K : Set E) (F : E → ℝ) (F' : E → E →L[ℝ] ℝ) (η : ℕ → ℝ)
    (x₀ : E) : OnlineLearner C (E →L[ℝ] ℝ) E :=
  ofUpdate x₀ fun t y a ↦ mirrorDescentStep K F (η t) y a (F' a)

/-- The first play of the mirror descent learner is `x₀`. -/
@[simp]
lemma run_mirrorDescent_zero (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) :
    (mirrorDescent K F F' η x₀).run c y 0 = x₀ :=
  run_ofUpdate_zero c y

/-- The play of round `t + 1` of the mirror descent learner is the chosen mirror descent step from
its play of round `t`, for the loss of round `t`. -/
@[simp]
lemma run_mirrorDescent_succ (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) :
    (mirrorDescent K F F' η x₀).run c y (t + 1) =
      mirrorDescentStep K F (η t) (y t) ((mirrorDescent K F F' η x₀).run c y t)
        (F' ((mirrorDescent K F F' η x₀).run c y t)) :=
  run_ofUpdate_succ c y t

/-- The plays of the mirror descent learner started in `K` lie in `K`. -/
lemma run_mirrorDescent_mem (hx₀ : x₀ ∈ K) (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) :
    (mirrorDescent K F F' η x₀).run c y t ∈ K :=
  run_ofUpdate_mem hx₀ (fun _ _ _ ↦ mirrorDescentStep_mem) c y t

/-- **The mirror descent learner plays mirror descent.** At every round where a mirror descent
step exists from the play of the learner, its next play is one (`IsMirrorDescentStep`), with the
learning rate and the loss of the round and the linear map `F'` at the play. -/
theorem isMirrorDescentStep_run_mirrorDescent (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) {t : ℕ}
    (h : ∃ x, IsMirrorDescentStep K F (η t) (y t) ((mirrorDescent K F F' η x₀).run c y t)
      (F' ((mirrorDescent K F F' η x₀).run c y t)) x) :
    IsMirrorDescentStep K F (η t) (y t) ((mirrorDescent K F F' η x₀).run c y t)
      (F' ((mirrorDescent K F F' η x₀).run c y t)) ((mirrorDescent K F F' η x₀).run c y (t + 1)) :=
  run_mirrorDescent_succ (K := K) (F := F) (F' := F') (η := η) (x₀ := x₀) c y t ▸
    isMirrorDescentStep_mirrorDescentStep h

variable {m : ℝ}

/-- The plays of the mirror descent learner are mirror descent steps at every round, when steps
exist from every point of `K` and `x₀ ∈ K`. -/
private lemma isMirrorDescentStep_run_mirrorDescent_of_forall (hx₀ : x₀ ∈ K)
    (hex : ∀ (η : ℝ) (y : E →L[ℝ] ℝ), ∀ a ∈ K, ∃ x, IsMirrorDescentStep K F η y a (F' a) x)
    (c : ℕ → C) (y : ℕ → E →L[ℝ] ℝ) (t : ℕ) :
    IsMirrorDescentStep K F (η t) (y t) ((mirrorDescent K F F' η x₀).run c y t)
      (F' ((mirrorDescent K F F' η x₀).run c y t)) ((mirrorDescent K F F' η x₀).run c y (t + 1)) :=
  isMirrorDescentStep_run_mirrorDescent c y (hex _ _ _ (run_mirrorDescent_mem hx₀ c y t))

/-- **Regret guarantee of the mirror descent learner with a constant learning rate**
[Ora, Theorem 6.11; LS, Corollary 28.8]. Let the potential `F` be `m`-strongly convex on `K` for
the norm of `E`, with `m > 0`, and let `F' x` be a derivative of `F` within `K` at every `x ∈ K`.
Let mirror descent steps exist from every point of `K`, for every learning rate and loss (for
instance by `exists_isMirrorDescentStep` on a nonempty compact set, or by
`exists_isMirrorDescentStep_of_strongConvexOn` on a closed set in finite dimension), and let
`x₀ ∈ K`. Then for every learning rate `η > 0`, every sequence of linear losses `y`, every horizon
`n` and every `u ∈ K`, the plays `x` of the mirror descent learner with the constant learning rate
`η` satisfy
`∑ t < n, y t (x t - u) ≤ D_F(u, x₀) / η + η / (2 m) * ∑ t < n, ‖y t‖ ^ 2`,
where `D_F(u, x₀)` is the Bregman divergence for `F' x₀` and `‖y t‖` the dual norm. No bound on
the size of `K` is needed, and `x₀` need not minimize `F`. -/
theorem hasRegretBound_mirrorDescent_of_strongConvexOn (hF : StrongConvexOn K m F) (hm : 0 < m)
    (hF' : ∀ x ∈ K, HasFDerivWithinAt F (F' x) K x)
    (hex : ∀ (η : ℝ) (y : E →L[ℝ] ℝ), ∀ a ∈ K, ∃ x, IsMirrorDescentStep K F η y a (F' a) x)
    (hx₀ : x₀ ∈ K) {η : ℝ} (hη : 0 < η) :
    (mirrorDescent (C := C) K F F' (fun _ ↦ η) x₀).HasRegretBound (fun y x ↦ y x)
      (fun _ _ ↦ True) K
      (fun n _ y u ↦ bregDiv F u x₀ (F' x₀) / η + η / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2) := by
  refine hasRegretBound_iff.mpr fun c y n _ u hu ↦ ?_
  set x := (mirrorDescent (C := C) K F F' (fun _ ↦ η) x₀).run c y
  have h_mem (t : ℕ) : x t ∈ K := run_mirrorDescent_mem hx₀ c y t
  -- the regret bound of mirror descent from any initial play, and its stability terms
  have h := mirrorDescent_regret_le_bregDiv_div (n := n) (strongConvexOn_zero.mp (hF.mono hm.le))
    hη y x (fun t ↦ F' (x t)) (h_mem 0)
    (fun t _ ↦ isMirrorDescentStep_run_mirrorDescent_of_forall (η := fun _ ↦ η) hx₀ hex c y t)
    (fun t _ ↦ hF' _ (h_mem t)) hu
  have h_stab := sum_apply_sub_sub_bregDiv_le_of_strongConvexOn (n := n) hF hm hη y x
    (fun t _ ↦ h_mem t) (fun t ↦ F' (x t)) fun t _ ↦ hF' _ (h_mem t)
  rw [show x 0 = x₀ from run_mirrorDescent_zero c y] at h
  rw [regret_eq_sum_apply_sub]
  linarith

/-- **Anytime regret guarantee of the mirror descent learner** [Ora, Theorem 6.11]. Let the
potential `F` be `m`-strongly convex on `K` for the norm of `E`, with `m > 0`, and let `F' x` be a
derivative of `F` within `K` at every `x ∈ K`. Let mirror descent steps exist from every point of
`K`, for every learning rate and loss, and let `x₀ ∈ K`. Let the Bregman divergences
`D_F(u, x)` (for `F' x`) of the points of `K` be at most `D`, and let the learning rates `η t > 0`
be nonincreasing. Then for every sequence of linear losses `y`, every horizon `n` and every
`u ∈ K`, the plays `x` of the mirror descent learner satisfy
`∑ t < n, y t (x t - u) ≤ D / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2`,
where `‖y t‖` is the dual norm. The learning rates need not be tuned to the horizon. -/
theorem hasRegretBound_mirrorDescent_of_strongConvexOn_of_antitone (hF : StrongConvexOn K m F)
    (hm : 0 < m) (hF' : ∀ x ∈ K, HasFDerivWithinAt F (F' x) K x)
    (hex : ∀ (η : ℝ) (y : E →L[ℝ] ℝ), ∀ a ∈ K, ∃ x, IsMirrorDescentStep K F η y a (F' a) x)
    (hx₀ : x₀ ∈ K) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η) {D : ℝ}
    (hD : ∀ u ∈ K, ∀ x ∈ K, bregDiv F u x (F' x) ≤ D) :
    (mirrorDescent (C := C) K F F' η x₀).HasRegretBound (fun y x ↦ y x) (fun _ _ ↦ True) K
      (fun n _ y _ ↦ D / η (n - 1) + ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2) := by
  refine hasRegretBound_iff.mpr fun c y n _ u hu ↦ ?_
  set x := (mirrorDescent (C := C) K F F' η x₀).run c y
  have h_mem (t : ℕ) : x t ∈ K := run_mirrorDescent_mem hx₀ c y t
  -- the divergence of a point to itself vanishes, so `D ≥ 0`
  have hD0 : 0 ≤ D := by simpa using hD x₀ hx₀ x₀ hx₀
  rw [regret_eq_sum_apply_sub]
  exact mirrorDescent_regret_le_of_strongConvexOn_of_antitone hF hm hη hη_anti y x
    (fun t ↦ F' (x t)) (h_mem 0)
    (fun t _ ↦ isMirrorDescentStep_run_mirrorDescent_of_forall hx₀ hex c y t)
    (fun t _ ↦ hF' _ (h_mem t)) hD0 (fun t _ ↦ hD u hu _ (h_mem t)) hu

/-- **Anytime regret guarantee of the mirror descent learner for bounded losses**
[Ora, Theorem 6.11]. Let the potential `F` be `m`-strongly convex on `K` for the norm of `E`, with
`m > 0`, and let `F' x` be a derivative of `F` within `K` at every `x ∈ K`. Let mirror descent
steps exist from every point of `K`, for every learning rate and loss, and let `x₀ ∈ K`. Let the
Bregman divergences `D_F(u, x)` (for `F' x`) of the points of `K` be at most `D > 0`, and let
`L > 0`. Then with the learning rates `η t = √(m D) / (L √(t + 1))`, which do not depend on the
horizon, for every sequence of linear losses `y` of dual norm at most `L`, every horizon `n` and
every `u ∈ K`, the plays `x` of the mirror descent learner satisfy
`∑ t < n, y t (x t - u) ≤ 2 L √(D n / m)`. -/
theorem hasRegretBound_mirrorDescent_of_strongConvexOn_of_norm_le (hF : StrongConvexOn K m F)
    (hm : 0 < m) (hF' : ∀ x ∈ K, HasFDerivWithinAt F (F' x) K x)
    (hex : ∀ (η : ℝ) (y : E →L[ℝ] ℝ), ∀ a ∈ K, ∃ x, IsMirrorDescentStep K F η y a (F' a) x)
    (hx₀ : x₀ ∈ K) {D L : ℝ} (hD : 0 < D) (hL : 0 < L)
    (hDK : ∀ u ∈ K, ∀ x ∈ K, bregDiv F u x (F' x) ≤ D) :
    (mirrorDescent (C := C) K F F' (fun t ↦ √(m * D) / (L * √((t : ℝ) + 1))) x₀).HasRegretBound
      (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) K (fun n _ _ _ ↦ 2 * L * √(D * n / m)) := by
  set η : ℕ → ℝ := fun t ↦ √(m * D) / (L * √((t : ℝ) + 1)) with hη_def
  have hη (t : ℕ) : 0 < η t := by positivity
  have hη_anti : Antitone η := fun s t hst ↦
    div_le_div_of_nonneg_left (by positivity) (by positivity) (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hst 1)) hL.le)
  refine hasRegretBound_iff.mpr fun c y n hy u hu ↦ ?_
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [regret_zero]
  refine ((hasRegretBound_mirrorDescent_of_strongConvexOn_of_antitone hF hm hF' hex hx₀ hη hη_anti
    hDK).regret_le (fun _ _ ↦ trivial) hu).trans ?_
  -- `√(D n / m) = √(m D) √n / m`
  have h_sqrt : √(D * n / m) = √(m * D) * √n / m := by
    rw [Real.sqrt_div' _ hm.le, Real.sqrt_mul hm.le, Real.sqrt_mul hD.le]
    field_simp
    rw [Real.sq_sqrt hm.le]
  -- the penalty is `L √(D n / m)`
  have h_pen : D / η (n - 1) = L * √(D * n / m) := by
    have hn' : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
    simp only [hη_def]
    rw [hn', h_sqrt, Real.sqrt_mul hm.le]
    field_simp
    rw [Real.sq_sqrt hm.le, Real.sq_sqrt hD.le]
    ring
  -- the stability terms add up to at most `L √(D n / m)`
  have h_stab : ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2 ≤ L * √(D * n / m) := by
    calc ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2
    _ ≤ ∑ t ∈ range n, √(m * D) * L / (2 * m) * (√((t : ℝ) + 1))⁻¹ := by
      refine sum_le_sum fun t ht ↦ ?_
      have h_sq : ‖y t‖ ^ 2 ≤ L ^ 2 := by
        gcongr
        exact hy t (mem_range.mp ht)
      calc η t / (2 * m) * ‖y t‖ ^ 2 ≤ η t / (2 * m) * L ^ 2 := by
            gcongr
        _ = √(m * D) * L / (2 * m) * (√((t : ℝ) + 1))⁻¹ := by
          simp only [hη_def]
          field_simp
    _ = √(m * D) * L / (2 * m) * ∑ t ∈ range n, (√((t : ℝ) + 1))⁻¹ := by rw [mul_sum]
    _ ≤ √(m * D) * L / (2 * m) * (2 * √n) := by
      gcongr
      exact Real.sum_range_inv_sqrt_add_one_le n
    _ = L * √(D * n / m) := by
      rw [h_sqrt]
      ring
  linarith

end OnlineLearner

end LMLExplore.OnlineLearning
