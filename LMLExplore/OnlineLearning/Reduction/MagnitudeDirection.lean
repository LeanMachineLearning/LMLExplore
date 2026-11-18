/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import LMLExplore.OnlineLearning.Learner.Basic

/-!
# Learning the magnitude and the direction separately

An online learner for linear losses on a real normed space `E` can be built from a learner `A` on
`ℝ`, which learns a magnitude, and a learner `B` on `E`, which learns a direction
[CO18], [Ora, Section 12.3, Algorithm 12.3]. At each round, `A` plays `z t`, `B` plays `x t`, and
the reduction plays `z t • x t`. After the linear loss `y t` is revealed, `B` receives `y t`, and
`A` receives the coefficient `y t (x t)` of the one-dimensional linear loss `r ↦ y t (x t) * r`.
If `B` plays in the unit ball, this coefficient is at most `‖y t‖` in absolute value.

The regret of the reduction against comparators of norm at most `U` is the regret of the
magnitude learner plus `U` times the regret of the direction learner: for linear losses, the loss
of the play `z • x` relative to a comparator `U • v` is `(z - U) * y x + U * y (x - v)`
(`apply_smul_sub_smul`). Summed over the rounds, for comparators
`u t` of norm at most `U`, the dynamic regret of the plays `z t • x t` is the regret of the
magnitudes `z t` against `U` plus `U` times the dynamic regret of the directions `x t` against the
comparators `U⁻¹ • u t` of the unit ball (`dynRegret_smul_eq_of_norm_le`) [JC22],
[Ora, Theorem 14.5]. For a fixed comparator `u`, with `U = ‖u‖`, the regret of the plays is the
regret of the magnitudes against `‖u‖` plus `‖u‖` times the regret of the directions against the
unit vector `‖u‖⁻¹ • u` (`regret_smul_eq`) [Ora, Theorem 12.16]; for `u = 0`, it is the regret of
the magnitudes against `0`.

The learner `A.magnitudeDirection B` runs the reduction (`run_magnitudeDirection`). Its regret
guarantee is the sum of a guarantee of `A` at `‖u‖` and `‖u‖` times a guarantee of `B` on the
unit sphere at `‖u‖⁻¹ • u` (`OnlineLearner.HasRegretBound.magnitudeDirection`); for losses of
dual norm at most `L`, the learner `A` must only handle coefficients of absolute value at most `L`
(`OnlineLearner.HasRegretBound.magnitudeDirection_of_norm_le`). Combined with a learner `B` on
the unit ball of `E`, a parameter-free learner on `ℝ` thus gives a regret bound on `E` that
scales with `‖u‖`.

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner.magnitudeDirection A B`: the product of the plays of a
  learner `A` on `ℝ` and of a learner `B` on `E`, with `A` fed the losses of the plays of `B`.

## Main statements

* `LMLExplore.OnlineLearning.dynRegret_smul_eq_of_norm_le` [Ora, Theorem 14.5]: the dynamic
  regret of the products of magnitudes and directions.
* `LMLExplore.OnlineLearning.regret_smul_eq` [Ora, Theorem 12.16]: their regret against a fixed
  comparator.
* `LMLExplore.OnlineLearning.OnlineLearner.dynRegret_run_magnitudeDirection`,
  `LMLExplore.OnlineLearning.OnlineLearner.regret_run_magnitudeDirection`: the same statements for
  the runs of `A.magnitudeDirection B`.
* `LMLExplore.OnlineLearning.OnlineLearner.HasRegretBound.magnitudeDirection`,
  `LMLExplore.OnlineLearning.OnlineLearner.HasRegretBound.magnitudeDirection_of_norm_le`: the
  regret guarantees of `A.magnitudeDirection B`.

## References

* [CO18] A. Cutkosky and F. Orabona, *Black-box reductions for parameter-free online learning in
  Banach spaces*, COLT 2018.
* [JC22] A. Jacobsen and A. Cutkosky, *Parameter-free mirror descent*, COLT 2022.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, Sections 12.3 and 14.1.3.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

variable {E F : Type*}

section Sequences

section Module

variable [AddCommGroup E] [Module ℝ E] [FunLike F E ℝ] [LinearMapClass F ℝ E ℝ]

/-- **The per-round identity of the magnitude–direction reduction.** For a linear loss `y`, the
loss of the play `z • x` relative to the comparator `U • v` is the loss `(z - U) * y x` of the
magnitude `z` relative to `U`, for the one-dimensional linear loss of coefficient `y x`, plus `U`
times the loss of the direction `x` relative to `v`. -/
lemma apply_smul_sub_smul (y : F) (z U : ℝ) (x v : E) :
    y (z • x - U • v) = (z - U) * y x + U * y (x - v) := by
  simp only [map_sub, map_smul, smul_eq_mul]
  ring

/-- **Dynamic regret of magnitudes times directions**, against comparators `U • v t`: for linear
losses `y t`, the dynamic regret of the plays `z t • x t` against `U • v t` is the regret of the
magnitudes `z t` against `U`, for the one-dimensional linear losses of coefficients `y t (x t)`,
plus `U` times the dynamic regret of the directions `x t` against `v t`. -/
theorem dynRegret_smul_smul (y : ℕ → F) (z : ℕ → ℝ) (x v : ℕ → E) (U : ℝ) (n : ℕ) :
    dynRegret (fun t ↦ y t) (fun t ↦ z t • x t) (fun t ↦ U • v t) n =
      regret (fun t r ↦ y t (x t) * r) z U n + U * dynRegret (fun t ↦ y t) x v n := by
  rw [dynRegret_def, regret_def, dynRegret_def, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [← map_sub, ← map_sub, apply_smul_sub_smul]
  ring

end Module

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FunLike F E ℝ] [LinearMapClass F ℝ E ℝ]

/-- **Dynamic regret of magnitudes times directions** [JC22], [Ora, Theorem 14.5]. For linear
losses `y t` and comparators `u t` of norm at most `U` on the first `n` rounds, the dynamic regret
of the plays `z t • x t` is the regret of the magnitudes `z t` against `U`, for the
one-dimensional linear losses of coefficients `y t (x t)`, plus `U` times the dynamic regret of the
directions `x t` against the comparators `U⁻¹ • u t`, which lie in the unit ball. -/
theorem dynRegret_smul_eq_of_norm_le (y : ℕ → F) (z : ℕ → ℝ) (x u : ℕ → E) {U : ℝ} {n : ℕ}
    (hu : ∀ t < n, ‖u t‖ ≤ U) :
    dynRegret (fun t ↦ y t) (fun t ↦ z t • x t) u n =
      regret (fun t r ↦ y t (x t) * r) z U n +
        U * dynRegret (fun t ↦ y t) x (fun t ↦ U⁻¹ • u t) n := by
  rw [← dynRegret_smul_smul]
  refine dynRegret_congr fun t ht ↦ ?_
  rcases eq_or_ne U 0 with rfl | hU
  · simpa using hu t ht
  · rw [smul_inv_smul₀ hU]

/-- **Regret of magnitudes times directions** [CO18], [Ora, Theorem 12.16]. For linear losses
`y t` and every comparator `u`, the regret of the plays `z t • x t` against `u` is the regret of
the magnitudes `z t` against `‖u‖`, for the one-dimensional linear losses of coefficients
`y t (x t)`, plus `‖u‖` times the regret of the directions `x t` against the unit vector
`‖u‖⁻¹ • u`. For `u = 0`, it is the regret of the magnitudes against `0`. -/
theorem regret_smul_eq (y : ℕ → F) (z : ℕ → ℝ) (x : ℕ → E) (u : E) (n : ℕ) :
    regret (fun t ↦ y t) (fun t ↦ z t • x t) u n =
      regret (fun t r ↦ y t (x t) * r) z ‖u‖ n + ‖u‖ * regret (fun t ↦ y t) x (‖u‖⁻¹ • u) n := by
  have h := dynRegret_smul_eq_of_norm_le y z x (fun _ ↦ u) (n := n) fun _ _ ↦ le_rfl
  rwa [dynRegret_const, dynRegret_const] at h

end Normed

end Sequences

namespace OnlineLearner

variable {C : Type*}

section Learner

variable [AddCommGroup E] [Module ℝ E] [FunLike F E ℝ]

/-- The learner **learning the magnitude and the direction separately** [CO18],
[Ora, Algorithm 12.3], from a learner `A` on `ℝ` and a learner `B` on `E`, for linear losses in
`F`. At round `t`, `A` plays a magnitude `z t`, `B` plays a direction `x t`, and the learner plays
`z t • x t`. After the loss `y t` is revealed, `B` receives `y t` and `A` receives the coefficient
`y t (x t)` of the one-dimensional linear loss `r ↦ y t (x t) * r` (`run_magnitudeDirection`). The
two learners share the contexts. -/
def magnitudeDirection (A : OnlineLearner C ℝ ℝ) (B : OnlineLearner C F E) :
    OnlineLearner C F E where
  play t h c := A.play t (fun s ↦ ((h s).1,
      (h s).2 (B.play s (fun r ↦ h (Fin.castLE s.2.le r)) (h s).1))) c • B.play t h c

variable (A : OnlineLearner C ℝ ℝ) (B : OnlineLearner C F E)

/-- The play of `A.magnitudeDirection B` from the history `h` and the context `c` of round `t` is
the play of `A`, fed the losses `(h s).2` of the plays of `B` from the truncated histories, times
the play of `B`. -/
lemma play_magnitudeDirection (t : ℕ) (h : Fin t → C × F) (c : C) :
    (A.magnitudeDirection B).play t h c = A.play t (fun s ↦ ((h s).1,
      (h s).2 (B.play s (fun r ↦ h (Fin.castLE s.2.le r)) (h s).1))) c • B.play t h c := (rfl)

/-- The plays of `A.magnitudeDirection B` are the plays of `A`, fed the losses `y s (B.run c y s)`
of the plays of `B`, times the plays of `B`, fed the losses `y s`. -/
@[simp]
lemma run_magnitudeDirection (c : ℕ → C) (y : ℕ → F) (t : ℕ) :
    (A.magnitudeDirection B).run c y t = A.run c (fun s ↦ y s (B.run c y s)) t • B.run c y t := by
  simp only [run_def, play_magnitudeDirection, Fin.val_castLE]

end Learner

section Regret

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FunLike F E ℝ] [LinearMapClass F ℝ E ℝ]
  (A : OnlineLearner C ℝ ℝ) (B : OnlineLearner C F E)

/-- **Dynamic regret of `A.magnitudeDirection B`** [JC22], [Ora, Theorem 14.5]: against
comparators `u t` of norm at most `U` on the first `n` rounds, it is the regret of `A` against `U`
on the losses it is fed plus `U` times the dynamic regret of `B` against `U⁻¹ • u t`. -/
theorem dynRegret_run_magnitudeDirection (c : ℕ → C) (y : ℕ → F) (u : ℕ → E) {U : ℝ} {n : ℕ}
    (hu : ∀ t < n, ‖u t‖ ≤ U) :
    dynRegret (fun t ↦ y t) ((A.magnitudeDirection B).run c y) u n =
      regret (fun t r ↦ y t (B.run c y t) * r) (A.run c fun s ↦ y s (B.run c y s)) U n +
        U * dynRegret (fun t ↦ y t) (B.run c y) (fun t ↦ U⁻¹ • u t) n := by
  rw [funext (A.run_magnitudeDirection B c y)]
  exact dynRegret_smul_eq_of_norm_le y _ _ u hu

/-- **Regret of `A.magnitudeDirection B`** [CO18], [Ora, Theorem 12.16]: against a comparator
`u`, it is the regret of `A` against `‖u‖` on the losses it is fed plus `‖u‖` times the regret of
`B` against `‖u‖⁻¹ • u`. -/
theorem regret_run_magnitudeDirection (c : ℕ → C) (y : ℕ → F) (u : E) (n : ℕ) :
    regret (fun t ↦ y t) ((A.magnitudeDirection B).run c y) u n =
      regret (fun t r ↦ y t (B.run c y t) * r) (A.run c fun s ↦ y s (B.run c y s)) ‖u‖ n +
        ‖u‖ * regret (fun t ↦ y t) (B.run c y) (‖u‖⁻¹ • u) n := by
  rw [funext (A.run_magnitudeDirection B c y)]
  exact regret_smul_eq y _ _ u n

variable {A B} {admA : C → ℝ → Prop} {UA : Set ℝ} {RA : ℕ → (ℕ → C) → (ℕ → ℝ) → ℝ → ℝ}
  {adm : C → F → Prop} {UB : Set E} {RB : ℕ → (ℕ → C) → (ℕ → F) → E → ℝ}

/-- **Regret guarantee of `A.magnitudeDirection B`** [CO18], [Ora, Theorem 12.16]. Let `A` have
the regret bound `RA` for one-dimensional linear losses against the comparators of `UA`, and `B`
the regret bound `RB` for the linear losses with admissible feedback `adm` against comparators
including the unit sphere. If the coefficients `y t (B.run c y t)` fed to `A` are admissible for
`A` whenever the losses `y t` are admissible, then the learner `A.magnitudeDirection B` has the
regret bound `RA` at `‖u‖` plus `‖u‖` times `RB` at `‖u‖⁻¹ • u`, against the comparators `u` with
`‖u‖ ∈ UA`. -/
theorem HasRegretBound.magnitudeDirection (hA : A.HasRegretBound (fun s r ↦ s * r) admA UA RA)
    (hB : B.HasRegretBound (fun y x ↦ y x) adm UB RB) (hUB : Metric.sphere 0 1 ⊆ UB)
    (hadm : ∀ (c : ℕ → C) (y : ℕ → F) t, adm (c t) (y t) → admA (c t) (y t (B.run c y t))) :
    (A.magnitudeDirection B).HasRegretBound (fun y x ↦ y x) adm (norm ⁻¹' UA)
      (fun n c y u ↦ RA n c (fun s ↦ y s (B.run c y s)) ‖u‖ + ‖u‖ * RB n c y (‖u‖⁻¹ • u)) := by
  refine hasRegretBound_iff.mpr fun c y n hy u hu ↦ ?_
  rw [regret_run_magnitudeDirection]
  refine add_le_add (hA.regret_le (fun t ht ↦ hadm c y t (hy t ht)) hu) ?_
  rcases eq_or_ne u 0 with rfl | hu₀
  · simp
  refine mul_le_mul_of_nonneg_left (hB.regret_le hy (hUB ?_)) (norm_nonneg u)
  simp [norm_smul, hu₀]

end Regret

section OfNormLE

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {A : OnlineLearner C ℝ ℝ}
  {B : OnlineLearner C (E →L[ℝ] ℝ) E} {L : ℝ} {UA : Set ℝ}
  {RA : ℕ → (ℕ → C) → (ℕ → ℝ) → ℝ → ℝ} {UB : Set E}
  {RB : ℕ → (ℕ → C) → (ℕ → E →L[ℝ] ℝ) → E → ℝ}

/-- **Regret guarantee of `A.magnitudeDirection B` for bounded losses** [CO18],
[Ora, Theorem 12.16]. If `B` plays in the unit ball, the coefficient `y t (x t)` fed to `A` has
absolute value at most `‖y t‖`. So a guarantee of `A` for the one-dimensional linear losses of
coefficients of absolute value at most `L`, and a guarantee of `B` for the linear losses of dual
norm at most `L` against comparators including the unit sphere, give a guarantee of
`A.magnitudeDirection B` for the linear losses of dual norm at most `L`. -/
theorem HasRegretBound.magnitudeDirection_of_norm_le
    (hA : A.HasRegretBound (fun s r ↦ s * r) (fun _ s ↦ |s| ≤ L) UA RA)
    (hB : B.HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) UB RB)
    (hUB : Metric.sphere 0 1 ⊆ UB) (hB₁ : ∀ c y t, ‖B.run c y t‖ ≤ 1) :
    (A.magnitudeDirection B).HasRegretBound (fun y x ↦ y x) (fun _ y ↦ ‖y‖ ≤ L) (norm ⁻¹' UA)
      (fun n c y u ↦ RA n c (fun s ↦ y s (B.run c y s)) ‖u‖ + ‖u‖ * RB n c y (‖u‖⁻¹ • u)) :=
  hA.magnitudeDirection hB hUB fun c y t hy ↦ by
    rw [← Real.norm_eq_abs]
    exact ((y t).unit_le_opNorm _ (hB₁ c y t)).trans hy

end OfNormLE

end OnlineLearner

end LMLExplore.OnlineLearning
