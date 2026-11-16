/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.OnlineLearning.MirrorDescent.Optimistic
public import LMLExplore.Analysis.Normed.Group.Basic
public import LMLExplore.Analysis.Real.Sqrt

/-!
# Mirror descent with delayed feedback

Online linear optimization on a set `K` of a real normed space `E`, with losses
`y t : E →L[ℝ] ℝ`, as in `LMLExplore.OnlineLearning.MirrorDescent.Basic`, when the feedback
arrives with a constant **delay** `τ`: the loss `y t` of round `t` is revealed only after round
`t + τ`. **Delayed mirror descent** [Ora, §6.12] keeps its initial play during the first `τ`
rounds, which receive no feedback, and then, at each round `t ≥ τ`, takes the mirror descent step
from `a t` for the loss `y (t - τ)` that has just arrived.

Delayed mirror descent is optimistic mirror descent
(`LMLExplore.OnlineLearning.MirrorDescent.Optimistic`) with the hints
`delayHint τ y t = -∑ t - τ ≤ s < t, y s`, minus the losses suffered but not yet observed: the
optimistic loss `y t - h t + h (t + 1)` of round `t` is `y (t - τ)` for `t ≥ τ` and `0` before
(`sub_delayHint_add_delayHint`). The hints are bad guesses, but the bounds of optimistic mirror
descent pay only for the prediction errors `y t - delayHint τ y t = ∑ t - τ ≤ s ≤ t, y s`, and the
factor `min` of [Ora, Theorem 6.38] measures them against the single loss `y (t - τ)` of the step.
When all losses have dual norm at most `L`, each round then costs `O(τ L ^ 2)` rather than the
`O(τ ^ 2 L ^ 2)` of the squared prediction error, which gives the regret `O(L √(τ n))` with a tuned
learning rate.

The horizon is `n + 1`, the rounds `0, …, n`: the plays `a 0, …, a n` are all that the regret
involves, and no step after the last play is needed.

## Main definitions

* `delayHint τ y t`: the hint `-∑ t - τ ≤ s < t, y s` that turns a delay `τ` into optimism.

## Main statements

* `sub_delayHint`, `sub_delayHint_add_delayHint`: the prediction errors of the delay hints, and
  the optimistic losses `y (t - τ)` (or `0` for `t < τ`) that they produce.
* `sum_apply_sub_le_delayedMirrorDescent`: for any positive learning rates, the regret bound
  before the divergences to the comparator are bounded.
* `delayedMirrorDescent_regret_le_of_strongConvexOn_of_antitone`: [Ora, §6.12] with nonincreasing
  learning rates, an `m`-strongly convex potential and divergences `D_F(u, a t) ≤ D` for `t ≤ n`,
  `∑ t < n + 1, y t (a t - u) ≤ D / η n
    + ∑ τ ≤ t < n, η t / (2 m) * ‖∑ t - τ ≤ s ≤ t, y s‖ * min ‖∑ t - τ ≤ s ≤ t, y s‖ (2 ‖y (t - τ)‖)
    + η n / (2 m) * ‖∑ n - τ ≤ s ≤ n, y s‖ ^ 2`.
* `delayedMirrorDescent_regret_le_of_strongConvexOn`: its form with `D_F(u, a 0) / η` for a
  constant learning rate `η`.
* `delayedMirrorDescent_regret_le_of_norm_le`: for losses of dual norm at most `L`, the regret is
  at most `D_F(u, a 0) / η + 3 η (τ + 1) (n + 1) L ^ 2 / (2 m)`.
* `delayedMirrorDescent_regret_le_sqrt`: with the tuned learning rate, the regret is at most
  `L √(6 (τ + 1) (n + 1) D / m)` for `D_F(u, a 0) ≤ D`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026, §6.12.
-/

public section

open Finset

namespace LMLExplore.OnlineLearning

section DelayHint

variable {M : Type*} [AddCommGroup M]

/-- The **hint of delayed feedback** [Ora, §6.12]: with a delay `τ`, the hint of round `t` is
`-∑ t - τ ≤ s < t, y s`, minus the losses of the rounds before `t` whose feedback has not arrived
at round `t`. Optimistic mirror descent with these hints is delayed mirror descent
(`sub_delayHint_add_delayHint`). -/
def delayHint (τ : ℕ) (y : ℕ → M) (t : ℕ) : M := -∑ s ∈ Ico (t - τ) t, y s

theorem delayHint_def (τ : ℕ) (y : ℕ → M) (t : ℕ) :
    delayHint τ y t = -∑ s ∈ Ico (t - τ) t, y s := (rfl)

/-- With no delay, the hints vanish. -/
@[simp]
theorem delayHint_zero (y : ℕ → M) : delayHint 0 y = 0 := by
  ext t
  simp [delayHint_def]

/-- The hint of the first round vanishes, as optimistic mirror descent requires. -/
@[simp]
theorem delayHint_apply_zero (τ : ℕ) (y : ℕ → M) : delayHint τ y 0 = 0 := by
  simp [delayHint_def]

/-- The prediction error of the hint of round `t` is the sum `∑ t - τ ≤ s ≤ t, y s` of the losses
not observed before round `t` and of the loss of round `t`. -/
theorem sub_delayHint (τ : ℕ) (y : ℕ → M) (t : ℕ) :
    y t - delayHint τ y t = ∑ s ∈ Icc (t - τ) t, y s := by
  rw [delayHint_def, sub_neg_eq_add, add_sum_Ico_eq_sum_Icc (t.sub_le τ)]

/-- **Delayed feedback is optimism** [Ora, §6.12]. With the hints `delayHint τ y`, the loss
`y t - h t + h (t + 1)` of optimistic mirror descent at round `t` is the loss `y (t - τ)` that
arrives at round `t` if `τ ≤ t`, and `0` if no loss has arrived yet. -/
theorem sub_delayHint_add_delayHint (τ : ℕ) (y : ℕ → M) (t : ℕ) :
    y t - delayHint τ y t + delayHint τ y (t + 1) = if τ ≤ t then y (t - τ) else 0 := by
  rw [sub_delayHint, delayHint_def, ← Ico_add_one_right_eq_Icc]
  split_ifs with hτ
  · rw [sum_eq_sum_Ico_succ_bot (by omega), show t + 1 - τ = t - τ + 1 by omega,
      add_neg_cancel_right]
  · rw [show t + 1 - τ = t - τ by omega, add_neg_cancel]

end DelayHint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ}
  {n τ : ℕ} {u : E}

/-- **Regret of delayed mirror descent for any positive learning rates** [Ora, §6.12]. Let `F` be
`m`-strongly convex on `K`, with `m > 0`, and let `η t > 0` for `t ≤ n`. Let `a 0 ∈ K`, let the
play be kept during the first `τ` rounds, `a (t + 1) = a t` for `t < τ`, and for `τ ≤ t < n` let
`a (t + 1)` be a mirror descent step on `K` from `a t` with derivative `F' t` and learning rate
`η t`, for the loss `y (t - τ)`, which arrives at the end of round `t`, where `F` has derivative
`F' t` within `K` at `a t` for `t ≤ n`. Then over the `n + 1` rounds `0, …, n`, for every `u ∈ K`,
the regret `∑ t < n + 1, y t (a t - u)` is at most
`D_F(u, a 0) / η 0 + ∑ t < n, (1 / η (t + 1) - 1 / η t) * D_F(u, a (t + 1))
  + ∑ τ ≤ t < n, η t / (2 m) * ‖∑ t - τ ≤ s ≤ t, y s‖ * min ‖∑ t - τ ≤ s ≤ t, y s‖ (2 ‖y (t - τ)‖)
  + η n / (2 m) * ‖∑ n - τ ≤ s ≤ n, y s‖ ^ 2`,
where the norms are dual norms. -/
theorem sum_apply_sub_le_delayedMirrorDescent {η : ℕ → ℝ} {m : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hη : ∀ t ≤ n, 0 < η t) (y : ℕ → E →L[ℝ] ℝ)
    (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K) (ha_wait : ∀ t < n, t < τ → a (t + 1) = a t)
    (ha : ∀ t < n, τ ≤ t → IsMirrorDescentStep K F (η t) (y (t - τ)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range (n + 1), y t (a t - u) ≤ bregDiv F u (a 0) (F' 0) / η 0 +
      ∑ t ∈ range n, ((η (t + 1))⁻¹ - (η t)⁻¹) * bregDiv F u (a (t + 1)) (F' (t + 1)) +
      ∑ t ∈ Ico τ n, η t / (2 * m) *
        (‖∑ s ∈ Icc (t - τ) t, y s‖ * min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖)) +
      η n / (2 * m) * ‖∑ s ∈ Icc (n - τ) n, y s‖ ^ 2 := by
  have hF_cvx := strongConvexOn_zero.mp (hF.mono hm.le)
  -- the plays stay in `K`: a waiting round keeps the play, a step lands in `K`
  have h_mem : ∀ t ≤ n, a t ∈ K := by
    intro t
    induction t with
    | zero => exact fun _ ↦ ha0K
    | succ t ih =>
      intro ht
      by_cases hτ : τ ≤ t
      · exact (ha t ht hτ).mem
      · rw [ha_wait t ht (not_le.mp hτ)]
        exact ih (by omega)
  -- the plays are those of optimistic mirror descent with the delay hints
  have h_step : ∀ t < n, IsMirrorDescentStep K F (η t)
      (y t - delayHint τ y t + delayHint τ y (t + 1)) (a t) (F' t) (a (t + 1)) := by
    intro t ht
    rw [sub_delayHint_add_delayHint]
    split_ifs with hτ
    · exact ha t ht hτ
    · rw [ha_wait t ht (not_le.mp hτ)]
      exact isMirrorDescentStep_zero_self (h_mem t ht.le)
        ((hF' t ht.le).hasSubgradientWithinAt hF_cvx (h_mem t ht.le))
  have h := sum_apply_sub_le_optimisticMirrorDescent hF hm hη y (delayHint τ y)
    (delayHint_apply_zero τ y) a F' ha0K h_step hF' hu
  simp only [sub_delayHint_add_delayHint] at h
  simp only [sub_delayHint] at h
  -- the rounds `t < τ` take no step and cost nothing
  have h_wait : ∑ t ∈ range n, η t / (2 * m) * (‖∑ s ∈ Icc (t - τ) t, y s‖ *
      min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖if τ ≤ t then y (t - τ) else 0‖)) =
      ∑ t ∈ Ico τ n, η t / (2 * m) *
        (‖∑ s ∈ Icc (t - τ) t, y s‖ * min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖)) := by
    rw [← sum_subset (fun t ht ↦ mem_range.mpr (mem_Ico.mp ht).2)]
    · exact sum_congr rfl fun t ht ↦ by simp only [(mem_Ico.mp ht).1, ↓reduceIte]
    · intro t ht_range ht
      have hτ : ¬τ ≤ t := fun hτ ↦ ht (mem_Ico.mpr ⟨hτ, mem_range.mp ht_range⟩)
      simp [hτ]
  linarith

/-- **Regret of delayed mirror descent with nonincreasing learning rates** [Ora, §6.12]. Let `F`
be `m`-strongly convex on `K`, with `m > 0`, and let the learning rates `η t > 0` be
nonincreasing. Let `a 0 ∈ K`, let the play be kept during the first `τ` rounds,
`a (t + 1) = a t` for `t < τ`, and for `τ ≤ t < n` let `a (t + 1)` be a mirror descent step on
`K` from `a t` with derivative `F' t` and learning rate `η t`, for the loss `y (t - τ)`, which
arrives at the end of round `t`, where `F` has derivative `F' t` within `K` at `a t` for `t ≤ n`.
If `D` bounds the Bregman divergences `D_F(u, a t)` for `t ≤ n`, then over the `n + 1` rounds
`0, …, n`, for every `u ∈ K`,
`∑ t < n + 1, y t (a t - u) ≤ D / η n
  + ∑ τ ≤ t < n, η t / (2 m) * ‖∑ t - τ ≤ s ≤ t, y s‖ * min ‖∑ t - τ ≤ s ≤ t, y s‖ (2 ‖y (t - τ)‖)
  + η n / (2 m) * ‖∑ n - τ ≤ s ≤ n, y s‖ ^ 2`,
where the norms are dual norms. Each summand is at most `η t / m * ‖∑ t - τ ≤ s ≤ t, y s‖ *
‖y (t - τ)‖`, linear in the number `τ + 1` of losses of the prediction error. -/
theorem delayedMirrorDescent_regret_le_of_strongConvexOn_of_antitone {η : ℕ → ℝ} {m : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hη : ∀ t, 0 < η t) (hη_anti : Antitone η)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha_wait : ∀ t < n, t < τ → a (t + 1) = a t)
    (ha : ∀ t < n, τ ≤ t → IsMirrorDescentStep K F (η t) (y (t - τ)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) {D : ℝ}
    (hDu : ∀ t ≤ n, bregDiv F u (a t) (F' t) ≤ D) (hu : u ∈ K) :
    ∑ t ∈ range (n + 1), y t (a t - u) ≤ D / η n +
      ∑ t ∈ Ico τ n, η t / (2 * m) *
        (‖∑ s ∈ Icc (t - τ) t, y s‖ * min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖)) +
      η n / (2 * m) * ‖∑ s ∈ Icc (n - τ) n, y s‖ ^ 2 := by
  have h := sum_apply_sub_le_delayedMirrorDescent hF hm (fun t _ ↦ hη t) y a F' ha0K ha_wait ha
    hF' hu
  have h_parts := div_add_sum_inv_sub_inv_mul_le_div hη hη_anti
    (d := fun t ↦ bregDiv F u (a t) (F' t)) hDu
  linarith

/-- **Regret of delayed mirror descent with a constant learning rate** [Ora, §6.12]. Under the
assumptions of `delayedMirrorDescent_regret_le_of_strongConvexOn_of_antitone`, with a constant
learning rate `η > 0` instead, for every `u ∈ K`,
`∑ t < n + 1, y t (a t - u) ≤ D_F(u, a 0) / η + η / (2 m) *
  (∑ τ ≤ t < n, ‖∑ t - τ ≤ s ≤ t, y s‖ * min ‖∑ t - τ ≤ s ≤ t, y s‖ (2 ‖y (t - τ)‖)
    + ‖∑ n - τ ≤ s ≤ n, y s‖ ^ 2)`,
where the norms are dual norms. -/
theorem delayedMirrorDescent_regret_le_of_strongConvexOn {η m : ℝ} (hF : StrongConvexOn K m F)
    (hm : 0 < m) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha0K : a 0 ∈ K) (ha_wait : ∀ t < n, t < τ → a (t + 1) = a t)
    (ha : ∀ t < n, τ ≤ t → IsMirrorDescentStep K F η (y (t - τ)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range (n + 1), y t (a t - u) ≤ bregDiv F u (a 0) (F' 0) / η + η / (2 * m) *
      (∑ t ∈ Ico τ n,
          ‖∑ s ∈ Icc (t - τ) t, y s‖ * min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖) +
        ‖∑ s ∈ Icc (n - τ) n, y s‖ ^ 2) := by
  have h := sum_apply_sub_le_delayedMirrorDescent (η := fun _ ↦ η) hF hm (fun _ _ ↦ hη) y a F'
    ha0K ha_wait ha hF' hu
  simp only [sub_self, zero_mul, sum_const_zero, add_zero] at h
  rw [mul_add, mul_sum]
  linarith

/-- **Regret of delayed mirror descent for bounded losses** [Ora, §6.12]. Under the assumptions of
`delayedMirrorDescent_regret_le_of_strongConvexOn`, if the losses have dual norm `‖y t‖ ≤ L` for
`t ≤ n`, then for every `u ∈ K`,
`∑ t < n + 1, y t (a t - u) ≤ D_F(u, a 0) / η + 3 η (τ + 1) (n + 1) L ^ 2 / (2 m)`.
Without delay, mirror descent has the bound `D_F(u, a 0) / η + η (n + 1) L ^ 2 / (2 m)`: the delay
multiplies the second term by `O(τ + 1)`, not by the `(τ + 1) ^ 2` of the squared prediction
errors. -/
theorem delayedMirrorDescent_regret_le_of_norm_le {η m L : ℝ} (hF : StrongConvexOn K m F)
    (hm : 0 < m) (hη : 0 < η) (y : ℕ → E →L[ℝ] ℝ) (hy : ∀ t ≤ n, ‖y t‖ ≤ L) (a : ℕ → E)
    (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K) (ha_wait : ∀ t < n, t < τ → a (t + 1) = a t)
    (ha : ∀ t < n, τ ≤ t → IsMirrorDescentStep K F η (y (t - τ)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hu : u ∈ K) :
    ∑ t ∈ range (n + 1), y t (a t - u) ≤
      bregDiv F u (a 0) (F' 0) / η + 3 * η * (τ + 1) * (n + 1) * L ^ 2 / (2 * m) := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hy 0 n.zero_le)
  have h := delayedMirrorDescent_regret_le_of_strongConvexOn hF hm hη y a F' ha0K ha_wait ha hF'
    hu
  -- each of the at most `n` rounds `τ ≤ t < n` costs at most `2 (τ + 1) L ^ 2`
  have h_sum : ∑ t ∈ Ico τ n,
      ‖∑ s ∈ Icc (t - τ) t, y s‖ * min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖) ≤
        n * (2 * (τ + 1) * L ^ 2) := by
    refine (sum_le_card_nsmul _ _ (2 * (τ + 1) * L ^ 2) fun t ht ↦ ?_).trans ?_
    · have ht := mem_Ico.mp ht
      have h_min : min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖) ≤ 2 * L :=
        (min_le_right _ _).trans (by linarith [hy (t - τ) (by omega)])
      calc ‖∑ s ∈ Icc (t - τ) t, y s‖ * min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖)
          ≤ ((τ + 1) * L) * (2 * L) :=
            mul_le_mul (norm_sum_Icc_sub_le t τ fun s hs ↦ hy s (hs.trans ht.2.le)) h_min
              (le_min (norm_nonneg _) (by positivity)) (by positivity)
        _ = 2 * (τ + 1) * L ^ 2 := by ring
    · rw [nsmul_eq_mul, Nat.card_Ico]
      gcongr
      exact_mod_cast n.sub_le τ
  -- the last prediction error is a sum of at most `min (τ + 1) (n + 1)` losses
  have h_last : ‖∑ s ∈ Icc (n - τ) n, y s‖ ^ 2 ≤ (τ + 1) * (n + 1) * L ^ 2 := by
    have h_bd := norm_sum_le_card_mul (Icc (n - τ) n) fun s hs ↦ hy s (mem_Icc.mp hs).2
    rw [Nat.card_Icc] at h_bd
    have h1 : ((n + 1 - (n - τ) : ℕ) : ℝ) ≤ τ + 1 := by exact_mod_cast (by omega)
    have h2 : ((n + 1 - (n - τ) : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast (by omega)
    calc ‖∑ s ∈ Icc (n - τ) n, y s‖ ^ 2 ≤ (((n + 1 - (n - τ) : ℕ) : ℝ) * L) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h_bd 2
      _ = ((n + 1 - (n - τ) : ℕ) : ℝ) * ((n + 1 - (n - τ) : ℕ) : ℝ) * L ^ 2 := by ring
      _ ≤ (τ + 1) * (n + 1) * L ^ 2 := by gcongr
  have h_total : η / (2 * m) * (∑ t ∈ Ico τ n,
      ‖∑ s ∈ Icc (t - τ) t, y s‖ * min ‖∑ s ∈ Icc (t - τ) t, y s‖ (2 * ‖y (t - τ)‖) +
        ‖∑ s ∈ Icc (n - τ) n, y s‖ ^ 2) ≤ 3 * η * (τ + 1) * (n + 1) * L ^ 2 / (2 * m) := by
    calc _ ≤ η / (2 * m) * (n * (2 * (τ + 1) * L ^ 2) + (τ + 1) * (n + 1) * L ^ 2) := by
          gcongr
      _ ≤ η / (2 * m) * (3 * (τ + 1) * (n + 1) * L ^ 2) := by
          gcongr
          nlinarith [sq_nonneg L, (n.cast_nonneg : (0 : ℝ) ≤ n), (τ.cast_nonneg : (0 : ℝ) ≤ τ)]
      _ = 3 * η * (τ + 1) * (n + 1) * L ^ 2 / (2 * m) := by ring
  linarith

/-- **Regret of delayed mirror descent with a tuned learning rate** [Ora, §6.12]. Under the
assumptions of `delayedMirrorDescent_regret_le_of_norm_le`, with `L > 0`, `D > 0` bounding the
divergence `D_F(u, a 0)` and the learning rate `η = √(2 D / b)` for
`b = 3 (τ + 1) (n + 1) L ^ 2 / m`, which depends on the delay and the horizon, for every `u ∈ K`,
`∑ t < n + 1, y t (a t - u) ≤ L √(6 (τ + 1) (n + 1) D / m)`.
This is the regret `O(L √(τ n))` of [Ora]. -/
theorem delayedMirrorDescent_regret_le_sqrt {η m L D : ℝ} (hF : StrongConvexOn K m F) (hm : 0 < m)
    (hL : 0 < L) (hD : 0 < D) (hη : η = √(2 * D / (3 * (τ + 1) * (n + 1) * L ^ 2 / m)))
    (y : ℕ → E →L[ℝ] ℝ) (hy : ∀ t ≤ n, ‖y t‖ ≤ L) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ)
    (ha0K : a 0 ∈ K) (ha_wait : ∀ t < n, t < τ → a (t + 1) = a t)
    (ha : ∀ t < n, τ ≤ t → IsMirrorDescentStep K F η (y (t - τ)) (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t)) (hDu : bregDiv F u (a 0) (F' 0) ≤ D)
    (hu : u ∈ K) :
    ∑ t ∈ range (n + 1), y t (a t - u) ≤ L * √(6 * (τ + 1) * (n + 1) * D / m) := by
  set b : ℝ := 3 * (τ + 1) * (n + 1) * L ^ 2 / m with hb
  have hb_pos : 0 < b := by positivity
  have hη_pos : 0 < η := hη ▸ Real.sqrt_pos.mpr (by positivity)
  have h := delayedMirrorDescent_regret_le_of_norm_le hF hm hη_pos y hy a F' ha0K ha_wait ha hF'
    hu
  have h_init : bregDiv F u (a 0) (F' 0) / η ≤ D / η := div_le_div_of_nonneg_right hDu hη_pos.le
  -- the tuned rate balances `D / η` and `η b / 2`
  have h_tune := Real.div_sqrt_add_sqrt_mul_div_two D hb_pos.le
  rw [← hη] at h_tune
  have h_eq : 3 * η * (τ + 1) * (n + 1) * L ^ 2 / (2 * m) = η * b / 2 := by
    rw [hb]
    field_simp
  have h_sqrt : √(2 * b * D) = L * √(6 * (τ + 1) * (n + 1) * D / m) := by
    rw [show 2 * b * D = L ^ 2 * (6 * (τ + 1) * (n + 1) * D / m) by rw [hb]; field_simp; ring,
      Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]
  linarith

end LMLExplore.OnlineLearning
