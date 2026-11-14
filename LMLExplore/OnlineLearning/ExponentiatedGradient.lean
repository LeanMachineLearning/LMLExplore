/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Analysis.Convex.NegEntropy
public import LMLExplore.OnlineLearning.ExponentialWeights
public import LMLExplore.OnlineLearning.MirrorDescent

/-!
# Exponentiated gradient: mirror descent with the negative entropy on the simplex

On the simplex `simplex α` of `α → ℝ`, the step of mirror descent with the negative entropy
`negEntropy`, from a point `w` with positive coordinates, with learning rate `η` and the linear loss
`b ↦ ∑ a, ℓ a * b a`, is the multiplicative weights update
`a ↦ w a * exp (-(η * ℓ a)) / ∑ b, w b * exp (-(η * ℓ b))`, which is
`softmax (log w - η ℓ)` [Ora, Section 6.6, (6.12)]. The derivative of the negative entropy at `w`
is `∑ a, log (w a) • ContinuousLinearMap.proj a` (`LMLExplore.hasFDerivAt_negEntropy_pi`).

The proof is the Gibbs variational principle: on the simplex, the objective
`b ↦ η ⟨ℓ, b⟩ + D(b, w)` of the step is the relative entropy of `b` to the update, minus the
log-partition function `log ∑ a, w a * exp (-(η * ℓ a))`. So the update is the unique step, and the
minimum value of the objective is `-log ∑ a, w a * exp (-(η * ℓ a))`. In particular every step stays
in the interior of the simplex, the steps do not change when a constant is added to the loss, and
from the uniform point with a constant learning rate the exact trajectory is the sequence of
exponential weights `softmax (-(η • ∑ s < t, ℓ s))`, to which the regret bounds of
`LMLExplore.OnlineLearning.ExponentialWeights` apply (for instance `softmax_regret_le`). The
analysis of mirror descent with the negative entropy and approximate steps [SSKM26, Section 5.3,
Appendix D] uses the step in this form, with the minimum value of its objective.

## Main statements

* `LMLExplore.OnlineLearning.mul_apply_add_bregDiv_negEntropy_eq`: the objective of a step is the
  relative entropy to the multiplicative weights update, minus `log ∑ a, w a * exp (-(η * ℓ a))`.
* `LMLExplore.OnlineLearning.isLeast_mul_apply_add_bregDiv_negEntropy`: the minimum value of the
  objective over the simplex is `-log ∑ a, w a * exp (-(η * ℓ a))`, attained at the update.
* `LMLExplore.OnlineLearning.isMirrorDescentStep_negEntropy_iff`: the step of mirror descent with
  the negative entropy is unique, and it is the multiplicative weights update.
* `LMLExplore.OnlineLearning.IsMirrorDescentStep.pos_of_negEntropy`: the steps have positive
  coordinates.
* `LMLExplore.OnlineLearning.isMirrorDescentStep_negEntropy_add_const_iff`: adding a constant to
  the loss changes no step.
* `LMLExplore.OnlineLearning.isMirrorDescentStep_negEntropy_softmax`,
  `LMLExplore.OnlineLearning.eq_softmax_of_isMirrorDescentStep_negEntropy`: from the uniform point
  with a constant learning rate, exponential weights are the exact trajectory, and the only one.

## Implementation notes

This file is adapted from `ForLMLExplore/OnlineLearning/ExponentiatedGradient.lean` in the
formalization of [SSKM26] in the paper project `RemyDegenne/Schlisselberg2026Hidden`
(same author). The minimum value of the objective is obtained here from the Gibbs variational
principle `LMLExplore.isGreatest_sum_mul_sub_sum_mul_log_div`.

## References

* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
* [SSKM26] O. Schlisselberg, U. Sherman, T. Koren and Y. Mansour, *The hidden cost of
  approximation in online mirror descent*, arXiv:2511.22283v2, 2026.
-/

public section

open Finset Real

namespace LMLExplore.OnlineLearning

variable {α : Type*} [Fintype α] {w b x : α → ℝ} {ℓ : α → ℝ} {η : ℝ}

/-- The objective `η ⟨ℓ, b⟩ + D(b, w)` of a step of mirror descent with the negative entropy, at
`b ∈ simplex α`, written out as `∑ a, b a * (η * ℓ a) + ∑ a, b a * log (b a / w a)`. -/
private lemma mul_apply_add_bregDiv_negEntropy_eq_sum (hw : w ∈ simplex α)
    (hpos : ∀ a, 0 < w a) (ℓ : α → ℝ) (η : ℝ) (hb : b ∈ simplex α) :
    η * (∑ a, ℓ a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) b +
        bregDiv negEntropy b w
          (∑ a, log (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
      ∑ a, b a * (η * ℓ a) + ∑ a, b a * log (b a / w a) := by
  rw [bregDiv_negEntropy_pi hb hw fun a h ↦ absurd h (hpos a).ne']
  simp [mul_sum, mul_left_comm, mul_comm]

/-- **The objective of a step of mirror descent with the negative entropy.** From `w ∈ simplex α`
with positive coordinates, with learning rate `η` and loss `ℓ`, the objective
`η ⟨ℓ, b⟩ + D(b, w)` at `b ∈ simplex α` is the relative entropy of `b` to the multiplicative
weights update `softmax (log w - η ℓ)`, minus `log ∑ a, w a * exp (-(η * ℓ a))`. -/
theorem mul_apply_add_bregDiv_negEntropy_eq (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (ℓ : α → ℝ) (η : ℝ) (hb : b ∈ simplex α) :
    η * (∑ a, ℓ a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) b +
        bregDiv negEntropy b w
          (∑ a, log (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
      ∑ a, b a * log (b a / softmax (fun a ↦ log (w a) - η * ℓ a) a) -
        log (∑ a, w a * exp (-(η * ℓ a))) := by
  have := nonempty_of_mem_simplex hw
  have hZ : ∑ a, w a * exp (-(η * ℓ a)) ≠ 0 :=
    (sum_pos (fun a _ ↦ mul_pos (hpos a) (exp_pos _)) univ_nonempty).ne'
  have hm : softmax (fun a ↦ log (w a) - η * ℓ a) =
      fun a ↦ w a * exp (-(η * ℓ a)) / ∑ b, w b * exp (-(η * ℓ b)) := by
    funext a
    simp_rw [sub_eq_add_neg]
    exact softmax_log_add_apply hpos _ a
  have hwb (a : α) : w a = 0 → b a = 0 := fun h ↦ absurd h (hpos a).ne'
  rw [mul_apply_add_bregDiv_negEntropy_eq_sum hw hpos ℓ η hb, hm,
    sum_mul_log_div_mul_exp_div_eq (mem_simplex_iff.1 hb).2 hwb hZ]
  simp only [mul_neg, sum_neg_distrib]
  ring

/-- **The minimum of the objective of a step of mirror descent with the negative entropy** (the
Gibbs variational principle). From `w ∈ simplex α` with positive coordinates, the minimum over the
simplex of the objective `b ↦ η ⟨ℓ, b⟩ + D(b, w)` is `-log ∑ a, w a * exp (-(η * ℓ a))`, attained
at the multiplicative weights update `softmax (log w - η ℓ)`. -/
theorem isLeast_mul_apply_add_bregDiv_negEntropy (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (ℓ : α → ℝ) (η : ℝ) :
    IsLeast ((fun b ↦ η * (∑ a, ℓ a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) b +
        bregDiv negEntropy b w
          (∑ a, log (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ)) '' simplex α)
      (-log (∑ a, w a * exp (-(η * ℓ a)))) := by
  -- the objective is the negative of the Gibbs variational objective for `-(η • ℓ)`
  have hobj (b : α → ℝ) (hb : b ∈ simplex α) :
      η * (∑ a, ℓ a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) b +
          bregDiv negEntropy b w
            (∑ a, log (w a) • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ) =
        -(∑ a, b a * -(η * ℓ a) - ∑ a, b a * log (b a / w a)) := by
    rw [mul_apply_add_bregDiv_negEntropy_eq_sum hw hpos ℓ η hb]
    simp only [mul_neg, sum_neg_distrib]
    ring
  obtain ⟨⟨q, hq, hq_eq⟩, h_le⟩ :=
    isGreatest_sum_mul_sub_sum_mul_log_div hw hpos fun a ↦ -(η * ℓ a)
  refine ⟨⟨q, hq, ?_⟩, ?_⟩
  · simp only at hq_eq ⊢
    rw [hobj q hq, hq_eq]
  · rintro _ ⟨b, hb, rfl⟩
    simp only
    rw [hobj b hb]
    exact neg_le_neg (h_le ⟨b, hb, rfl⟩)

/-- **Mirror descent with the negative entropy is multiplicative weights** [Ora, Section 6.6,
(6.12)]. From `w ∈ simplex α` with positive coordinates, the step of mirror descent on the simplex
with the negative entropy, learning rate `η` and loss `ℓ` is unique, and it is
`softmax (log w - η ℓ)`, the vector `a ↦ w a * exp (-(η * ℓ a))` normalized
(`softmax_log_add_apply`). -/
theorem isMirrorDescentStep_negEntropy_iff (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a) :
    IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) x ↔
      x = softmax (fun a ↦ log (w a) - η * ℓ a) := by
  have := nonempty_of_mem_simplex hw
  set p := softmax fun a ↦ log (w a) - η * ℓ a
  have hp : p ∈ simplex α := softmax_mem_simplex _
  have hpx (y : α → ℝ) (a : α) : p a = 0 → y a = 0 := fun h ↦ absurd h (softmax_pos _ a).ne'
  have hp_self : ∑ a, p a * log (p a / p a) = 0 := by simp
  constructor
  · intro h
    have h_le := isMinOn_iff.1 h.isMinOn p hp
    rw [mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η h.mem,
      mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η hp, hp_self] at h_le
    have h0 := sum_mul_log_div_nonneg (mem_simplex_iff.1 h.mem).1 (softmax_nonneg _) (hpx x)
      (by rw [sum_softmax, (mem_simplex_iff.1 h.mem).2] : ∑ a, p a ≤ ∑ a, x a)
    exact (sum_mul_log_div_eq_zero_iff h.mem hp (hpx x)).1 (by linarith)
  · rintro rfl
    refine ⟨hp, isMinOn_iff.2 fun b hb ↦ ?_⟩
    have h_least := (isLeast_mul_apply_add_bregDiv_negEntropy hw hpos ℓ η).2
    rw [mul_apply_add_bregDiv_negEntropy_eq hw hpos ℓ η hp, hp_self, zero_sub]
    exact h_least ⟨b, hb, rfl⟩

/-- The multiplicative weights update `softmax (log w - η ℓ)` is a step of mirror descent with the
negative entropy from a point `w` of the simplex with positive coordinates. -/
theorem isMirrorDescentStep_negEntropy (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (ℓ : α → ℝ) (η : ℝ) :
    IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
      (∑ a, log (w a) • ContinuousLinearMap.proj a) (softmax fun a ↦ log (w a) - η * ℓ a) :=
  (isMirrorDescentStep_negEntropy_iff hw hpos).2 rfl

/-- **The steps of mirror descent with the negative entropy stay in the interior of the simplex**:
from a point of the simplex with positive coordinates, a step has positive coordinates. -/
theorem IsMirrorDescentStep.pos_of_negEntropy (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (h : IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
      (∑ a, log (w a) • ContinuousLinearMap.proj a) x) (a : α) : 0 < x a := by
  have := nonempty_of_mem_simplex hw
  rw [(isMirrorDescentStep_negEntropy_iff hw hpos).1 h]
  exact softmax_pos _ a

/-- Adding a constant to every coordinate of the loss changes no step of mirror descent with the
negative entropy on the simplex. -/
theorem isMirrorDescentStep_negEntropy_add_const_iff (hw : w ∈ simplex α) (hpos : ∀ a, 0 < w a)
    (c : ℝ) :
    IsMirrorDescentStep (simplex α) negEntropy η (∑ a, (ℓ a + c) • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) x ↔
      IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ a • ContinuousLinearMap.proj a) w
        (∑ a, log (w a) • ContinuousLinearMap.proj a) x := by
  rw [isMirrorDescentStep_negEntropy_iff (ℓ := fun a ↦ ℓ a + c) hw hpos,
    isMirrorDescentStep_negEntropy_iff hw hpos]
  have h : (fun a ↦ log (w a) - η * (ℓ a + c)) = fun a ↦ (log (w a) - η * ℓ a) + -(η * c) := by
    funext a
    ring
  rw [h, softmax_add_const]

/-- **Exponential weights are a trajectory of mirror descent with the negative entropy**: with a
constant learning rate `η`, the step of round `t` from `softmax (-(η • ∑ s < t, ℓ s))`, with the
loss `ℓ t`, is `softmax (-(η • ∑ s < t + 1, ℓ s))`. -/
theorem isMirrorDescentStep_negEntropy_softmax [Nonempty α] (ℓ : ℕ → α → ℝ) (η : ℝ) (t : ℕ) :
    IsMirrorDescentStep (simplex α) negEntropy η (∑ a, ℓ t a • ContinuousLinearMap.proj a)
      (softmax (-(η • ∑ s ∈ range t, ℓ s)))
      (∑ a, log (softmax (-(η • ∑ s ∈ range t, ℓ s)) a) • ContinuousLinearMap.proj a)
      (softmax (-(η • ∑ s ∈ range (t + 1), ℓ s))) := by
  rw [isMirrorDescentStep_negEntropy_iff (softmax_mem_simplex _) (softmax_pos _)]
  simp_rw [sub_eq_add_neg, softmax_log_softmax_add]
  congr 1
  funext a
  simp only [sum_range_succ, Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Finset.sum_apply,
    smul_eq_mul]
  ring

/-- **The trajectory of mirror descent with the negative entropy from the uniform point**: a
sequence started at the uniform point whose terms, up to round `n`, are steps of mirror descent on
the simplex with the negative entropy, a constant learning rate `η` and the losses `ℓ t`, is the
sequence of exponential weights `b t = softmax (-(η • ∑ s < t, ℓ s))` for `t ≤ n`. -/
theorem eq_softmax_of_isMirrorDescentStep_negEntropy [Nonempty α] {ℓ : ℕ → α → ℝ}
    {b : ℕ → α → ℝ} {n : ℕ} (h0 : b 0 = fun _ ↦ (Fintype.card α : ℝ)⁻¹)
    (hstep : ∀ t < n, IsMirrorDescentStep (simplex α) negEntropy η
      (∑ a, ℓ t a • ContinuousLinearMap.proj a) (b t)
      (∑ a, log (b t a) • ContinuousLinearMap.proj a) (b (t + 1))) :
    ∀ t ≤ n, b t = softmax (-(η • ∑ s ∈ range t, ℓ s)) := by
  intro t ht
  induction t with
  | zero => simp [h0]
  | succ t ih =>
    have h := hstep t (by omega)
    rw [ih (by omega)] at h
    have h' := isMirrorDescentStep_negEntropy_softmax ℓ η t
    rw [isMirrorDescentStep_negEntropy_iff (softmax_mem_simplex _) (softmax_pos _)] at h h'
    rw [h, h']

end LMLExplore.OnlineLearning
