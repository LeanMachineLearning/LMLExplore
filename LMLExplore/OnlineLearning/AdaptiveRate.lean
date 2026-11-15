/-
Copyright (c) 2026 LMLExplore contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LMLExplore contributors
-/
module

public import LMLExplore.Algebra.Order.Interval.Set.ProjIcc
public import LMLExplore.Analysis.Convex.Smooth
public import LMLExplore.Analysis.SumIntegralComparisons
public import LMLExplore.OnlineLearning.Learner.Operations
public import LMLExplore.OnlineLearning.SubgradientDescent
import TauCeti.Analysis.Real.Sqrt

/-!
# Adaptive learning rates, `L⋆` bounds and AdaGrad

The regret bound of mirror descent with nonincreasing learning rates `η t` and an `m`-strongly
convex potential `F` is `B / η (n - 1) + ∑ t < n, η t / (2 m) * ‖y t‖ ^ 2`, where `B` bounds the
Bregman divergences `D_F(u, a t)` from the plays to the comparator. The learning rate that
balances the two terms after `n` rounds depends on the losses to come. The **adaptive learning
rates** [Ora, Section 4.2, Theorem 4.14]
`η t = √(m B / ∑ s ≤ t, ‖y s‖ ^ 2)`
use instead the losses observed so far, the loss of the current round included, and give the
regret bound `2 √(B ∑ t < n, ‖y t‖ ^ 2 / m)` against every comparator, at every horizon, with no
bound on the losses known in advance. While the losses observed so far all vanish, the learning
rate is `√(m B / 0) = 0` with Lean's division, and the step for the learning rate `0` is a
Bregman projection of the current play: the algorithm makes no step, as in [Ora].

For projected online subgradient descent with plays at distance at most `D` from the
comparator, as on a set of diameter `D`, the potential `‖·‖ ^ 2 / 2` with `B = D ^ 2 / 2` gives
the rates `η t = D / √(2 ∑ s ≤ t, ‖g s‖ ^ 2)` and the regret bound
`D √(2 ∑ t < n, ‖g t‖ ^ 2)` [Ora, Theorem 4.14]. When the squared norms of the subgradients are
controlled by the losses, `‖g t‖ ^ 2 ≤ 2 s f t (a t)`, as for nonnegative `s`-self-bounded losses
(`LMLExplore.SelfBoundedOn`), the regret is in turn controlled by the cumulative loss of the
comparator `u`: it is at most `4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)` [Ora, Theorem 4.30]. This
**`L⋆` bound** is constant when the comparator has zero cumulative loss.

**AdaGrad** [DHS11], [Ora, Section 4.2.4] adapts one learning rate per coordinate. On a box
`∏ a, [l a, r a]` of `α → ℝ`, it runs in each coordinate `a` the adaptive projected online
subgradient descent on the interval `[l a, r a]`, of diameter `D a = r a - l a`, with the learning
rate `D a / √(2 ∑ s ≤ t, g s a ^ 2)` computed from that coordinate of the subgradients alone. It
is the coordinatewise product (`OnlineLearner.pi`) of the one-dimensional learners
`OnlineLearner.adaGradIcc`, so its linear regret is the sum of the regrets of the coordinates, and
the one-dimensional case of [Ora, Theorem 4.14] gives the regret bound
`√2 ∑ a, D a √(∑ t < n, g t a ^ 2)` [Ora, Theorem 4.32]. Since `|g t a| ≤ ‖g t‖`, this is at most
`√2 (∑ a, D a) √(∑ t < n, ‖g t‖ ^ 2)`, for the sup norm of `α → ℝ`. Since each coordinate divides
its step by the root of the sum of its own squared subgradients, the plays of AdaGrad are unchanged
when each coordinate of every subgradient is multiplied by a positive constant of that coordinate.

## Main definitions

* `LMLExplore.OnlineLearning.OnlineLearner.adaGradIcc l r h x₀`: AdaGrad on the interval `[l, r]`,
  that is, projected online subgradient descent on `[l, r]` with adaptive learning rates.
* `LMLExplore.OnlineLearning.OnlineLearner.adaGrad l r h x₀`: AdaGrad on the box
  `∏ a, [l a, r a]` [Ora, Algorithm 4.1].

## Main statements

* `mirrorDescent_regret_le_two_mul_sqrt`: mirror descent with an `m`-strongly convex potential and
  the adaptive learning rates has regret at most `2 √(B ∑ t < n, ‖y t‖ ^ 2 / m)`.
* `onlineSubgradientDescent_regret_le_mul_sqrt_sum`: [Ora, Theorem 4.14] projected online
  subgradient descent with the adaptive learning rates, with plays at distance at most `D` from the
  comparator, has regret at most `D √(2 ∑ t < n, ‖g t‖ ^ 2)`.
* `onlineSubgradientDescent_regret_le_of_norm_sq_le`: [Ora, Theorem 4.30] the `L⋆` bound
  `4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)` for losses with `‖g t‖ ^ 2 ≤ 2 s f t (a t)`.
* `onlineSubgradientDescent_regret_le_of_selfBoundedOn`: its form for nonnegative `s`-self-bounded
  losses.
* `OnlineLearner.hasRegretBound_adaGradIcc`: AdaGrad on an interval `[l, r]` has regret at most
  `(r - l) √(2 ∑ t < n, g t ^ 2)` for linear losses.
* `OnlineLearner.hasRegretBound_adaGrad`, `OnlineLearner.regret_run_adaGrad_le`:
  [Ora, Theorem 4.32] AdaGrad on a box has regret at most `√2 ∑ a, D a √(∑ t < n, g t a ^ 2)`,
  for linear and for convex losses.
* `OnlineLearner.run_adaGrad_mul`: AdaGrad is coordinatewise scale-free (see
  [Ora, Definition 4.33]).

## References

* [DHS11] J. Duchi, E. Hazan and Y. Singer, *Adaptive subgradient methods for online learning and
  stochastic optimization*, JMLR 12, 2011.
* [Ora] F. Orabona, *Online learning: a modern introduction using convex optimization*,
  arXiv:1912.13213v10, 2026.
-/

public section

open Finset
open scoped NNReal

namespace LMLExplore.OnlineLearning

variable {n : ℕ}

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {F : E → ℝ} {u : E}

/-- The two terms of the regret bound balance at the adaptive learning rates: if `r ^ 2 = m B`,
then `B √A / r + r √A / m = 2 √(B A / m)`. -/
private lemma mul_sqrt_div_add_mul_sqrt_div_eq {r m B A : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hr_sq : r ^ 2 = m * B) (hA : 0 ≤ A) :
    B * √A / r + r * √A / m = 2 * √(B * A / m) := by
  have h_B : B * √A / r = r * √A / m := by
    rw [div_eq_div_iff hr.ne' hm.ne']
    linear_combination (-√A) * hr_sq
  have h_sqrt : √(B * A / m) = r * √A / m := by
    rw [show B * A / m = (r * √A / m) ^ 2 by
      rw [div_pow, mul_pow, hr_sq, Real.sq_sqrt hA]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  rw [h_B, h_sqrt]
  ring

/-- The case of `mirrorDescent_regret_le_two_mul_sqrt` with `B > 0` and a first round `t₀ < n`
with a nonzero loss. From `t₀` on, the adaptive learning rates are positive and nonincreasing;
before `t₀` the losses vanish, so that the steps are also steps for the learning rate of `t₀`,
and the bound of mirror descent with nonincreasing learning rates applies. -/
private theorem mirrorDescent_regret_le_two_mul_sqrt_of_ne_zero {m B : ℝ}
    (hF : StrongConvexOn K m F) (hm : 0 < m) (hB : 0 < B) (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E)
    (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K) {t₀ : ℕ} (ht₀n : t₀ < n) (hyt₀ : y t₀ ≠ 0)
    (hy_lt : ∀ t < t₀, y t = 0)
    (ha : ∀ t < n, IsMirrorDescentStep K F (√(m * B / ∑ s ∈ range (t + 1), ‖y s‖ ^ 2)) (y t)
      (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t))
    (hBu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ B) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ 2 * √(B * (∑ t ∈ range n, ‖y t‖ ^ 2) / m) := by
  set S : ℕ → ℝ := fun t ↦ ∑ s ∈ range (t + 1), ‖y s‖ ^ 2 with hS_def
  set A := ∑ t ∈ range n, ‖y t‖ ^ 2 with hA_def
  have hS_mono : Monotone S := fun s t hst ↦
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega)) fun _ _ _ ↦ sq_nonneg _
  have hS_pos (t : ℕ) (ht : t₀ ≤ t) : 0 < S t :=
    calc 0 < ‖y t₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hyt₀) 2
      _ ≤ S t := single_le_sum (f := fun s ↦ ‖y s‖ ^ 2) (fun _ _ ↦ sq_nonneg _)
        (mem_range.mpr (by omega))
  -- the learning rate of round `t` is `r / √(S t)`, with `r = √(m B)`
  set r := √(m * B) with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr (mul_pos hm hB)
  have hr_sq : r ^ 2 = m * B := Real.sq_sqrt (mul_pos hm hB).le
  have h_rate (t : ℕ) : √(m * B / S t) = r / √(S t) := Real.sqrt_div' _ (by positivity)
  -- the learning rates frozen at round `t₀` before it are positive and nonincreasing
  set η : ℕ → ℝ := fun t ↦ r / √(S (max t t₀)) with hη_def
  have hη (t : ℕ) : 0 < η t := div_pos hr (Real.sqrt_pos.mpr (hS_pos _ (le_max_right _ _)))
  have hη_anti : Antitone η := fun s t hst ↦
    div_le_div_of_nonneg_left hr.le (Real.sqrt_pos.mpr (hS_pos _ (le_max_right _ _)))
      (Real.sqrt_le_sqrt (hS_mono (max_le_max hst le_rfl)))
  have ha' (t : ℕ) (ht : t < n) :
      IsMirrorDescentStep K F (η t) (y t) (a t) (F' t) (a (t + 1)) := by
    have h_step := ha t ht
    rcases lt_or_ge t t₀ with htt | htt
    · rw [hy_lt t htt] at h_step ⊢
      exact isMirrorDescentStep_zero_iff.mpr (isMirrorDescentStep_zero_iff.mp h_step)
    · simp only [hη_def, max_eq_left htt, ← h_rate]
      exact h_step
  have h := mirrorDescent_regret_le_of_strongConvexOn_of_antitone hF hm hη hη_anti y a F' ha0K ha'
    hF' hB.le hBu hu
  -- the first term is `B √A / r`, and the stability terms add up to at most `r √A / m`
  have h_first : B / η (n - 1) = B * √A / r := by
    have hn : 0 < n := (Nat.zero_le t₀).trans_lt ht₀n
    have hSn : S (n - 1) = A := by simp only [hS_def, hA_def, Nat.sub_add_cancel hn]
    simp only [hη_def, max_eq_left (Nat.le_sub_one_of_lt ht₀n), hSn, div_div_eq_mul_div]
  have h_term (t : ℕ) (ht : t ∈ range n) :
      η t / (2 * m) * ‖y t‖ ^ 2 = r / (2 * m) * (‖y t‖ ^ 2 / √(S t)) := by
    rcases lt_or_ge t t₀ with htt | htt
    · simp [hy_lt t htt]
    · simp only [hη_def, max_eq_left htt]
      ring
  have h_stab : ∑ t ∈ range n, η t / (2 * m) * ‖y t‖ ^ 2 ≤ r * √A / m := by
    rw [sum_congr rfl h_term, ← mul_sum]
    calc r / (2 * m) * ∑ t ∈ range n, ‖y t‖ ^ 2 / √(S t) ≤ r / (2 * m) * (2 * √A) :=
          mul_le_mul_of_nonneg_left (Real.sum_div_sqrt_le_two_mul_sqrt fun _ _ ↦ sq_nonneg _)
            (by positivity)
      _ = r * √A / m := by field_simp
  linarith [mul_sqrt_div_add_mul_sqrt_div_eq hr hm hr_sq (sum_nonneg fun _ _ ↦ sq_nonneg _ : 0 ≤ A)]

/-- **Mirror descent with adaptive learning rates**, the form of [Ora, Theorem 4.14] for mirror
descent with a strongly convex potential. Let `F` be `m`-strongly
convex on `K`, with `m > 0`. Let `a 0 ∈ K` and let each `a (t + 1)`, for `t < n`, be a mirror
descent step on `K` from `a t` with derivative `F' t`, for the loss `y t` and the learning rate
`η t = √(m B / ∑ s ≤ t, ‖y s‖ ^ 2)`, where `F` has derivative `F' t` within `K` at `a t` for
`t ≤ n`. If `B` bounds the Bregman divergences `D_F(u, a t)` for `t < n`, then for every `u ∈ K`,
`∑ t < n, y t (a t - u) ≤ 2 √(B ∑ t < n, ‖y t‖ ^ 2 / m)`,
where `‖y t‖` is the dual norm. While the losses observed so far vanish, the learning rate is `0`
and the step is a Bregman projection of `a t`, so that the algorithm stays at `a t`. -/
theorem mirrorDescent_regret_le_two_mul_sqrt {m B : ℝ} (hF : StrongConvexOn K m F) (hm : 0 < m)
    (y : ℕ → E →L[ℝ] ℝ) (a : ℕ → E) (F' : ℕ → E →L[ℝ] ℝ) (ha0K : a 0 ∈ K)
    (ha : ∀ t < n, IsMirrorDescentStep K F (√(m * B / ∑ s ∈ range (t + 1), ‖y s‖ ^ 2)) (y t)
      (a t) (F' t) (a (t + 1)))
    (hF' : ∀ t ≤ n, HasFDerivWithinAt F (F' t) K (a t))
    (hBu : ∀ t < n, bregDiv F u (a t) (F' t) ≤ B) (hu : u ∈ K) :
    ∑ t ∈ range n, y t (a t - u) ≤ 2 * √(B * (∑ t ∈ range n, ‖y t‖ ^ 2) / m) := by
  have h_mem := mem_of_isMirrorDescentStep ha0K ha
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  -- `B ≥ 0`, as the Bregman divergences of a convex function are nonnegative
  have hB : 0 ≤ B := ((hF' 0 hn.le).hasSubgradientWithinAt
    (strongConvexOn_zero.mp (hF.mono hm.le)) ha0K u hu).trans (hBu 0 hn)
  -- if every loss vanishes, so does the regret
  by_cases hy : ∀ t < n, y t = 0
  · rw [sum_eq_zero fun t ht ↦ by simp [hy t (mem_range.mp ht)]]
    positivity
  push Not at hy
  rcases hB.eq_or_lt with hB0 | hB0
  · -- if `B = 0`, every play is the comparator, by strong convexity
    refine (sum_eq_zero fun t ht ↦ ?_).le.trans (by positivity)
    have ht := mem_range.mp ht
    have h_lower := hF.mul_norm_sub_sq_le_bregDiv (h_mem t ht.le) hu (hF' t ht.le)
    have h_sq : ‖u - a t‖ ^ 2 = 0 := by nlinarith [hBu t ht, sq_nonneg ‖u - a t‖]
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h_sq
    simp [h_sq]
  -- otherwise, let `t₀` be the first round with a nonzero loss
  classical
  refine mirrorDescent_regret_le_two_mul_sqrt_of_ne_zero hF hm hB0 y a F' ha0K
    (Nat.find_spec hy).1 (Nat.find_spec hy).2 (fun t ht ↦ ?_) ha hF' hBu hu
  by_contra h
  exact Nat.find_min hy ht ⟨ht.trans (Nat.find_spec hy).1, h⟩

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {u : E}

/-- **Projected online subgradient descent with adaptive learning rates** [Ora, Theorem 4.14].
Let `K` be convex, and let `g t` be a subgradient of the loss `f t` within `K` at `a t`, for
`t < n`. Let `a 0 ∈ K` and let each `a (t + 1)` be a point of `K` nearest to `a t - η t • g t`, for
the learning rate `η t = D / √(2 ∑ s ≤ t, ‖g s‖ ^ 2)`. If `‖u - a t‖ ≤ D` for `t < n`, for
instance if `u ∈ K` and `K` has diameter at most `D`, then
`regret f a u n ≤ D √(2 ∑ t < n, ‖g t‖ ^ 2)`.
The learning rates need neither the horizon nor a bound on the subgradients. While the
subgradients observed so far vanish, the learning rate is `0` and the algorithm stays at `a t`. -/
theorem onlineSubgradientDescent_regret_le_mul_sqrt_sum (hK : Convex ℝ K) {D : ℝ}
    (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t)) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn
      (fun b ↦ ‖b - (a t - (D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2)) • g t)‖) K (a (t + 1)))
    (hD : ∀ t < n, ‖u - a t‖ ≤ D) (hu : u ∈ K) :
    regret f a u n ≤ D * √(2 * ∑ t ∈ range n, ‖g t‖ ^ 2) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [regret_def]
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 hn)
  -- the learning rates are those of `mirrorDescent_regret_le_two_mul_sqrt` for the potential
  -- `‖·‖ ^ 2 / 2`, with `m = 1` and `B = D ^ 2 / 2`
  have h_rate (S : ℝ) (hS : 0 ≤ S) : √(1 * (D ^ 2 / 2) / S) = D / √(2 * S) := by
    rw [show 1 * (D ^ 2 / 2) / S = D ^ 2 / (2 * S) by ring, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hD0]
  have ha' (t : ℕ) (ht : t < n) : IsMirrorDescentStep K (fun b : E ↦ ‖b‖ ^ 2 / 2)
      (√(1 * (D ^ 2 / 2) / ∑ s ∈ range (t + 1), ‖innerSL ℝ (g s)‖ ^ 2)) (innerSL ℝ (g t)) (a t)
      (innerSL ℝ (a t)) (a (t + 1)) := by
    simp only [innerSL_apply_norm]
    rw [h_rate _ (sum_nonneg fun _ _ ↦ sq_nonneg _)]
    exact isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  have hBu (t : ℕ) (ht : t < n) :
      bregDiv (fun b : E ↦ ‖b‖ ^ 2 / 2) u (a t) (innerSL ℝ (a t)) ≤ D ^ 2 / 2 := by
    rw [bregDiv_norm_sq_div_two]
    gcongr
    exact hD t ht
  have h := mirrorDescent_regret_le_two_mul_sqrt (strongConvexOn_norm_sq_div_two hK) one_pos
    (fun t ↦ innerSL ℝ (g t)) a (fun t ↦ innerSL ℝ (a t)) ha0 ha'
    (fun t _ ↦ (hasFDerivAt_norm_sq_div_two _).hasFDerivWithinAt) hBu hu
  simp only [innerSL_apply_norm] at h
  rw [regret_def]
  refine (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f _ a hg hu).trans (h.trans_eq ?_)
  rw [div_one, show D ^ 2 / 2 * ∑ t ∈ range n, ‖g t‖ ^ 2 =
    (D / 2) ^ 2 * (2 * ∑ t ∈ range n, ‖g t‖ ^ 2) by ring, Real.sqrt_sq_mul,
    abs_of_nonneg (by positivity)]
  ring

/-- **The `L⋆` bound of projected online subgradient descent** [Ora, Theorem 4.30]. Under the
assumptions of `onlineSubgradientDescent_regret_le_mul_sqrt_sum`, if moreover the subgradients
satisfy `‖g t‖ ^ 2 ≤ 2 s f t (a t)` for `t < n`, then
`regret f a u n ≤ 4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)`.
The bound depends on the cumulative loss of the comparator, and not on the number of rounds. -/
theorem onlineSubgradientDescent_regret_le_of_norm_sq_le (hK : Convex ℝ K) {D : ℝ} {s : ℝ≥0}
    (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t))
    (hgf : ∀ t < n, ‖g t‖ ^ 2 ≤ 2 * s * f t (a t)) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn
      (fun b ↦ ‖b - (a t - (D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2)) • g t)‖) K (a (t + 1)))
    (hD : ∀ t < n, ‖u - a t‖ ≤ D) (hu : u ∈ K) :
    regret f a u n ≤ 4 * s * D ^ 2 + 2 * D * √(s * ∑ t ∈ range n, f t u) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [regret_def, range_zero, sum_empty, mul_zero, Real.sqrt_zero, add_zero]
    positivity
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 hn)
  set L := ∑ t ∈ range n, f t (a t)
  set U := ∑ t ∈ range n, f t u
  have h_reg : regret f a u n = L - U := by rw [regret_def, sum_sub_distrib]
  have h := onlineSubgradientDescent_regret_le_mul_sqrt_sum hK f g a hg ha0 ha hD hu
  -- the squared subgradients add up to at most `2 s L`, so that `L - U ≤ √(4 s D ^ 2 L)`
  have h_sum : 2 * ∑ t ∈ range n, ‖g t‖ ^ 2 ≤ 4 * s * L := by
    have := sum_le_sum fun t ht ↦ hgf t (mem_range.mp ht)
    rw [← mul_sum] at this
    linarith
  have h_imp : L - √(4 * s * D ^ 2 * L + 0) ≤ U := by
    have h_le : D * √(2 * ∑ t ∈ range n, ‖g t‖ ^ 2) ≤ √(4 * s * D ^ 2 * L + 0) := by
      rw [add_zero, show 4 * s * D ^ 2 * L = D ^ 2 * (4 * s * L) by ring,
        Real.sqrt_sq_mul, abs_of_nonneg hD0]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h_sum) hD0
    linarith
  -- solving for `L` gives `L ≤ 4 s D ^ 2 + U + √(4 s D ^ 2 U)`
  have h_sol := Real.le_add_add_sqrt_of_sub_sqrt_le (by positivity) h_imp
  rw [zero_add, show 4 * s * D ^ 2 * U = (2 * D) ^ 2 * (s * U) by ring,
    Real.sqrt_sq_mul, abs_of_nonneg (by positivity)] at h_sol
  rw [h_reg]
  linarith

/-- **The `L⋆` bound for self-bounded losses** [Ora, Theorem 4.30]. Let `K` be convex, and let the
losses `f t` be nonnegative and `s`-self-bounded within `K`, with a subgradient `g t` within `K`
at `a t`, for `t < n`. Let `a 0 ∈ K` and let each `a (t + 1)` be a point of `K` nearest to
`a t - η t • g t`, for the learning rate `η t = D / √(2 ∑ s ≤ t, ‖g s‖ ^ 2)`. If `u ∈ K` and
`‖u - a t‖ ≤ D` for `t < n`, as on a set of diameter at most `D`, then
`regret f a u n ≤ 4 s D ^ 2 + 2 D √(s ∑ t < n, f t u)`. -/
theorem onlineSubgradientDescent_regret_le_of_selfBoundedOn (hK : Convex ℝ K) {D : ℝ}
    {s : ℝ≥0} (f : ℕ → E → ℝ) (g a : ℕ → E)
    (hf : ∀ t < n, SelfBoundedOn K s (f t)) (hf0 : ∀ t < n, ∀ x ∈ K, 0 ≤ f t x)
    (hg : ∀ t < n, HasSubgradientWithinAt (f t) (innerSL ℝ (g t)) K (a t)) (ha0 : a 0 ∈ K)
    (ha : ∀ t < n, a (t + 1) ∈ K ∧ IsMinOn
      (fun b ↦ ‖b - (a t - (D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2)) • g t)‖) K (a (t + 1)))
    (hD : ∀ t < n, ‖u - a t‖ ≤ D) (hu : u ∈ K) :
    regret f a u n ≤ 4 * s * D ^ 2 + 2 * D * √(s * ∑ t ∈ range n, f t u) := by
  have h_mem := mem_of_isMirrorDescentStep (η := fun t ↦ D / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2))
    ha0 fun t ht ↦ isMirrorDescentStep_norm_sq_div_two_iff.mpr (ha t ht)
  refine onlineSubgradientDescent_regret_le_of_norm_sq_le hK f g a hg (fun t ht ↦ ?_) ha0 ha hD hu
  have := (hf t ht).norm_sq_le_of_nonneg (hf0 t ht) (h_mem t ht.le) (hg t ht)
  rwa [innerSL_apply_norm] at this

end InnerProductSpace

section AdaGrad

open Set

/-- The play of round `t` of `OnlineLearner.adaGradIcc l r h x₀` from the feedback `g` of the
rounds `s < t`, by recursion on `t`. -/
private noncomputable def adaGradIccPlay (l r : ℝ) (h : l ≤ r) (x₀ : ℝ) :
    (t : ℕ) → (Fin t → ℝ) → ℝ
  | 0, _ => projIcc l r h x₀
  | t + 1, g => projIcc l r h (adaGradIccPlay l r h x₀ t (fun s ↦ g s.castSucc) -
      (r - l) / √(2 * ∑ s, g s ^ 2) * g (Fin.last t))

namespace OnlineLearner

variable {C : Type*}

section Interval

variable {l r : ℝ} {h : l ≤ r} {x₀ : ℝ}

/-- **AdaGrad on an interval** `[l, r]`: projected online subgradient descent on `[l, r]` with the
adaptive learning rates of [Ora, Theorem 4.14], for the diameter `r - l`. Its feedback at round
`t` is the derivative `g t` of a linear loss `x ↦ g t * x`, or a subgradient of a convex loss at
the play. It plays first the projection of `x₀` onto `[l, r]`, then
`x (t + 1) = projIcc l r h (x t - (r - l) / √(2 ∑ s ≤ t, g s ^ 2) * g t)`
(`run_adaGradIcc_succ`). While the feedback observed so far vanishes, the learning rate is `0`
with Lean's division, and the learner stays at its play. It ignores the contexts. -/
noncomputable def adaGradIcc (l r : ℝ) (h : l ≤ r) (x₀ : ℝ) : OnlineLearner C ℝ ℝ where
  play t hist _ := adaGradIccPlay l r h x₀ t fun s ↦ (hist s).2

/-- The first play of AdaGrad on `[l, r]` is the projection of `x₀` onto `[l, r]`. -/
@[simp]
lemma run_adaGradIcc_zero (c : ℕ → C) (g : ℕ → ℝ) :
    (adaGradIcc l r h x₀).run c g 0 = projIcc l r h x₀ := by
  simp only [run_def, adaGradIcc, adaGradIccPlay]

/-- The update of AdaGrad on `[l, r]`: the projection onto `[l, r]` of the subgradient step from
the current play, with the learning rate `(r - l) / √(2 ∑ s ≤ t, g s ^ 2)`. -/
lemma run_adaGradIcc_succ (c : ℕ → C) (g : ℕ → ℝ) (t : ℕ) :
    (adaGradIcc l r h x₀).run c g (t + 1) = projIcc l r h ((adaGradIcc l r h x₀).run c g t -
      (r - l) / √(2 * ∑ s ∈ range (t + 1), g s ^ 2) * g t) := by
  rw [run_def, run_def]
  simp only [adaGradIcc, adaGradIccPlay, Fin.val_castSucc, Fin.val_last,
    Fin.sum_univ_eq_sum_range (fun s ↦ g s ^ 2)]

/-- The plays of AdaGrad on `[l, r]` lie in `[l, r]`. -/
lemma run_adaGradIcc_mem (c : ℕ → C) (g : ℕ → ℝ) (t : ℕ) :
    (adaGradIcc l r h x₀).run c g t ∈ Icc l r := by
  rcases t with _ | t
  · rw [run_adaGradIcc_zero]
    exact Subtype.mem _
  · rw [run_adaGradIcc_succ]
    exact Subtype.mem _

/-- **AdaGrad on an interval is scale-free**: its plays are unchanged when every feedback is
multiplied by the same positive constant. -/
theorem run_adaGradIcc_const_mul {k : ℝ} (hk : 0 < k) (c : ℕ → C) (g : ℕ → ℝ) :
    (adaGradIcc l r h x₀).run c (fun t ↦ k * g t) = (adaGradIcc l r h x₀).run c g := by
  funext t
  induction t with
  | zero => rw [run_adaGradIcc_zero, run_adaGradIcc_zero]
  | succ t ih =>
    rw [run_adaGradIcc_succ, run_adaGradIcc_succ, ih]
    -- the learning rate is divided by `k`, and the feedback multiplied by `k`
    have h_sum : 2 * ∑ s ∈ range (t + 1), (k * g s) ^ 2 =
        k ^ 2 * (2 * ∑ s ∈ range (t + 1), g s ^ 2) := by
      simp only [mul_pow, ← mul_sum]
      ring
    rw [h_sum, Real.sqrt_sq_mul, abs_of_pos hk]
    rcases eq_or_ne (√(2 * ∑ s ∈ range (t + 1), g s ^ 2)) 0 with h0 | h0
    · simp [h0]
    · congr 3
      field_simp

/-- **Regret guarantee of AdaGrad on an interval** [Ora, Theorem 4.14]. For linear losses
`x ↦ g t * x` on `ℝ`, the regret of AdaGrad on `[l, r]` after `n` rounds against every `u ∈ [l, r]`
is at most `(r - l) √(2 ∑ t < n, g t ^ 2)`. The learning rates need neither the horizon nor a bound
on the feedback. -/
theorem hasRegretBound_adaGradIcc :
    (adaGradIcc (C := C) l r h x₀).HasRegretBound (fun g x ↦ g * x) (fun _ _ ↦ True) (Icc l r)
      (fun n _ g _ ↦ (r - l) * √(2 * ∑ t ∈ range n, g t ^ 2)) := by
  refine hasRegretBound_iff.mpr fun c g n _ u hu ↦ ?_
  have h_mem := run_adaGradIcc_mem (l := l) (r := r) (h := h) (x₀ := x₀) c g
  -- the step is a projected subgradient step on `[l, r]` for the losses `⟪g t, ·⟫ = g t * ·`
  have h_step (t : ℕ) (_ : t < n) : (adaGradIcc l r h x₀).run c g (t + 1) ∈ Icc l r ∧
      IsMinOn (fun b ↦ ‖b - ((adaGradIcc l r h x₀).run c g t -
        ((r - l) / √(2 * ∑ s ∈ range (t + 1), ‖g s‖ ^ 2)) • g t)‖) (Icc l r)
        ((adaGradIcc l r h x₀).run c g (t + 1)) := by
    simp only [Real.norm_eq_abs, sq_abs, smul_eq_mul]
    rw [run_adaGradIcc_succ]
    exact ⟨Subtype.mem _, isMinOn_abs_sub_projIcc h _⟩
  have h_dist (t : ℕ) (_ : t < n) : ‖u - (adaGradIcc l r h x₀).run c g t‖ ≤ r - l := by
    rw [Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [hu.1, hu.2, (h_mem t).1, (h_mem t).2]
  have h_bound := onlineSubgradientDescent_regret_le_mul_sqrt_sum (convex_Icc l r)
    (fun t ↦ innerSL ℝ (g t)) g _ (fun t _ ↦ hasSubgradientWithinAt_linear _) (h_mem 0) h_step
    h_dist hu
  simp only [Real.norm_eq_abs, sq_abs] at h_bound
  convert h_bound using 1
  simp only [regret_def, innerSL_apply_apply, Real.inner_apply]

end Interval

section Box

variable {α : Type*} {l r : α → ℝ} {h : l ≤ r} {x₀ : α → ℝ}

/-- **AdaGrad** on the box `∏ a, [l a, r a]` of `α → ℝ` [Ora, Algorithm 4.1]: the coordinatewise
product (`OnlineLearner.pi`) of the learners AdaGrad on the intervals `[l a, r a]`. Its feedback at
round `t` is a vector `g t : α → ℝ`, the gradient of a linear loss `x ↦ ∑ a, g t a * x a` or a
subgradient of a convex loss at the play. Each coordinate `a` runs projected online subgradient
descent on `[l a, r a]` with its own adaptive learning rate
`(r a - l a) / √(2 ∑ s ≤ t, g s a ^ 2)` (`run_adaGrad_succ`), from the projection of `x₀` onto the
box. It ignores the contexts. -/
noncomputable def adaGrad (l r : α → ℝ) (h : l ≤ r) (x₀ : α → ℝ) :
    OnlineLearner C (α → ℝ) (α → ℝ) :=
  pi (G := fun _ ↦ ℝ) (X := fun _ ↦ ℝ) fun a ↦ adaGradIcc (l a) (r a) (h a) (x₀ a)

/-- The coordinates of the plays of AdaGrad are the plays of AdaGrad on the intervals
`[l a, r a]` against the coordinates of the feedback. -/
lemma run_adaGrad (c : ℕ → C) (g : ℕ → α → ℝ) (t : ℕ) (a : α) :
    (adaGrad l r h x₀).run c g t a = (adaGradIcc (l a) (r a) (h a) (x₀ a)).run c (g · a) t :=
  run_pi (G := fun _ ↦ ℝ) (X := fun _ ↦ ℝ) _ c g t a

/-- The first play of AdaGrad is the projection of `x₀` onto the box. -/
@[simp]
lemma run_adaGrad_zero (c : ℕ → C) (g : ℕ → α → ℝ) (a : α) :
    (adaGrad l r h x₀).run c g 0 a = projIcc (l a) (r a) (h a) (x₀ a) := by
  rw [run_adaGrad, run_adaGradIcc_zero]

/-- The update of AdaGrad [Ora, Algorithm 4.1]: each coordinate takes a projected subgradient step
on `[l a, r a]`, with the learning rate `(r a - l a) / √(2 ∑ s ≤ t, g s a ^ 2)` of that
coordinate. -/
lemma run_adaGrad_succ (c : ℕ → C) (g : ℕ → α → ℝ) (t : ℕ) (a : α) :
    (adaGrad l r h x₀).run c g (t + 1) a = projIcc (l a) (r a) (h a)
      ((adaGrad l r h x₀).run c g t a -
        (r a - l a) / √(2 * ∑ s ∈ range (t + 1), g s a ^ 2) * g t a) := by
  rw [run_adaGrad, run_adaGrad, run_adaGradIcc_succ]

/-- The plays of AdaGrad lie in the box `∏ a, [l a, r a]`. -/
lemma run_adaGrad_mem (c : ℕ → C) (g : ℕ → α → ℝ) (t : ℕ) :
    (adaGrad l r h x₀).run c g t ∈ univ.pi fun a ↦ Icc (l a) (r a) := fun a _ ↦ by
  rw [run_adaGrad]
  exact run_adaGradIcc_mem c _ t

/-- **AdaGrad is coordinatewise scale-free** (see [Ora, Definition 4.33]): its plays are unchanged
when each coordinate of every feedback is multiplied by a positive constant of that coordinate. -/
theorem run_adaGrad_mul {k : α → ℝ} (hk : ∀ a, 0 < k a) (c : ℕ → C) (g : ℕ → α → ℝ) :
    (adaGrad l r h x₀).run c (fun t ↦ k * g t) = (adaGrad l r h x₀).run c g := by
  funext t a
  rw [run_adaGrad, run_adaGrad]
  exact congrFun (run_adaGradIcc_const_mul (hk a) c fun s ↦ g s a) t

variable [Fintype α]

/-- **Regret guarantee of AdaGrad** [Ora, Theorem 4.32]. For linear losses
`x ↦ ∑ a, g t a * x a` on `α → ℝ`, the regret of AdaGrad after `n` rounds against every `u` in the
box `∏ a, [l a, r a]` is at most `√2 ∑ a, (r a - l a) √(∑ t < n, g t a ^ 2)`: the sum over the
coordinates of the regret bounds of AdaGrad on the intervals. -/
theorem hasRegretBound_adaGrad :
    (adaGrad (C := C) l r h x₀).HasRegretBound (fun g x ↦ ∑ a, g a * x a) (fun _ _ ↦ True)
      (univ.pi fun a ↦ Icc (l a) (r a))
      (fun n _ g _ ↦ √2 * ∑ a, (r a - l a) * √(∑ t ∈ range n, g t a ^ 2)) := by
  refine (HasRegretBound.pi (G := fun _ ↦ ℝ) (X := fun _ ↦ ℝ)
    fun a ↦ hasRegretBound_adaGradIcc).mono (fun _ _ _ _ ↦ trivial) subset_rfl
    fun n c g u _ _ ↦ le_of_eq ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [Real.sqrt_mul zero_le_two]
  ring

/-- **AdaGrad on convex losses** [Ora, Theorem 4.32]. Let `g t` be a subgradient of the loss `f t`
within the box `∏ a, [l a, r a]` at the play of round `t` of AdaGrad, for `t < n`: the linear map
`x ↦ ∑ a, g t a * x a`. Then for every `u` in the box, the regret of AdaGrad after `n` rounds is at
most `√2 ∑ a, (r a - l a) √(∑ t < n, g t a ^ 2)`. The feedback `g` may be chosen adaptively, as for
the closed-loop runs (`OnlineLearner.closedLoopFeedback`). -/
theorem regret_run_adaGrad_le (f : ℕ → (α → ℝ) → ℝ) (c : ℕ → C) (g : ℕ → α → ℝ) {n : ℕ}
    (hg : ∀ t < n, HasSubgradientWithinAt (f t)
      (∑ a, g t a • ContinuousLinearMap.proj a : (α → ℝ) →L[ℝ] ℝ)
      (univ.pi fun a ↦ Icc (l a) (r a)) ((adaGrad l r h x₀).run c g t))
    {u : α → ℝ} (hu : u ∈ univ.pi fun a ↦ Icc (l a) (r a)) :
    regret f ((adaGrad l r h x₀).run c g) u n ≤
      √2 * ∑ a, (r a - l a) * √(∑ t ∈ range n, g t a ^ 2) := by
  rw [regret_def]
  refine (sum_sub_le_sum_apply_sub_of_hasSubgradientWithinAt f _ _ hg hu).trans ?_
  refine le_of_eq_of_le ?_ ((hasRegretBound_adaGrad (h := h) (x₀ := x₀)).regret_le (c := c)
    (g := g) (fun _ _ ↦ trivial) hu)
  simp [regret_def, mul_sub, sum_sub_distrib]

end Box

end OnlineLearner

end AdaGrad

end LMLExplore.OnlineLearning
